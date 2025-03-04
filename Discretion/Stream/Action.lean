import Mathlib.Data.Stream.Defs
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Action.Prod
import Mathlib.Algebra.Group.Action.Pi
import Mathlib.Tactic.Convert
import Mathlib.Algebra.Module.PUnit

class StreamProd (α: Type u) (β: Type v) where
  streamProd: (Stream' α) -> β

def StreamProd.infZero {α: Type u} {β: Type v} [Zero α] [StreamProd α β] : β
  := streamProd (λ_ => (0 : α))

def StreamProd.infOne {α: Type u} {β: Type v} [One α] [StreamProd α β] : β
  := streamProd (λ_ => (1 : α))

class StreamMulAction (α: Type u) (β: Type v) [SMul α β]
  : Type (max u v) extends StreamProd α β where
  streamProd_cons: ∀a f, streamProd (f.cons a) = a • streamProd f

open StreamProd

open StreamMulAction

theorem StreamMulAction.streamProd_step {α: Type u} {β: Type v} [SMul α β] [A : StreamMulAction α β]
  (f: Stream' α) : A.streamProd f = f.head • streamProd f.tail := by
  convert streamProd_cons f.head f.tail
  funext k; cases k <;> rfl

instance PUnit.instStreamMulAction {α: Type u}: StreamMulAction α PUnit where
  streamProd _ := ()
  streamProd_cons _ _ := rfl

instance Prod.instStreamProd {α β γ} [StreamProd α β] [StreamProd α γ]
  : StreamProd α (β × γ) where
  streamProd f := (streamProd f, streamProd f)

instance Prod.instStreamMulAction {α β γ}
  [SMul α β] [StreamMulAction α β] [SMul α γ] [StreamMulAction α γ]
  : StreamMulAction α (β × γ) where
  streamProd_cons a f := by simp [streamProd, streamProd_cons]

instance Pi.instStreamProd {α: Type u} {I: Type v} {g: I -> Type w}
  [∀i, StreamProd α (g i)] : StreamProd α (∀i, g i) where
  streamProd f _ := streamProd f

instance Pi.instStreamMulAction {α: Type u} {I: Type v} {g: I -> Type w} [∀i, SMul α (g i)]
  [∀i, StreamMulAction α (g i)] : StreamMulAction α (∀i, g i) where
  streamProd_cons a f := by funext i; simp [streamProd, streamProd_cons]
