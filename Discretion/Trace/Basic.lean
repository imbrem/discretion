import Mathlib.Algebra.Group.Defs
import Mathlib.Data.Set.Image
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Functor
import Mathlib.Control.Functor

import Discretion.Utils.Action
import Discretion.Utils.Kleisli
import Discretion.Nonempty.Set

open Functor

open SMul

inductive Trace (ε: Type u1) (τ: Type u2) (α: Type u3): Type (max u1 u2 u3)
  | done (a: α) (e: ε)
  | inf (t: τ)

namespace Trace

variable {ε τ α}

section Basic

instance Functor : Functor (Trace ε τ) where
  map f
    | done a e => done (f a) e
    | inf t => inf t

@[simp]
theorem map_done {f: α → β} {a: α} {e: ε} : f <$> done (τ := τ) a e = done (f a) e := rfl

@[simp]
theorem map_inf {f: α → β} {t: τ} : f <$> inf (α := α) (ε := ε) t = inf t := rfl

instance LawfulFunctor : LawfulFunctor (Trace ε τ) where
  id_map x := by cases x <;> simp
  comp_map f g x := by cases x <;> simp
  map_const := rfl

variable [Mul ε]

def append (e: ε): Trace ε τ α → Trace ε τ α
  | done a e' => done a (e' * e)
  | inf t => inf t

@[simp]
theorem append_done {e: ε} {a: α} {e': ε}
  : (done (τ := τ) a e').append e = done a (e' * e)
  := rfl

@[simp]
theorem append_inf {e: ε} {t: τ}
  : (inf (α := α) t).append e = inf t
  := rfl

variable [SMul ε τ]

instance instSMul : SMul ε (Trace ε τ α) where
  smul e
  | done a e' => done a (e * e')
  | inf t => inf (e • t)

@[simp]
theorem smul_done {e: ε} {a: α} {e': ε}
  : e • (done (τ := τ) a e') = done a (e * e')
  := rfl

@[simp]
theorem smul_inf {e: ε} {t: τ}
  : e • (inf (α := α) (ε := ε) t) = inf (e • t)
  := rfl

theorem smul_map {e: ε} {x: Trace ε τ α} {f: α → β}
  : e • (f <$> x) = f <$> (e • x) := by cases x <;> simp [mul_smul]

variable [One ε]

instance instMonad : Monad (Trace ε τ) where
  pure a := done a 1
  bind x f := match x with
    | done a e => e • f a
    | inf t => inf t

@[simp]
theorem bind_done {a: α} {e: ε} {f: α → Trace ε τ β}
  : (done a e) >>= f = e • f a
  := rfl

@[simp]
theorem bind_inf {t: τ} {f: α → Trace ε τ β}
  : (inf t) >>= f = inf t
  := rfl

end Basic

section Lawful

@[simp]
theorem append_one [MulOneClass ε] {x: Trace ε τ α}: x.append 1 = x := by cases x <;> simp

variable [Monoid ε] [MulAction ε τ]

open MulAction

instance instMulAction : MulAction ε (Trace ε τ α) where
  one_smul x := by cases x <;> simp
  mul_smul e e' x := by cases x <;> simp [mul_assoc, mul_smul]

theorem smul_pure {e: ε} {a: α} : e • pure a = done (τ := τ) a e := by simp [pure]

theorem smul_bind {e: ε} {x: Trace ε τ α} {f: α → Trace ε τ β}
  : e • (x >>= f) = (e • x) >>= f := by cases x <;> simp [mul_smul]

instance instLawfulMonad : LawfulMonad (Trace ε τ) :=
  LawfulMonad.mk' (m := Trace ε τ)
    (id_map := λx => by cases x <;> simp)
    (pure_bind := λx f => by simp [bind])
    (bind_assoc := λx f g => by cases x <;> simp [smul_bind])
    (bind_pure_comp := λf x => by cases x <;> simp [pure])

end Lawful

end Trace

def TraceT (ε: Type ue) (τ: Type ut) (m: Type (max ue ut u) → Type v) (α: Type u)
  : Type v := m (Trace ε τ α)

namespace TraceT

open Trace

variable {ε τ m α}

theorem id_monad : TraceT ε τ id α = Trace ε τ α := rfl

section Basic

instance instFunctor [Functor m] : Functor (TraceT ε τ m) where
  map f x := map (f := m) (map f) x

theorem map_def [Functor m] {f: α → β} {x: TraceT ε τ m α}
  : f <$> x = map (f := m) (map f) x := rfl

variable [Mul ε] [SMul ε τ]

instance instSMul [Functor m] : SMul ε (TraceT ε τ m α) where
  smul e x := map (f := m) (smul e) x

theorem smul_def [Functor m] {e: ε} {x: TraceT ε τ m α}
  : e • x = map (f := m) (smul e) x := rfl

variable [One ε] [Monad m]

-- TODO: applicative?

instance instMonad : Monad (TraceT ε τ m) where
  pure := λa => pure (f := m) (pure a)
  bind := λx f => Bind.bind (m := m) x (λ | done a e => e • f a | inf t  => pure (inf t))

theorem pure_def {a: α} : pure (f := TraceT ε τ m) a = pure (f := m) (pure a) := rfl

theorem bind_def {x: TraceT ε τ m α} {f: α → TraceT ε τ m β}
  : x >>= f = Bind.bind (m := m) x (λ | done a e => e • f a | inf t => pure (inf t)) := rfl

end Basic

section Lawful

section Functor

variable [Functor m] [LawfulFunctor m]

instance instLawfulFunctor : LawfulFunctor (TraceT ε τ m) where
  id_map x := by simp [map_def, Functor.map_id]
  comp_map f g x := by simp [map_def, <-Functor.map_comp_map]
  map_const := rfl

theorem smul_map [Mul ε] [SMul ε τ] {e: ε} {x: TraceT ε τ m α} {f: α → β}
  : e • (f <$> x) = f <$> (e • x) := by
  simp only [smul_def, map_def, <-comp_map]
  congr; funext x; cases x <;> simp [pure, smul]

instance instMulAction [Monoid ε] [MulAction ε τ] : MulAction ε (TraceT ε τ m α) where
  one_smul x := by simp [smul_def, smul_one]
  mul_smul e e' x := by simp [smul_def, smul_mul, comp_map]

end Functor

variable [Monad m] [LawfulMonad m]

theorem outer_pure_bind {a: α} {f: α → TraceT ε τ m β}
  : pure (f := m) a >>= f = f a := by simp [bind]

variable [Monoid ε] [MulAction ε τ]

theorem smul_pure {e: ε} {a: α} : e • pure (f := TraceT ε τ m) a = pure (done a e) := by
  simp [smul_def, pure_def, pure, smul]

theorem smul_bind {e: ε} {x: TraceT ε τ m α} {f: α → TraceT ε τ m β}
  : e • (x >>= f) = (e • x) >>= f := by
  simp only [smul_def, bind_def, map_eq_pure_bind, bind_assoc]
  congr; funext x; cases x with
  | done a e => simp only [bind_pure_comp, map_map, pure_bind, smul_mul]; rfl
  | inf t => simp [smul]

instance instLawfulMonad : LawfulMonad (TraceT ε τ m) :=
  LawfulMonad.mk' (m := TraceT ε τ m)
    (id_map := λx => by simp)
    (pure_bind := λx f => by simp [pure_def, bind_def])
    (bind_assoc := λx f g => by
      conv =>
        args
        · simp only [bind_def, bind_assoc]
        · rw [bind_def]
      congr; funext x; cases x <;> simp only [pure_bind, smul_bind]
      rfl)
    (bind_pure_comp := λf x => by
      rw [map_def, <-bind_pure_comp, bind_def]
      congr; funext x; cases x <;> simp [smul_pure])

end Lawful

end TraceT

def Traces? (ε: Type ue) (τ: Type ut) := TraceT ε τ Set

namespace Traces?

instance instMembership : Membership (Trace ε τ α) (Traces? ε τ α) := Set.instMembership

instance instSingleton : Singleton (Trace ε τ α) (Traces? ε τ α) := Set.instSingletonSet

instance instHasSubset : HasSubset (Traces? ε τ α) := Set.instHasSubset

instance instUnion : Union (Traces? ε τ α) := Set.instUnion

instance instInter : Inter (Traces? ε τ α) := Set.instInter

instance instEmptyCollection : EmptyCollection (Traces? ε τ α) := Set.instEmptyCollection

instance instInsert : Insert (Trace ε τ α) (Traces? ε τ α) := Set.instInsert

instance instLawfulSingleton : LawfulSingleton (Trace ε τ α) (Traces? ε τ α)
  := Set.instLawfulSingleton

attribute [local instance] Set.monad

instance instFunctor : Functor (Traces? ε τ) := TraceT.instFunctor

instance instMonad [One ε] [Mul ε] [SMul ε τ] : Monad (Traces? ε τ) := TraceT.instMonad

instance instLawfulFunctor : LawfulFunctor (Traces? ε τ) := TraceT.instLawfulFunctor

instance instSMul [Mul ε] [SMul ε τ] : SMul ε (Traces? ε τ α) := TraceT.instSMul

theorem smul_map [Mul ε] [SMul ε τ] {e: ε} {x: Traces? ε τ α} {f: α → β}
  : e • (f <$> x) = f <$> (e • x) := TraceT.smul_map

theorem smul_def [Mul ε] [SMul ε τ] {e: ε} {x: Traces? ε τ α}
  : e • x = map (f := Set) (smul e) x := rfl

theorem smul_empty [Mul ε] [SMul ε τ] {e : ε} : e • (∅ : Traces? ε τ α) = ∅
  := by simp only [smul_def]; exact Set.image_empty _

-- Note: the nonempty traces are a submonad of Traces?

variable [Monoid ε] [MulAction ε τ]

instance instLawfulMonad : LawfulMonad (Traces? ε τ)
  := TraceT.instLawfulMonad

instance instMulAction : MulAction ε (Traces? ε τ α)
  := TraceT.instMulAction

theorem smul_bind {e: ε} {x: Traces? ε τ α} {f: α → Traces? ε τ β}
  : e • (x >>= f) = (e • x) >>= f := TraceT.smul_bind

end Traces?

def Traces (ε: Type ue) (τ: Type ut) := TraceT ε τ NSet

namespace Traces

instance instMembership {ε τ α} : Membership (Trace ε τ α) (Traces ε τ α) where
  mem t ts := NSet.instMembership.mem t ts

instance instSingleton {ε τ α} : Singleton (Trace ε τ α) (Traces ε τ α) := NSet.instSingleton

instance instFunctor : Functor (Traces ε τ) := TraceT.instFunctor

instance instMonad [One ε] [Mul ε] [SMul ε τ] : Monad (Traces ε τ) := TraceT.instMonad

instance instLawfulFunctor : LawfulFunctor (Traces ε τ) := TraceT.instLawfulFunctor

instance instSMul [Mul ε] [SMul ε τ] : SMul ε (Traces ε τ α) := TraceT.instSMul

theorem smul_map [Mul ε] [SMul ε τ] {e: ε} {x: Traces? ε τ α} {f: α → β}
  : e • (f <$> x) = f <$> (e • x) := TraceT.smul_map

instance instCoeTraces? {ε τ α} : Coe (Traces ε τ α) (Traces? ε τ α) where
  coe ts := ts.val

section Lawful

variable [Monoid ε] [MulAction ε τ]

instance instLawfulMonad : LawfulMonad (Traces ε τ)
  := TraceT.instLawfulMonad

instance instMulAction : MulAction ε (Traces ε τ α)
  := TraceT.instMulAction

theorem smul_bind {e: ε} {x: Traces ε τ α} {f: α → Traces ε τ β}
  : e • (x >>= f) = (e • x) >>= f := TraceT.smul_bind

end Lawful

-- TODO: this induces a submonad

theorem coe_inj {ε τ α} {ts ts': Traces ε τ α}
  (h: (ts : Traces? ε τ α) = (ts' : Traces? ε τ α)) : ts = ts' := NSet.ext h

def kcoe {ε τ α β} (ts: α → Traces ε τ β) (a : α) : Traces? ε τ β := ts a

theorem kcoe_inj {ε τ α β} {ts ts': α → Traces ε τ β}
  (h: kcoe ts = kcoe ts') : ts = ts' := funext (λa => coe_inj (congrFun h a))

theorem kcoe_elim {f: α → Traces ε τ γ} {g: β → Traces ε τ γ}
  : kcoe (Sum.elim f g) = Sum.elim (kcoe f) (kcoe g) := funext (λx => by cases x <;> rfl)

variable [One ε] [Mul ε] [SMul ε τ]

theorem coe_bind {ts: Traces ε τ α} {f: α → Traces ε τ β}
  : (bind (m := Traces ε τ) ts f : Traces? ε τ β)
  = bind (m := Traces? ε τ) (ts : Traces? ε τ α) (kcoe f) := by
  simp only [bind, NSet.coe_iUnion, Set.iUnion_coe_set, Set.pure_def, Set.bind_def]
  apply congrArg; funext i; cases i <;> rfl

theorem kcoe_kleisli {f: α → Traces ε τ β} {g: β → Traces ε τ γ}
  : kcoe (f >=> g) = kcoe f >=> kcoe g := funext (λ_ => coe_bind)

theorem kcoe_sumM {f: α → Traces ε τ α'} {g: β → Traces ε τ β'}
  : kcoe (sumM f g) = sumM (kcoe f) (kcoe g) := funext (λx => by cases x <;> rfl)

end Traces

def Trace? (ε: Type ue) (τ: Type ut) := TraceT ε τ Option

namespace Trace?

instance instMembership {ε τ α} : Membership (Trace ε τ α) (Trace? ε τ α) where
  mem ts t := ts = some t

instance instEmptyCollection {ε τ α} : EmptyCollection (Trace? ε τ α) where
  emptyCollection := none

instance instSingleton {ε τ α} : Singleton (Trace ε τ α) (Trace? ε τ α) where
  singleton x := some x

theorem mem_singleton {ε τ α} {x: Trace ε τ α} : x ∈ ({x} : Trace? ε τ α) := rfl

theorem mem_singleton_iff {ε τ α} {x y: Trace ε τ α} : x ∈ ({y} : Trace? ε τ α) ↔ x = y :=
  by constructor <;> intro p <;> cases p <;> rfl

instance instCoeTraces? {ε τ α} : Coe (Trace? ε τ α) (Traces? ε τ α) where
  coe ts := {x | x ∈ ts}

-- TODO: this induces a submonad

@[simp]
theorem coe_empty {ε τ α} : (∅ : Trace? ε τ α) = (∅ : Traces? ε τ α) := by simp [Membership.mem]

@[simp]
theorem coe_singleton {ε τ α} {x: Trace ε τ α} : ({x} : Trace? ε τ α) = ({x} : Traces? ε τ α)
  := Set.ext (λa => by
    simp only [mem_singleton_iff, Set.setOf_eq_eq_singleton, Set.mem_singleton_iff]
    apply Set.mem_singleton_iff
  )

-- theorem coe_inj {ε τ α} {ts ts': Trace? ε τ α}
--   (h: (ts : Traces? ε τ α) = (ts' : Traces? ε τ α)) : ts = ts' := by sorry

def kcoe {ε τ α β} (ts: α → Trace? ε τ β) (a : α) : Traces? ε τ β := ts a

end Trace?
