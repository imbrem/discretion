import Mathlib.Algebra.Group.Defs
import Mathlib.Data.Set.Image
import Mathlib.Data.Set.Lattice
import Mathlib.Algebra.PUnitInstances.Module
import Mathlib.Data.Set.Functor

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

section MulOneClass

variable [MulOneClass ε]

@[simp]
theorem append_one {x: Trace ε τ α}: x.append 1 = x := by cases x <;> simp

end MulOneClass

section Monoid

open Functor

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

end Monoid

end Trace

def TraceT (ε: Type ue) (τ: Type ut) (m: Type (max ue ut u) → Type v) (α: Type u)
  : Type v := m (Trace ε τ α)

namespace TraceT

variable {ε τ m α}

theorem id_monad : TraceT ε τ id α = Trace ε τ α := rfl

section Basic

variable [Mul ε] [SMul ε τ] [Monad m]

end Basic

end TraceT

def Traces (ε: Type ue) (τ: Type ut) := TraceT ε τ SetM
