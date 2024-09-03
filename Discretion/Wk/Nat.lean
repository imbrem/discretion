import Mathlib.Logic.Function.Basic
import Mathlib.Data.Nat.Defs
import Mathlib.Data.Fin.Basic
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Order.Monotone.Basic

import Discretion.Utils

-- TODO: lore: a strictly monotone function ℕ → ℕ is increasing (i.e. ≥ id)
-- (this is StrictMono.id_le)

-- TODO: likewise for `Fin n → Fin n`; `Fin n → Fin m` in general w/ coe

-- TODO: under what conditions is this true for a partial order α instead?
-- 1) it needs to be linear
-- 2) since `WithBot ℤ` violates this, it must be `IsAtomic`
--    NOTE: we should add an `IsAtomic` instance for `ℕ`
--    NOTE: discrete (⊤, ⊥) orders satisfy `IsAtomistic`, I believe...
-- 3) since `Lex (ℕ ⊕ ℤ)` violates this, we need a lack of infinite decreasing chains...
--    question: is a linear order sans infinite decreasing chains always iso to the order on ℕ?

/-!
# Weakenings

Definitions and utilities for weakening de-Bruijn indices (represented as `Nat`)
-/

/-- Step a weakening -/
def Nat.stepWk (ρ : Nat -> Nat) : Nat -> Nat := Nat.succ ∘ ρ

/-- Lift a weakening under a binder -/
def Nat.liftWk (ρ : Nat -> Nat): Nat -> Nat
  | 0 => 0
  | n + 1 => (ρ n) + 1

@[simp]
theorem Nat.liftWk_id : liftWk id = id := by funext n; cases n <;> simp [liftWk]

@[simp]
theorem Nat.liftWk_id' : liftWk (λx => x) = id := Nat.liftWk_id

@[simp]
theorem Nat.liftWk_zero : liftWk ρ 0 = 0 := rfl

@[simp] -- TODO: think about this
theorem Nat.liftWk_eq_zero_iff : liftWk ρ n = 0 ↔ n = 0 := ⟨
  λh => by cases n <;> simp [liftWk] at *,
  λh => by cases h; rfl
⟩

theorem Nat.liftWk_ne_zero_iff : liftWk ρ n ≠ 0 ↔ n ≠ 0 := by simp [liftWk_eq_zero_iff]

@[simp]
theorem Nat.liftWk_succ : liftWk ρ (n + 1) = (ρ n) + 1 := rfl

@[simp]
theorem Nat.stepWk_apply : stepWk ρ n = (ρ n) + 1 := rfl

theorem Nat.liftWk_comp (ρ σ : Nat -> Nat): liftWk (ρ ∘ σ) = liftWk ρ ∘ liftWk σ := by
 funext n; cases n <;> rfl

theorem Nat.liftWk_comp_succ (ρ : Nat -> Nat): liftWk ρ ∘ Nat.succ = Nat.succ ∘ ρ := rfl

theorem Nat.liftWk_comp_succ' (ρ : Nat -> Nat): liftWk ρ ∘ Nat.succ = stepWk ρ := rfl

@[simp]
theorem Nat.liftWk_succ_comp_succ : (Nat.liftWk Nat.succ) ∘ Nat.succ = (· + 2) := rfl

theorem Nat.liftWk_ne_stepWk (ρ σ : Nat -> Nat) : liftWk ρ ≠ stepWk σ :=
  have H: (liftWk ρ 0) ≠ (stepWk σ 0) := by simp [liftWk, stepWk]
  λH' => H (by rw [H'])

theorem Nat.liftWk_injective : Function.Injective liftWk := by
  intro ρ σ H
  funext n
  have H': liftWk ρ (n + 1) = liftWk σ (n + 1) := by rw [H]
  exact Nat.succ_injective H'

theorem Nat.stepWk_injective : Function.Injective stepWk := by
  intro ρ σ H
  funext n
  have H': stepWk ρ n = stepWk σ n := by rw [H]
  exact Nat.succ_injective H'

theorem Nat.liftWk_injective_iff : Function.Injective (liftWk ρ) ↔ Function.Injective ρ := ⟨
  λhρ n m h => (by
    apply Nat.succ_inj.mp
    apply hρ
    simp [h]
  ),
  λhρ n m h => (by
    cases n <;> cases m
    case zero.zero => rfl
    case succ.succ => simp only [liftWk_succ, add_left_inj] at h; rw [hρ h]
    all_goals cases h
  )⟩

theorem Nat.stepWk_injective_iff : Function.Injective (stepWk ρ) ↔ Function.Injective ρ
  := forall₂_congr (by simp)

-- TODO: liftWk and stepWk are (strict) monotone themselves

theorem Nat.liftWk_monotone_iff : Monotone (liftWk ρ) ↔ Monotone ρ := ⟨
  λhρ n m h => (by
    apply Nat.le_of_succ_le_succ
    simp only [Nat.succ_eq_add_one, <-liftWk_succ]
    exact hρ (Nat.succ_le_succ h)
  ),
  λhρ n m h => (by
    cases n <;> cases m
    case succ.succ => exact Nat.succ_le_succ (hρ (Nat.le_of_succ_le_succ h))
    all_goals simp at *
  )⟩

theorem Nat.stepWk_monotone_iff : Monotone (stepWk ρ) ↔ Monotone ρ := by
  apply forall₂_congr
  intro n m
  simp [stepWk, Nat.succ_le_succ_iff]

theorem Nat.liftWk_strictMono_iff : StrictMono (liftWk ρ) ↔ StrictMono ρ := ⟨
  λhρ n m h => (by
    apply Nat.lt_of_succ_lt_succ
    simp only [Nat.succ_eq_add_one, <-liftWk_succ]
    exact hρ (Nat.succ_lt_succ h)
  ),
  λhρ n m h => (by
    cases n <;> cases m
    case succ.succ => exact Nat.succ_lt_succ (hρ (Nat.lt_of_succ_lt_succ h))
    all_goals simp at *
  )⟩

theorem Nat.stepWk_strictMono_iff : StrictMono (stepWk ρ) ↔ StrictMono ρ := by
  apply forall₂_congr
  intro n m
  simp [stepWk, Nat.succ_lt_succ_iff]

-- TODO: monotoneOn iff

-- TODO: strictMonoOn iff

-- TODO: liftWk is a surjection iff, so liftWk is a bijection iff

theorem Nat.liftWk_image_succ_image (ρ) : (liftWk ρ) '' (Nat.succ '' s) = Nat.succ '' (ρ '' s) := by
  ext x
  simp only [Set.mem_image, exists_exists_and_eq_and]
  exact exists_congr (by simp)

theorem Nat.stepWk_image (ρ) : stepWk ρ '' s = Nat.succ '' (ρ '' s) := by
  ext x
  simp only [Set.mem_image, exists_exists_and_eq_and]
  exact exists_congr (by simp)

theorem Nat.pred_stepWk_image (ρ) : Nat.pred '' (stepWk ρ '' s) = ρ '' s := by
  rw [stepWk_image, <-Set.image_comp, Nat.pred_comp_succ, Set.image_id]

theorem Nat.stepWk_image_eq_liftWk_image_succ (ρ) : stepWk ρ '' s = liftWk ρ '' (Nat.succ '' s) := by
  rw [stepWk_image, liftWk_image_succ_image]

theorem Nat.liftWk_eqOn_zero (ρ σ) : ({0} : Set ℕ).EqOn (liftWk ρ) (liftWk σ) := by simp

theorem Nat.liftWk_eqOn_succ_of_eqOn {s : Set ℕ} (hs : s.EqOn ρ σ)
    : (succ '' s).EqOn (liftWk ρ) (liftWk σ) := by
  intro x hx
  have ⟨y, hy, hy'⟩ := hx
  cases x <;> cases hy'
  simp only [liftWk_succ, hs hy]

theorem Nat.eqOn_of_liftWk_eqOn_succ {s : Set ℕ} (hs : (succ '' s).EqOn (liftWk ρ) (liftWk σ))
    : s.EqOn ρ σ := by
  intro x hx
  have hs' := @hs (x + 1) (by simp [hx])
  simp only [liftWk_succ, add_left_inj] at hs'
  exact hs'

theorem Nat.liftWk_eqOn_succ_iff {s : Set ℕ} : (succ '' s).EqOn (liftWk ρ) (liftWk σ) ↔ s.EqOn ρ σ
  := ⟨eqOn_of_liftWk_eqOn_succ, liftWk_eqOn_succ_of_eqOn⟩

theorem Nat.liftWk_eqOn_insert_succ_iff {s : Set ℕ}
  : (insert 0 (succ '' s)).EqOn (liftWk ρ) (liftWk σ) ↔ s.EqOn ρ σ := by
  rw [<-@liftWk_eqOn_succ_iff _ _ s]
  simp

theorem Nat.liftWk_eqOn_insert_zero_iff {s : Set ℕ}
  : (insert 0 s).EqOn (liftWk ρ) (liftWk σ) ↔ s.EqOn (liftWk ρ) (liftWk σ) := by
  simp

theorem Nat.liftWk_eqOn_remove_zero_iff {s : Set ℕ}
  : (s \ {0}).EqOn (liftWk ρ) (liftWk σ) ↔ s.EqOn (liftWk ρ) (liftWk σ) := by
  rw [<-Nat.liftWk_eqOn_insert_zero_iff]; simp

theorem Nat.liftWk_eqOn_Iio_iff {M : ℕ}
  : (Set.Iio (M + 1)).EqOn (liftWk ρ) (liftWk σ) ↔ (Set.Iio M).EqOn ρ σ := by
  rw [<-@liftWk_eqOn_insert_succ_iff _ _ (Set.Iio M), iff_iff_eq]
  congr
  ext x
  cases x <;> simp [Nat.succ_lt_succ_iff]

theorem Nat.liftWk_eqOn_Ioo_iff {m M : ℕ}
  : (Set.Ioo (m + 1) (M + 1)).EqOn (liftWk ρ) (liftWk σ) ↔ (Set.Ioo m M).EqOn ρ σ := by
  rw [<-@liftWk_eqOn_succ_iff _ _ (Set.Ioo m M), iff_iff_eq]
  congr
  ext x
  cases x <;> simp [Nat.succ_lt_succ_iff]

theorem Nat.stepWk_eqOn_iff {s : Set ℕ} : s.EqOn (stepWk ρ) (stepWk σ) ↔ s.EqOn ρ σ
  := Set.eqOn_comp_left_iff_of_injective (Nat.succ_injective)

/-- Lift a weakening under `n` binders -/
def Nat.liftnWk (n : Nat) (ρ : Nat -> Nat) : Nat -> Nat
  := λm => if m < n then m else (ρ (m - n)) + n

/-- Step a weakening to ignore the first `n` variables -/
def Nat.stepnWk (n : Nat) (ρ : Nat -> Nat) : Nat -> Nat := (· + n) ∘ ρ

theorem Nat.liftnWk_zero : liftnWk 0 = id := by
  funext ρ m
  simp only [liftnWk, Nat.sub_zero, Nat.add_zero, id_eq, ite_eq_right_iff]
  intro H
  cases H

theorem Nat.stepnWk_zero : stepnWk 0 = id := rfl

theorem Nat.liftnWk_succ' (n) : liftnWk (n.succ) = liftWk ∘ liftnWk n := by
  induction n with
  | zero => funext ρ m; cases m <;> rfl
  | succ n I =>
    rw [I]
    funext ρ m
    cases m with
    | zero => rfl
    | succ m =>
      cases m with
      | zero => simp only [liftnWk, Nat.succ_lt_succ_iff, Nat.zero_lt_succ]; rfl
      | succ m =>
        simp only [liftnWk, Nat.succ_lt_succ_iff, Function.comp_apply, liftWk]
        split <;> simp_arith

theorem Nat.liftnWk_succ_apply' (n) (ρ) : liftnWk (n.succ) ρ = liftWk (liftnWk n ρ) := by
  rw [liftnWk_succ', Function.comp_apply]

theorem Nat.stepnWk_succ' (n) : stepnWk (n.succ) = stepWk ∘ stepnWk n := by
  induction n with
  | zero => rfl
  | succ n I =>
    rw [I]
    funext ρ m
    cases m with
    | zero => rfl
    | succ m => simp_arith [stepnWk, stepWk]

theorem Nat.liftnWk_one : liftnWk 1 = liftWk := by simp [liftnWk_succ', liftnWk_zero]

theorem Nat.stepnWk_one : stepnWk 1 = stepWk := rfl

theorem Nat.liftnWk_two : liftnWk 2 = liftWk ∘ liftWk
  := by simp [liftnWk_succ', liftnWk_one, liftnWk_zero]

theorem Nat.liftnWk_two_apply (ρ) : liftnWk 2 ρ = liftWk (liftWk ρ) := by
  rw [liftnWk_two]; rfl

theorem Nat.liftnWk_eq_iterate_liftWk : liftnWk = Nat.iterate liftWk := by
  funext n
  induction n with
  | zero => rfl
  | succ n I => rw [liftnWk_succ', I, Function.iterate_succ']

theorem Nat.stepnWk_eq_iterate_stepWk : stepnWk = Nat.iterate stepWk := by
  funext n
  induction n with
  | zero => rfl
  | succ n I => rw [stepnWk_succ', I, Function.iterate_succ']

theorem Nat.liftnWk_succ (n) : liftnWk (n.succ) = liftnWk n ∘ liftWk := by
  rw [liftnWk_eq_iterate_liftWk, Function.iterate_succ]

theorem Nat.liftnWk_succ_apply (n) (ρ) : liftnWk (n.succ) ρ = liftnWk n (liftWk ρ) := by
  rw [liftnWk_eq_iterate_liftWk, Function.iterate_succ_apply]

theorem Nat.liftWk_comm_liftnWk (n) : liftWk ∘ liftnWk n = liftnWk n ∘ liftWk := by
  rw [<-Nat.liftnWk_succ, <-Nat.liftnWk_succ']

theorem Nat.liftWk_comm_liftnWk_apply (n) (ρ) : liftWk (liftnWk n ρ) = liftnWk n (liftWk ρ) := by
  rw [<-Nat.liftnWk_succ_apply, <-Nat.liftnWk_succ_apply']

theorem Nat.liftnWk_comm_liftWk (n) : liftnWk n ∘ liftWk = liftWk ∘ liftnWk n := by
  rw [Nat.liftWk_comm_liftnWk]

theorem Nat.liftnWk_comm_liftWk_apply (n) (ρ) : liftnWk n (liftWk ρ) = liftWk (liftnWk n ρ) := by
  rw [Nat.liftWk_comm_liftnWk_apply]

theorem Nat.stepnWk_succ (n) : stepnWk (n.succ) = stepnWk n ∘ stepWk := by
  rw [stepnWk_eq_iterate_stepWk, Function.iterate_succ]

theorem Nat.liftnWk_add (m n : ℕ) : liftnWk (m + n) = liftnWk m ∘ liftnWk n
  := by rw [liftnWk_eq_iterate_liftWk, Function.iterate_add]

theorem Nat.liftnWk_add_apply (m n : ℕ) (ρ) : liftnWk (m + n) ρ = liftnWk m (liftnWk n ρ)
  := by rw [liftnWk_eq_iterate_liftWk, Function.iterate_add_apply]

theorem Nat.liftnWk_add' (m n : ℕ) : liftnWk (n + m) = liftnWk m ∘ liftnWk n
  := by rw [add_comm, Nat.liftnWk_add]

theorem Nat.liftnWk_add_apply' (m n : ℕ) (ρ) : liftnWk (n + m) ρ = liftnWk m (liftnWk n ρ)
  := by rw [add_comm, Nat.liftnWk_add_apply]

theorem Nat.liftnWk_comm_liftnWk (m n) : liftnWk m ∘ liftnWk n = liftnWk n ∘ liftnWk m
  := by rw [<-Nat.liftnWk_add, add_comm, Nat.liftnWk_add]

theorem Nat.liftnWk_comm_liftnWk_apply (m n ρ) : liftnWk m (liftnWk n ρ) = liftnWk n (liftnWk m ρ)
  := by rw [<-Nat.liftnWk_add_apply, add_comm, Nat.liftnWk_add_apply]

theorem Nat.stepnWk_add (m n : ℕ) : stepnWk (m + n) = stepnWk m ∘ stepnWk n
  := by rw [stepnWk_eq_iterate_stepWk, Function.iterate_add]

theorem Nat.stepnWk_add_apply (m n : ℕ) (ρ) : stepnWk (m + n) ρ = stepnWk m (stepnWk n ρ)
  := by rw [stepnWk_eq_iterate_stepWk, Function.iterate_add_apply]

@[simp]
theorem Nat.iterate_liftWk_id : (n : ℕ) -> liftWk^[n] id = id
  | 0 => rfl
  | n + 1 => by simp [liftWk_id, iterate_liftWk_id n]

theorem Nat.iterate_liftWk_comp : (n : ℕ)
  -> ∀ρ σ, liftWk^[n] (ρ ∘ σ) = liftWk^[n] ρ ∘ liftWk^[n] σ
  | 0, _, _ => rfl
  | n + 1, _, _ => by simp [liftWk_comp, iterate_liftWk_comp n]

@[simp]
theorem Nat.liftnWk_id (n) : liftnWk n id = id := by
  rw [liftnWk_eq_iterate_liftWk, iterate_liftWk_id]

@[simp]
theorem Nat.liftnWk_id' (n) : liftnWk n (λx => x) = id := Nat.liftnWk_id n

theorem Nat.liftnWk_comp (n ρ σ) : liftnWk n (ρ ∘ σ) = liftnWk n ρ ∘ liftnWk n σ := by
  rw [liftnWk_eq_iterate_liftWk, iterate_liftWk_comp]

theorem Nat.liftnWk_comp_succ (n ρ) : liftnWk (n + 1) ρ ∘ Nat.succ = Nat.succ ∘ liftnWk n ρ := by
  rw [liftnWk_succ_apply', liftWk_comp_succ]

theorem Nat.liftnWk_comp_add_left (n m ρ) : liftnWk (n + m) ρ ∘ (· + m) = (· + m) ∘ liftnWk n ρ
  := by induction m with
  | zero => rfl
  | succ m I =>
    have h : (· + (m + 1)) = Nat.succ ∘ (· + m) := funext (λx => rfl)
    rw [<-add_assoc, h, <-Function.comp.assoc, liftnWk_comp_succ, Function.comp.assoc, I]
    rfl

theorem Nat.liftnWk_comp_add_right (n m ρ) : liftnWk (n + m) ρ ∘ (· + n) = (· + n) ∘ liftnWk m ρ
  := by rw [add_comm, liftnWk_comp_add_left]

theorem Nat.liftnWk_comp_add (n ρ) : liftnWk n ρ ∘ (· + n) = (· + n) ∘ ρ
  := liftnWk_comp_add_right n 0 ρ

/-- Weaken the `n`th variable of a term -/
def Nat.wkn (n: ℕ) := λ m => if m < n then m else m + 1

theorem Nat.liftnWk_n_succ (n : ℕ) : liftnWk n succ = wkn n := by
  funext m
  simp only [liftnWk, wkn]
  split
  case isTrue _ => rfl
  case isFalse h => simp_arith [Nat.le_of_not_lt h]

theorem Nat.wkn_zero : wkn 0 = succ := rfl

theorem Nat.wkn_one : wkn 1 = liftWk succ := by simp [<-liftnWk_n_succ, liftnWk_one]

theorem Nat.wkn_succ : wkn (n + 1) = liftWk (wkn n) := by
  simp only [<-liftnWk_n_succ, liftnWk_succ']; rfl

theorem Nat.wkn_add : wkn (m + n) = liftnWk m (wkn n) := by
  simp only [<-liftnWk_n_succ, <-liftnWk_add_apply]

theorem Nat.wkn_add_right : wkn (m + n) = liftnWk n (wkn m) := by rw [add_comm, wkn_add]

-- EqOn lore

-- TODO: liftnWk and stepnWk, equalities

-- TODO: liftnWk and stepnWk lore (injectivity, (strict) monotonicity, surjectivity, EqOn, etc)

-- TODO: define the weakenings (T, P); induction on weakenings

-- TODO: liftnWk, stepnWk of weakenings are weakenings

-- TODO: weakenings are closed under composition ==> form a monoid

-- TODO: the weakenings are the strictly monotonic functions s.t.
-- ∃c k, ∀n ≥ k, f(n) = n + c

-- TODO: if f is strictly monotonic, (∃N, ∀n, f(n) ≤ n + N) ↔ (∃c k, ∀n ≥ k, f(n) = n + c)

-- TODO: therefore, the weakenings are the strictly monotonic functions s.t. ∃N, ∀n, f(n) ≤ n + N

-- TODO: define the bounded weakenings (T, P); induction on bounded weakenings

-- TODO: liftnWk, stepnWk of bounded weakenings are bounded weakenings

-- TODO: the bounded weakenings are the strictly monotonic functions on their interval

-- TODO: bounded weakenings are closed under composition ==> form a _category_

-- TODO: not gaunt, since unrestricted outside interval

/-- "unlift" a map on `ℕ` -/
def Nat.unliftWk (ρ : Nat → Nat) : Nat → Nat := Nat.pred ∘ ρ ∘ Nat.succ

@[simp]
theorem Nat.unliftWk_liftWk (ρ) : unliftWk (liftWk ρ) = ρ := by
  funext n
  cases n <;> simp [unliftWk, liftWk]

@[simp]
theorem Nat.unliftWk_comp_liftWk : unliftWk ∘ liftWk = id := by
  funext ρ; exact unliftWk_liftWk ρ

theorem Nat.unliftWk_wkn_succ (n) : unliftWk (wkn (n + 1)) = wkn n := by simp [wkn_succ]

/-- "unlift" a map on `ℕ`, removing `n` binders -/
def Nat.unliftnWk (n: Nat) (ρ : Nat → Nat) : Nat → Nat := (λx => x - n) ∘ ρ ∘ (λx => x + n)

theorem Nat.unliftnWk_zero : unliftnWk 0 = id := by
  funext ρ n
  simp [unliftnWk]

theorem Nat.unliftnWk_one : unliftnWk 1 = unliftWk := by
  funext ρ n
  simp [unliftnWk, unliftWk]

theorem Nat.unliftnWk_succ (n) : unliftnWk (n + 1) = unliftnWk n ∘ unliftWk := by
  funext ρ m
  simp only [unliftnWk, Function.comp_apply, unliftWk, succ_eq_add_one, pred_eq_sub_one]
  rw [Nat.add_assoc, Nat.sub_succ, Nat.pred_eq_sub_one, Nat.sub_sub, Nat.sub_sub]
  congr 1
  rw [Nat.add_comm]

theorem Nat.unliftnWk_eq_iterate_unliftWk: unliftnWk = Nat.iterate unliftWk := by
  funext n
  induction n with
  | zero => rfl
  | succ n I => rw [unliftnWk_succ, I, Function.iterate_succ]

theorem Nat.unliftnWk_succ' (n): unliftnWk (n.succ) = unliftWk ∘ unliftnWk n := by
  rw [unliftnWk_eq_iterate_unliftWk, Function.iterate_succ']

theorem Nat.unliftnWk_comp_liftnWk : unliftnWk n ∘ liftnWk n = id := by
  induction n with
  | zero => simp [unliftnWk_zero, liftnWk_zero]
  | succ n I =>
    rw [
      unliftnWk_succ,
      liftnWk_succ',
      Function.comp.assoc,
      <-Function.comp.assoc unliftWk,
      unliftWk_comp_liftWk
      ]
    simp [I]

theorem Nat.unliftnWk_liftnWk : unliftnWk n (liftnWk n ρ) = ρ
  := congrFun unliftnWk_comp_liftnWk ρ

theorem Nat.unliftnWk_wkn_add (m n: ℕ): unliftnWk n (wkn (n + m)) = wkn m := by
  rw [wkn_add, unliftnWk_liftnWk]

theorem Nat.unliftnWk_wkn_add_right (m n: ℕ): unliftnWk n (wkn (m + n)) = wkn m := by
  rw [add_comm, unliftnWk_wkn_add]

/-- A map on `ℕ` may be constructed via `liftWk` -/
def Nat.isLift (f : Nat → Nat) : Prop := f 0 = 0 ∧ ∀i, f (i + 1) ≠ 0

theorem Nat.wkn_isLift_iff (n) : isLift (wkn n) ↔ n ≠ 0 := by
  simp only [isLift, wkn, zero_add, ite_eq_left_iff, not_lt, le_zero_eq, one_ne_zero, imp_false,
    ne_eq, and_iff_left_iff_imp]
  intros
  split <;> simp

-- TODO: isLift iff f = liftWk (unliftWk f) iff ∃ρ, f = liftWk ρ

-- TODO: in particular, liftWk isLift

/-- A map on `ℕ` may be constructed via `liftnWk` -/
def Nat.isLiftn (n : ℕ) (f : Nat → Nat) : Prop := ∀i, (i < n -> f i = i) ∧ (i ≥ n -> f i ≥ n)

-- TODO: isLiftn iff f = liftnWk n (unliftnWk n f) iff ∃ρ, f = liftnWk n ρ

-- TODO: in particular, liftnWk n is isLiftn n and isLiftn n f ==> liftnWk (n + 1) (liftWk f)

-- TODO: isLiftn 0 = True

-- TODO: isLiftn (n + 1) ==> isLiftn n

-- TODO: ∀n, isLiftn n f iff f = id
