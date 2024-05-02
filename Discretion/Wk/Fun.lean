import Mathlib.Logic.Function.Basic
import Mathlib.Data.Nat.Defs
import Mathlib.Data.Fin.Basic
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Order.Monotone.Basic

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

theorem Nat.pred_comp_succ : Nat.pred ∘ Nat.succ = id := funext Nat.pred_succ

theorem Nat.pred_stepWk_image (ρ) : Nat.pred '' (stepWk ρ '' s) = ρ '' s := by
  rw [stepWk_image, <-Set.image_comp, Nat.pred_comp_succ, Set.image_id]

theorem Nat.stepWk_image_eq_liftWk_image_succ (ρ) : stepWk ρ '' s = liftWk ρ '' (Nat.succ '' s) := by
  rw [stepWk_image, liftWk_image_succ_image]

-- TODO: liftWk and stepWk EqOn lore

def Nat.liftnWk (n: Nat) (ρ: Nat -> Nat): Nat -> Nat := λm => if m < n then m else (ρ (m - n)) + n

theorem Nat.liftnWk_zero: liftnWk 0 = id := by
  funext ρ m
  simp only [liftnWk, Nat.sub_zero, Nat.add_zero, id_eq, ite_eq_right_iff]
  intro H
  cases H

theorem Nat.liftnWk_succ' (n): liftnWk (n.succ) = liftWk ∘ liftnWk n := by
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

theorem Nat.liftnWk_eq_iterate_liftWk: liftnWk = Nat.iterate liftWk := by
  funext n
  induction n with
  | zero => rfl
  | succ n I => rw [liftnWk_succ', I, Function.iterate_succ']

theorem Nat.liftnWk_succ (n): liftnWk (n.succ) = liftnWk n ∘ liftWk := by
  rw [liftnWk_eq_iterate_liftWk, Function.iterate_succ]

theorem Nat.liftnWk_add (m n: ℕ): liftnWk (m + n) = liftnWk m ∘ liftnWk n
  := by rw [liftnWk_eq_iterate_liftWk, Function.iterate_add]
theorem Nat.liftnWk_add_apply (m n: ℕ) (ρ): liftnWk (m + n) ρ = liftnWk m (liftnWk n ρ)
  := by rw [liftnWk_eq_iterate_liftWk, Function.iterate_add_apply]

theorem Nat.iterate_liftWk_id: (n: ℕ) -> liftWk^[n] id = id
  | 0 => rfl
  | n + 1 => by simp [liftWk_id, iterate_liftWk_id n]
theorem Nat.iterate_liftWk_comp: (n: ℕ)
  -> ∀ρ σ, liftWk^[n] (ρ ∘ σ) = liftWk^[n] ρ ∘ liftWk^[n] σ
  | 0, _, _ => rfl
  | n + 1, _, _ => by simp [liftWk_comp, iterate_liftWk_comp n]

theorem Nat.liftnWk_id (n): liftnWk n id = id := by
  rw [liftnWk_eq_iterate_liftWk, iterate_liftWk_id]
theorem Nat.liftnWk_comp (n ρ σ): liftnWk n (ρ ∘ σ) = liftnWk n ρ ∘ liftnWk n σ := by
  rw [liftnWk_eq_iterate_liftWk, iterate_liftWk_comp]

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

/-!
# Finite Weakenings

Definitions and utilities for weakening finite de-Bruijn indices (represented as `Fin n`)
-/

/-- Step a finite weakening -/
def Fin.stepWk {n m} (ρ : Fin n -> Fin m) : Fin n -> Fin (m + 1)
  := Fin.succ ∘ ρ

/-- Lift a finite weakening under a binder -/
def Fin.liftWk {n m} (ρ : Fin n -> Fin m) : Fin (n + 1) -> Fin (m + 1)
  := Fin.cases 0 (Fin.succ ∘ ρ)

/-- Extend a finite weakening by one -/
def Fin.extendWk {n m} (ρ : Fin n -> Fin m) : Fin (n + 1) -> Fin (m + 1)
  := Fin.lastCases (Fin.last m) (Fin.castSucc ∘ ρ)

theorem Fin.liftWk_id (n) : liftWk (@id (Fin n)) = id := by
  funext ⟨k, H⟩
  cases k with
  | zero => rfl
  | succ k => rfl

theorem Fin.liftWk_injective (n m) : Function.Injective (@liftWk n m) := by
  intro ρ σ H
  funext k
  have H': liftWk ρ k.succ = liftWk σ k.succ := by rw [H]
  exact Fin.succ_injective _ H'

theorem Fin.liftWk_comp {n m} (ρ : Fin m -> Fin k) (σ : Fin n -> Fin m)
    : liftWk (ρ ∘ σ) = liftWk ρ ∘ liftWk σ := by
  funext ⟨k, Hk⟩; cases k <;> rfl

theorem Fin.liftWk_comp_succ {n m} (ρ : Fin n -> Fin m) : liftWk ρ ∘ Fin.succ = Fin.succ ∘ ρ := rfl

-- TODO: extendWk, liftWk, stepWk preserve injectivity, monotonicity, strict monotonicity
-- TODO: extendWk, liftWk preserve surjectivity ==> bijectivity

-- TODO: liftnWk and stepnWk, equalities

-- TODO: liftnWk and stepnWk lore (injectivity, (strict) monotonicity, surjectivity, EqOn, etc)

/-- Restrict a weakening to a finite weakening -/
def Fin.wkOfBounded {n m} (ρ : Nat -> Nat) (H : ∀k, k < n -> ρ k < m) : Fin n -> Fin m
  := λk => ⟨ρ k, H k (Fin.is_lt k)⟩

/-- Extend a finite weakening to a weakening on `Nat` -/
def Fin.toNatWk {n m} (ρ : Fin n → Fin m) : Nat → Nat
  := λk => if h : k < n then ρ ⟨k, h⟩ else (k - n) + m

-- TODO: wkOfBounded ∘ toNatWk = id

-- TODO: wkOfBounded is surjective

-- TODO: wkOfBounded is (strict) monotonic if f is (strict) monotonic on

-- TODO: toNatWk ∘ extendWk = toNatWk

-- TODO: toNatWk ∘ liftWk = liftWk ∘ toNatWk

-- TODO: toNatWk ∘ stepWk = stepWk ∘ toNatWk

-- TODO: iterative versions of the above

-- TODO: toNatWk ∘ liftnWk = liftnWk ∘ toNatWk

-- TODO: toNatWk ∘ stepnWk = stepnWk ∘ toNatWk

-- TODO: toNatWk is (strict) monotonic if underlying is (strict) monotonic

-- TODO: wkOfBounded, toNatWk functors

-- TODO: define a weakening to be a strictly monotonic function Fin n → Fin m

-- TODO: therefore, in particular, n ≤ m, and if n = m then f is the identity

-- TODO: i.e., weakenings Fin n → Fin m form a gaunt category and wkOfBounded, toNatWk functors

-- TODO: is this an adjunction or smt?

-- TODO: wkOfBounded is a weakening ↔ toNatWk is a weakening
