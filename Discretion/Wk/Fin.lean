import Discretion.Wk.Nat

variable [PartialOrder α]


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

-- TODO: casesAdd
def Fin.liftnWk (k) {n m} (ρ : Fin n -> Fin m) (i : Fin (n + k)) : Fin (m + k)
  := if h : i < k then ⟨i, Nat.lt_add_left _ h⟩ else (ρ (i.subNat k (Nat.le_of_not_lt h))).addNat k

-- TODO: extendWk, liftWk, stepWk preserve injectivity, monotonicity, strict monotonicity
-- TODO: extendWk, liftWk preserve surjectivity ==> bijectivity

-- TODO: liftnWk and stepnWk, equalities

-- TODO: liftnWk and stepnWk lore (injectivity, (strict) monotonicity, surjectivity, EqOn, etc)

/-- Restrict a weakening to a finite weakening -/
def Fin.wkOfBounded {n m} (ρ : Nat -> Nat) (H : ∀k, k < n -> ρ k < m) : Fin n -> Fin m
  := λk => ⟨ρ k, H k (Fin.is_lt k)⟩

@[simp]
theorem Fin.wkOfBounded_id : @wkOfBounded n n id (λ_ h => h) = id := rfl

theorem Fin.wkOfBounded_comp {n m k}
    {ρ : Nat -> Nat} {hρ}
    {σ : Nat -> Nat} {hσ}
    : @wkOfBounded m k σ hσ ∘ @wkOfBounded n m ρ hρ = wkOfBounded (σ ∘ ρ) (λk h => hσ _ (hρ k h))
  := rfl

theorem Fin.wkOfBounded_strictMono {n m} {ρ : Nat -> Nat} {hρ}
  : StrictMono ρ -> StrictMono (@wkOfBounded n m ρ hρ) := by
  intro hρ' k l h
  simp only [wkOfBounded]
  exact hρ' h

-- TODO: wkOfBounded is surjective

-- TODO: wkOfBounded is (strict) monotonic if f is (strict) monotonic on

/-- Extend a finite weakening to a weakening on `Nat` -/
def Fin.toNatWk {n m} (ρ : Fin n → Fin m) : Nat → Nat
  := λk => if h : k < n then ρ ⟨k, h⟩ else (k - n) + m

@[simp]
theorem Fin.toNatWk_id (n) : toNatWk (@id (Fin n)) = id := by
  funext k
  unfold toNatWk
  aesop

theorem Fin.toNatWk_comp {n m k} (ρ : Fin m -> Fin k) (σ : Fin n -> Fin m)
    : toNatWk (ρ ∘ σ) = toNatWk ρ ∘ toNatWk σ := by
  funext k
  unfold toNatWk
  simp only [Function.comp_apply]
  split
  simp only [is_lt, ↓reduceDite, Fin.eta]
  simp_arith [Nat.add_sub_cancel]

theorem Fin.toNatWk_comp_lower_bound {n m} (ρ : Fin n -> Fin m) (σ : ℕ → ℕ) (hσ : ∀k, n ≤ σ k)
    : toNatWk ρ ∘ σ = (· - n + m) ∘ σ := by
  funext k
  simp [toNatWk, Nat.not_lt_of_le (hσ k)]

theorem Fin.toNatWk_perm_comp_lower_bound {n} (ρ : Fin n -> Fin n) (σ : ℕ → ℕ) (hσ : ∀k, n ≤ σ k)
    : toNatWk ρ ∘ σ = σ := by
  rw [toNatWk_comp_lower_bound _ _ hσ]
  funext k
  simp [Nat.sub_add_cancel (hσ k)]

theorem Fin.toNatWk_comp_add {n m} (ρ : Fin n -> Fin m)
    : toNatWk ρ ∘ (· + n) = (· + m) := by
  rw [toNatWk_comp_lower_bound _ _ (by simp)]
  funext k
  simp

theorem Fin.toNatWk_swapAdd_comp_liftnWk_add_apply (n m i : ℕ)
  : toNatWk (swapAdd n m) (n.liftnWk (· + m) i) = i + m := by
  simp [toNatWk, Nat.liftnWk, swapAdd, addCases]
  split
  case isTrue h =>
    rw [dite_cond_eq_true]
    simp [Nat.add_comm]
    simp [Nat.lt_add_right m h]
  case isFalse h =>
    have h' := Nat.le_of_not_lt h
    have hi : i - n + m + n = i + m := by
      rw [Nat.add_assoc, Nat.add_comm m n, <-Nat.add_assoc, Nat.sub_add_cancel h']
    simp [hi, h, h', Nat.add_comm m n, Nat.sub_add_cancel (Nat.add_le_add_right h' m)]

theorem Fin.toNatWk_swapAdd_comp_liftnWk_add (n m : ℕ)
  : toNatWk (swapAdd n m) ∘ n.liftnWk (· + m) = (· + m)
  := funext (Fin.toNatWk_swapAdd_comp_liftnWk_add_apply n m)

theorem Fin.toNatWk_symm_swapAdd_comp_liftnWk_add (n m : ℕ)
  : toNatWk (swapAdd m n).symm ∘ n.liftnWk (· + m) = (· + m)
  := toNatWk_swapAdd_comp_liftnWk_add n m

-- TODO: wkOfBounded ∘ toNatWk = id

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

/-- The function `ρ` weakens `Γ` to `Δ` -/
def Fin.FWkn {n m : Nat} (Γ : Fin n → α) (Δ : Fin m → α) (ρ : Fin m → Fin n) : Prop
  := (Γ ∘ ρ) ≤ Δ

theorem Fin.FWkn.id {n : Nat} (Γ : Fin n → α) : Fin.FWkn Γ Γ id := le_refl _

-- theorem Fin.FWkn.comp {ρ : Fin m → Fin n} {σ : Fin o → Fin m}
--   (hρ : Fin.FWkn Γ Δ ρ) (hσ : Fin.FWkn Δ Ξ σ) : Fin.FWkn Γ Ξ (ρ ∘ σ)
--   := λ_ => le_trans (hρ _) (hσ _)
