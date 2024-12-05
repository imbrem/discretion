import Discretion.Wk.Nat


/-!
# Finite Weakenings

Definitions and utilities for weakening finite de-Bruijn indices (represented as `Fin n`)
-/

/-- Step a finite weakening -/
def Fin.stepWk {n m} (ρ : Fin n -> Fin m) : Fin n -> Fin (m + 1)
  := Fin.succ ∘ ρ

theorem Fin.stepWk_injective (n m) : Function.Injective (@stepWk n m) := λ ρ σ h => by
  funext k
  have h := congr_fun h k
  simp only [stepWk, Function.comp_apply, succ_inj] at h
  exact h

theorem Fin.stepWk_inj {n m} {ρ σ : Fin n -> Fin m} : stepWk ρ = stepWk σ ↔ ρ = σ
  := ⟨λh => stepWk_injective _ _ h, λh => by cases h; rfl⟩

@[simp]
theorem Fin.stepWk_def {n m} (ρ : Fin n -> Fin m) (k : Fin n) : stepWk ρ k = (ρ k).succ := rfl

/-- Lift a finite weakening under a binder -/
def Fin.liftWk {n m} (ρ : Fin n -> Fin m) : Fin (n + 1) -> Fin (m + 1)
  := Fin.cases 0 (Fin.succ ∘ ρ)

@[simp]
theorem Fin.liftWk_zero {n m} (ρ : Fin n -> Fin m) : liftWk ρ 0 = 0 := rfl

@[simp]
theorem Fin.liftWk_succ {n m} (ρ : Fin n -> Fin m) (k : Fin n) : liftWk ρ k.succ = (ρ k).succ := rfl

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

theorem Fin.liftWk_inj {n m} {ρ σ : Fin n -> Fin m} : liftWk ρ = liftWk σ ↔ ρ = σ
  := ⟨λh => liftWk_injective _ _ h, λh => by cases h; rfl⟩

@[simp]
theorem Fin.liftWk_ne_stepWk {n m}
  (ρ : Fin n → Fin m)
  (σ : Fin (n + 1) → Fin m)
  : liftWk ρ ≠ stepWk σ := by
  intro h
  have h' := congr_fun h 0
  simp only [liftWk, cases_zero, stepWk, Function.comp_apply] at h'
  cases h'

@[simp]
theorem Fin.stepWk_ne_liftWk {n m}
  (ρ : Fin n → Fin m)
  (σ : Fin (n + 1) → Fin m)
  : stepWk σ ≠ liftWk ρ := Ne.symm (Fin.liftWk_ne_stepWk _ _)


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
theorem Fin.toNatWk_coe {n m} (ρ : Fin n → Fin m) (k : Fin n) : toNatWk ρ k = ρ k := by
  simp [toNatWk]

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
  simp only [is_lt, ↓reduceDIte, Fin.eta]
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

theorem Fin.toNatWk_comp_liftnWk {n m} (σ : ℕ → ℕ) (ρ : Fin n -> Fin m)
  : Fin.toNatWk ρ ∘ Nat.liftnWk n σ = Nat.liftnWk m σ ∘ Fin.toNatWk ρ := by
  funext i
  simp only [Function.comp_apply, Nat.liftnWk, toNatWk]
  split <;> simp_arith

theorem Fin.liftnWk_comp_toNatWk {n m} (σ : ℕ → ℕ) (ρ : Fin n -> Fin m)
  : Nat.liftnWk m σ ∘ Fin.toNatWk ρ = Fin.toNatWk ρ ∘ Nat.liftnWk n σ
  := by rw [toNatWk_comp_liftnWk]

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

-- The function `ρ` sends `Γ` to `Δ` -/
def Fin.FEWkn {n m : Nat} (Γ : Fin n → α) (Δ : Fin m → α) (ρ : Fin m → Fin n) : Prop
  := (Γ ∘ ρ) = Δ

theorem Fin.FEWkn.apply {n m : Nat} {Γ : Fin n → α} {Δ : Fin m → α} {ρ : Fin m → Fin n}
  (h : Fin.FEWkn Γ Δ ρ) (k : Fin m) : Γ (ρ k) = Δ k
  := by rw [<-Function.comp_apply (f := Γ), h]

theorem Fin.FEWkn.id {n : Nat} (Γ : Fin n → α) : Fin.FEWkn Γ Γ id := rfl

theorem Fin.FEWkn.comp {n m o : Nat} {Γ : Fin n → α} {Δ : Fin m → α} {Ξ : Fin o → α}
  {ρ : Fin m → Fin n} {σ : Fin o → Fin m}
  (hρ : Fin.FEWkn Γ Δ ρ) (hσ : Fin.FEWkn Δ Ξ σ) : Fin.FEWkn Γ Ξ (ρ ∘ σ)
  := by rw [FEWkn, <-Function.comp_assoc, hρ, hσ]

theorem Fin.FEWkn.trg_eq {n m : Nat} {Γ : Fin n → α} {Δ Δ' : Fin m → α} {ρ : Fin m → Fin n}
  (h : Fin.FEWkn Γ Δ ρ) (h' : Fin.FEWkn Γ Δ' ρ) : Δ = Δ'
  := by cases h; cases h'; rfl

variable [PartialOrder α]

/-- The function `ρ` weakens `Γ` to `Δ` -/
def Fin.FWkn {n m : Nat} (Γ : Fin n → α) (Δ : Fin m → α) (ρ : Fin m → Fin n) : Prop
  := (Γ ∘ ρ) ≤ Δ

theorem Fin.FWkn.apply {n m : Nat} {Γ : Fin n → α} {Δ : Fin m → α} {ρ : Fin m → Fin n}
  (h : Fin.FWkn Γ Δ ρ) (k : Fin m) : Γ (ρ k) ≤ Δ k
  := h k

theorem Fin.FWkn.id {n : Nat} (Γ : Fin n → α) : Fin.FWkn Γ Γ id := le_refl _

theorem Fin.FWkn.comp {n m o : Nat} {Γ : Fin n → α} {Δ : Fin m → α} {Ξ : Fin o → α}
  {ρ : Fin m → Fin n} {σ : Fin o → Fin m}
  (hρ : Fin.FWkn Γ Δ ρ) (hσ : Fin.FWkn Δ Ξ σ) : Fin.FWkn Γ Ξ (ρ ∘ σ)
  := le_trans (by rw [<-Function.comp_assoc]; exact Function.comp_left_mono hρ) hσ

theorem Fin.FEWkn.toFWkn {n m : Nat} {Γ : Fin n → α} {Δ : Fin m → α} {ρ : Fin m → Fin n}
  (h : Fin.FEWkn Γ Δ ρ) : Fin.FWkn Γ Δ ρ
  := le_of_eq h
