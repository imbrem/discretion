import Discretion.Wk.Fun
import Mathlib.Data.Fintype.Card

/-- The function `ρ` weakens `Γ` to `Δ` -/
def Fin.FWkn [PartialOrder α] {n m : Nat}
  (Γ : Fin n → α) (Δ : Fin m → α) (ρ : Fin m → Fin n) : Prop
  := (Γ ∘ ρ) ≤ Δ

/-- The function `ρ` weakens `Γ` to `Δ` -/
def List.FWkn [PartialOrder α] (Γ Δ : List α) (ρ : Fin Δ.length → Fin Γ.length) : Prop
  := (Γ.get ∘ ρ) ≤ Δ.get

theorem List.FWkn.id [PartialOrder α] (Γ : List α) : List.FWkn Γ Γ id := le_refl _

theorem List.FWkn.comp [PartialOrder α] {Γ Δ Ξ : List α}
  {ρ : Fin Δ.length → Fin Γ.length} {σ : Fin Ξ.length → Fin Δ.length}
  (hρ : List.FWkn Γ Δ ρ) (hσ : List.FWkn Δ Ξ σ) : List.FWkn Γ Ξ (ρ ∘ σ)
  := λ_ => le_trans (hρ _) (hσ _)

theorem List.FWkn.lift [PartialOrder α] {Γ Δ : List α} {ρ : Fin Δ.length → Fin Γ.length}
  (hAB : A ≤ B) (hρ : List.FWkn Γ Δ ρ) : List.FWkn (A :: Γ) (B :: Δ) (Fin.liftWk ρ)
  := λi => by cases i using Fin.cases with
  | zero => exact hAB
  | succ i => exact hρ i

theorem List.FWkn.step [PartialOrder α] {Γ Δ : List α} {ρ : Fin Δ.length → Fin Γ.length}
  (A : α) (hρ : List.FWkn Γ Δ ρ) : List.FWkn (A :: Γ) Δ (Fin.stepWk ρ)
  := λi => hρ i

/-- The `Γ` weakens to `Δ` -/
def List.FWkns [PartialOrder α] (Γ Δ : List α) : Prop := ∃ρ, List.FWkn Γ Δ ρ ∧ StrictMono ρ

theorem List.FWkns.refl [PartialOrder α] (Γ : List α) : List.FWkns Γ Γ
  := ⟨id, List.FWkn.id Γ, strictMono_id⟩

theorem List.FWkns.trans [PartialOrder α] {Γ Δ Ξ : List α}
  (hAB : List.FWkns Γ Δ) (hBC : List.FWkns Δ Ξ) : List.FWkns Γ Ξ
  := match hAB, hBC with
  | ⟨ρ, hAB, hρ⟩, ⟨σ, hBC, hσ⟩ => ⟨ρ ∘ σ, List.FWkn.comp hAB hBC, hρ.comp hσ⟩

theorem List.FWkns.len_le [PartialOrder α] {Γ Δ : List α} (hAB : List.FWkns Γ Δ)
  : Δ.length ≤ Γ.length
  := match hAB with | ⟨ρ, _, hρ⟩ => by {
    have h := Fintype.card_fin _ ▸ Fintype.card_fin _ ▸ Fintype.card_le_of_injective _ hρ.injective;
    simp only [Fintype.card_fin] at h
    exact h
  }

theorem List.FWkns.antisymm [PartialOrder α] {Γ Δ : List α}
  (hAB : List.FWkns Γ Δ) (hBA : List.FWkns Δ Γ) : Γ = Δ
  :=
  -- TODO: why does le_antisymm not work here?
  have len_eq : Γ.length = Δ.length := le_antisymm_iff.mpr ⟨hBA.len_le, hAB.len_le⟩
  match hAB, hBA with
  | ⟨ρ, hAB, hρ⟩, ⟨σ, hBA, hσ⟩
    => by
      cases Fin.strictMono_eq_cast hρ len_eq.symm
      cases Fin.strictMono_eq_cast hσ len_eq
      exact List.ext_get len_eq λi h h' => le_antisymm_iff.mpr ⟨hAB ⟨i, h'⟩, hBA ⟨i, h⟩⟩

/-- The function `ρ` weakens `Γ` to `Δ` -/
def List.NWkn [PartialOrder α] (Γ Δ : List α) (ρ : ℕ → ℕ) : Prop
  := ∀n, (hΔ : n < Δ.length) → ∃hΓ : ρ n < Γ.length, Γ.get ⟨ρ n , hΓ⟩ ≤ Δ.get ⟨n, hΔ⟩

theorem List.NWkn.bounded [PartialOrder α] {Γ Δ : List α} {ρ : ℕ → ℕ}
  (h : List.NWkn Γ Δ ρ) (n : ℕ) (hΔ : n < Δ.length) : ρ n < Γ.length
  := match h n hΔ with | ⟨hΓ, _⟩ => hΓ

/-- Restrict `ρ` from a function on `ℕ` to indices into `Δ` -/
def List.NWkn.toFinWk [PartialOrder α] {Γ Δ : List α} {ρ : ℕ → ℕ}
  (h : List.NWkn Γ Δ ρ) : Fin (Δ.length) → Fin (Γ.length)
  := Fin.wkOfBounded ρ h.bounded

theorem List.NWkn.toFWkn [PartialOrder α] (Γ Δ : List α) (ρ : ℕ → ℕ)
  (h : List.NWkn Γ Δ ρ) : List.FWkn Γ Δ (List.NWkn.toFinWk h)
  := λ⟨i, hi⟩ => have ⟨_, h⟩ := h i hi; h

theorem List.NWkn_iff [PartialOrder α] (Γ Δ : List α) (ρ : ℕ → ℕ)
  : List.NWkn Γ Δ ρ ↔ ∃ρ', List.FWkn Γ Δ ρ' ∧ ∀i : Fin Δ.length, ρ i = ρ' i
  := ⟨
    λh => ⟨_, h.toFWkn, λ_ => rfl⟩,
    λ⟨ρ', h, hρ'⟩ n hΔ =>
      have hρ' : ρ n = ρ' ⟨n, hΔ⟩ := hρ' ⟨n, hΔ⟩;
      have hΓ' : ρ' ⟨n, hΔ⟩ < Γ.length := by simp;
      have hΓ : ρ n < Γ.length := hρ' ▸ hΓ';
      have h' : Γ.get ⟨ρ' ⟨n, hΔ⟩, hΓ'⟩ ≤ Δ.get ⟨n, hΔ⟩ := h ⟨n, hΔ⟩;
      have hΓn : Γ.get ⟨ρ' ⟨n, hΔ⟩, hΓ'⟩ = Γ.get ⟨ρ n, hΓ⟩ := by
        congr
        exact hρ'.symm
      ⟨hρ' ▸ hΓ, hΓn ▸ h'⟩
  ⟩

theorem List.NWkn.id [PartialOrder α] (Γ : List α) : List.NWkn Γ Γ id
  := λ_ hΓ => ⟨hΓ, le_refl _⟩

theorem List.NWkn.len_le [PartialOrder α] {Γ Δ : List α} (h : List.NWkn Γ Δ ρ) (hρ : StrictMono ρ)
  : Δ.length ≤ Γ.length
  := FWkns.len_le ⟨_, h.toFWkn, Fin.wkOfBounded_strictMono hρ⟩

theorem List.NWkn.id_len_le [PartialOrder α] {Γ Δ : List α} (h : List.NWkn Γ Δ _root_.id)
  : Δ.length ≤ Γ.length := h.len_le strictMono_id

theorem List.NWkn.drop_all [PartialOrder α] (Γ : List α) (ρ) : List.NWkn Γ [] ρ
  := λi h => by cases h

theorem List.NWkn.comp [PartialOrder α] {Γ Δ Ξ : List α}
  {ρ : ℕ → ℕ} {σ : ℕ → ℕ} (hρ : List.NWkn Γ Δ ρ) (hσ : List.NWkn Δ Ξ σ) : List.NWkn Γ Ξ (ρ ∘ σ)
  := λn hΞ =>
    have ⟨hΔ, hσ⟩ := hσ n hΞ;
    have ⟨hΓ, hρ⟩ := hρ _ hΔ;
    ⟨hΓ, le_trans hρ hσ⟩

theorem List.NWkn.lift [PartialOrder α] {Γ Δ : List α} {ρ : ℕ → ℕ}
  (hAB : A ≤ B) (hρ : List.NWkn Γ Δ ρ) : List.NWkn (A :: Γ) (B :: Δ) (Nat.liftWk ρ)
  := λn hΔ => match n with
  | 0 => ⟨Nat.zero_lt_succ _, hAB⟩
  | n+1 => have ⟨hΔ, hρ⟩ := hρ n (Nat.lt_of_succ_lt_succ hΔ); ⟨Nat.succ_lt_succ hΔ, hρ⟩

theorem List.NWkn.of_lift [PartialOrder α] {Γ Δ : List α} {ρ : ℕ → ℕ}
  (h : List.NWkn (A :: Γ) (B :: Δ) (Nat.liftWk ρ)) : List.NWkn Γ Δ ρ
  := λi hΔ => have ⟨hΔ, hρ⟩ := h i.succ (Nat.succ_lt_succ hΔ); ⟨Nat.lt_of_succ_lt_succ hΔ, hρ⟩

theorem List.NWkn.le_of_lift [PartialOrder α] {Γ Δ : List α} {ρ : ℕ → ℕ}
  (h : List.NWkn (A :: Γ) (B :: Δ) (Nat.liftWk ρ)) : A ≤ B
  := (h 0 (Nat.zero_lt_succ _)).2

theorem List.NWkn.lift_iff [PartialOrder α] (A B) (Γ Δ : List α) (ρ : ℕ → ℕ)
  : List.NWkn (A :: Γ) (B :: Δ) (Nat.liftWk ρ) ↔ A ≤ B ∧ List.NWkn Γ Δ ρ
  := ⟨
    λh => ⟨h.le_of_lift, List.NWkn.of_lift h⟩,
    λ⟨hAB, hρ⟩ => List.NWkn.lift hAB hρ
  ⟩

theorem List.NWkn.lift₂ [PartialOrder α] {Γ Δ : List α} {ρ : ℕ → ℕ}
  (hAB₁ : A₁ ≤ B₁) (hAB₂ : A₂ ≤ B₂) (hρ : List.NWkn Γ Δ ρ)
  : List.NWkn (A₁ :: A₂ :: Γ) (B₁ :: B₂ :: Δ) (Nat.liftWk (Nat.liftWk ρ))
  := (hρ.lift hAB₂).lift hAB₁

theorem List.NWkn.liftn₂ [PartialOrder α] {Γ Δ : List α} {ρ : ℕ → ℕ}
  (hAB₁ : A₁ ≤ B₁) (hAB₂ : A₂ ≤ B₂) (hρ : List.NWkn Γ Δ ρ)
  : List.NWkn (A₁ :: A₂ :: Γ) (B₁ :: B₂ :: Δ) (Nat.liftnWk 2 ρ)
  := by rw [Nat.liftnWk_eq_iterate_liftWk]; exact lift₂ hAB₁ hAB₂ hρ

theorem List.NWkn.liftn_append [PartialOrder α] {Γ Δ : List α} {ρ : ℕ → ℕ}
  (Ξ : List α) (hρ : List.NWkn Γ Δ ρ) : List.NWkn (Ξ ++ Γ) (Ξ ++ Δ) (Nat.liftnWk Ξ.length ρ) := by
  induction Ξ with
  | nil => exact hρ
  | cons A Ξ I =>
    rw [List.length, Nat.liftnWk_succ']
    exact I.lift (le_refl _)

theorem List.NWkn.liftn_append' [PartialOrder α] {Γ Δ : List α} {ρ : ℕ → ℕ} (Ξ : List α)
  (hΞ : Ξ.length = n) (hρ : List.NWkn Γ Δ ρ) : List.NWkn (Ξ ++ Γ) (Ξ ++ Δ) (Nat.liftnWk n ρ)
  := hΞ ▸ hρ.liftn_append Ξ

-- TODO: pointwise liftn

theorem List.NWkn.step [PartialOrder α] {Γ Δ : List α} {ρ : ℕ → ℕ}
  (A : α) (hρ : List.NWkn Γ Δ ρ) : List.NWkn (A :: Γ) Δ (Nat.succ ∘ ρ)
  := λn hΔ => have ⟨hΔ, hρ⟩ := hρ n hΔ; ⟨Nat.succ_lt_succ hΔ, hρ⟩

theorem List.NWkn.of_step [PartialOrder α] {Γ Δ : List α} {ρ : ℕ → ℕ}
  (h : List.NWkn (A :: Γ) Δ (Nat.succ ∘ ρ)) : List.NWkn Γ Δ ρ
  := λi hΔ => have ⟨hΔ, hρ⟩ := h i hΔ; ⟨Nat.lt_of_succ_lt_succ hΔ, hρ⟩

theorem List.NWkn.step_iff [PartialOrder α] (A) (Γ Δ : List α) (ρ : ℕ → ℕ)
  : List.NWkn (A :: Γ) Δ (Nat.succ ∘ ρ) ↔ List.NWkn Γ Δ ρ
  := ⟨
    List.NWkn.of_step,
    List.NWkn.step A
  ⟩

-- TODO: step₂, stepn₂, stepn

-- TODO: if the order is discrete, weakenings are unique iff there are no duplicates in the source

-- TODO: if the order is discrete and there are no duplicates in the source, then the are none
--       in the target

-- TODO: inductive weakening, associated lore
