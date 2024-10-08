import Discretion.Wk.Nat
import Discretion.Wk.Fin
import Mathlib.Data.Fintype.Card

-- TODO: general relation edition...

/-- The function `ρ` sends `Γ` to `Δ` -/
def List.FEWkn (Γ Δ : List α) (ρ : Fin Δ.length → Fin Γ.length) : Prop
  := Fin.FEWkn Γ.get Δ.get ρ

theorem List.FEWkn.get {Γ Δ : List α} {ρ : Fin Δ.length → Fin Γ.length} (h : List.FEWkn Γ Δ ρ)
  : ∀i, Γ.get (ρ i) = Δ.get i := h.apply

theorem List.FEWkn.getElem {Γ Δ : List α} {ρ : Fin Δ.length → Fin Γ.length} (h : List.FEWkn Γ Δ ρ)
  : ∀i, Γ[ρ i] = Δ[i] := h.apply

theorem List.FEWkn.comp {ρ : Fin Δ.length → Fin Γ.length} {σ : Fin Ξ.length → Fin Δ.length}
  (hρ : List.FEWkn Γ Δ ρ) (hσ : List.FEWkn Δ Ξ σ) : List.FEWkn Γ Ξ (ρ ∘ σ)
  := Fin.FEWkn.comp hρ hσ

theorem List.FEWkn.lift {ρ : Fin Δ.length → Fin Γ.length} (hρ : List.FEWkn Γ Δ ρ)
    : List.FEWkn (A :: Γ) (A :: Δ) (Fin.liftWk ρ)
  := by funext i; cases i using Fin.cases with
  | zero => rfl
  | succ i =>
    simp only [length_cons, Function.comp_apply, Fin.liftWk, Fin.cases_succ, Fin.val_succ,
      get_eq_getElem, getElem_cons_succ]
    apply hρ.getElem

/-- The function `ρ` sends `Γ` to `Δ` -/
def List.NEWkn (Γ Δ : List α) (ρ : ℕ → ℕ) : Prop
  := ∀n, (hΔ : n < Δ.length) → ∃hΓ : ρ n < Γ.length, Γ[ρ n] = Δ[n]

theorem List.NEWkn.bounded {ρ : ℕ → ℕ} (h : List.NEWkn Γ Δ ρ) (n : ℕ) (hΔ : n < Δ.length)
  : ρ n < Γ.length := match h n hΔ with | ⟨hΓ, _⟩ => hΓ

def List.NEWkn.toFinWk {ρ : ℕ → ℕ} (h : List.NEWkn Γ Δ ρ) : Fin (Δ.length) → Fin (Γ.length)
  := Fin.wkOfBounded ρ h.bounded


theorem List.NEWkn.toFEWkn (Γ Δ : List α) (ρ : ℕ → ℕ)
  (h : List.NEWkn Γ Δ ρ) : List.FEWkn Γ Δ (List.NEWkn.toFinWk h)
  := funext λ⟨i, hi⟩ => have ⟨_, h⟩ := h i hi; h

-- ... TODO: NEWkns

theorem List.NEWkn.id (Γ : List α) : List.NEWkn Γ Γ id
  := λ_ hΓ => ⟨hΓ, rfl⟩

-- ... TODO: len_le

theorem List.NEWkn.drop_all (Γ : List α) (ρ) : List.NEWkn Γ [] ρ
  := λi h => by cases h

theorem List.NEWkn.comp {ρ : ℕ → ℕ} {σ : ℕ → ℕ} (hρ : List.NEWkn Γ Δ ρ) (hσ : List.NEWkn Δ Ξ σ)
  : List.NEWkn Γ Ξ (ρ ∘ σ) := λn hΞ =>
    have ⟨hΔ, hσ⟩ := hσ n hΞ;
    have ⟨hΓ, hρ⟩ := hρ _ hΔ;
    ⟨hΓ, hρ ▸ hσ⟩

theorem List.NEWkn.lift {ρ : ℕ → ℕ} (hρ : List.NEWkn Γ Δ ρ)
  : List.NEWkn (A :: Γ) (A :: Δ) (Nat.liftWk ρ) := λn hΔ => match n with
  | 0 => ⟨Nat.zero_lt_succ _, rfl⟩
  | n+1 => have ⟨hΔ, hρ⟩ := hρ n (Nat.lt_of_succ_lt_succ hΔ); ⟨Nat.succ_lt_succ hΔ, hρ⟩

theorem List.NEWkn.lift_tail {ρ : ℕ → ℕ} (h : List.NEWkn (A :: Γ) (B :: Δ) (Nat.liftWk ρ))
    : List.NEWkn Γ Δ ρ
  := λi hΔ => have ⟨hΔ, hρ⟩ := h i.succ (Nat.succ_lt_succ hΔ); ⟨Nat.lt_of_succ_lt_succ hΔ, hρ⟩

theorem List.NEWkn.lift_head {ρ : ℕ → ℕ} (h : List.NEWkn (A :: Γ) (B :: Δ) (Nat.liftWk ρ)) : A = B
  := (h 0 (Nat.zero_lt_succ _)).2

theorem List.NEWkn.lift_iff (A B) (Γ Δ : List α) (ρ : ℕ → ℕ)
  : List.NEWkn (A :: Γ) (B :: Δ) (Nat.liftWk ρ) ↔ A = B ∧ List.NEWkn Γ Δ ρ
  := ⟨
    λh => ⟨h.lift_head, List.NEWkn.lift_tail h⟩,
    λ⟨rfl, hρ⟩ => List.NEWkn.lift hρ
  ⟩

theorem List.NEWkn.lift_id (hρ : List.NEWkn Γ Δ _root_.id)
  : List.NEWkn (A :: Γ) (A :: Δ) _root_.id := Nat.liftWk_id ▸ hρ.lift

theorem List.NEWkn.lift_id_tail (h : List.NEWkn (left :: Γ) (right :: Δ) _root_.id)
    : List.NEWkn Γ Δ _root_.id
  := (Nat.liftWk_id ▸ h).lift_tail

theorem List.NEWkn.lift_id_head (h : List.NEWkn (left :: Γ) (right :: Δ) _root_.id)
  : left = right
  := (Nat.liftWk_id ▸ h).lift_head

theorem List.NEWkn.lift_id_iff (h : List.NEWkn (left :: Γ) (right :: Δ) _root_.id)
  : left = right ∧ List.NEWkn Γ Δ _root_.id
  := ⟨h.lift_id_head, h.lift_id_tail⟩

theorem List.NEWkn.lift₂ {ρ : ℕ → ℕ} (hρ : List.NEWkn Γ Δ ρ)
    : List.NEWkn (A₁ :: A₂ :: Γ) (A₁ :: A₂ :: Δ) (Nat.liftWk (Nat.liftWk ρ))
  := hρ.lift.lift

theorem List.NEWkn.liftn₂ {ρ : ℕ → ℕ} (hρ : List.NEWkn Γ Δ ρ)
    : List.NEWkn (A₁ :: A₂ :: Γ) (A₁ :: A₂ :: Δ) (Nat.liftnWk 2 ρ)
  := by rw [Nat.liftnWk_two]; exact hρ.lift₂

theorem List.NEWkn.liftn_append {ρ : ℕ → ℕ} (Ξ : List α) (hρ : List.NEWkn Γ Δ ρ)
    : List.NEWkn (Ξ ++ Γ) (Ξ ++ Δ) (Nat.liftnWk Ξ.length ρ) := by
  induction Ξ with
  | nil => exact hρ
  | cons A Ξ I =>
    rw [List.length, Nat.liftnWk_succ']
    exact I.lift

theorem List.NEWkn.liftn_append' {ρ : ℕ → ℕ} (Ξ : List α) (hΞ : Ξ.length = n)
  (hρ : List.NEWkn Γ Δ ρ) : List.NEWkn (Ξ ++ Γ) (Ξ ++ Δ) (Nat.liftnWk n ρ) := hΞ ▸ hρ.liftn_append Ξ

theorem List.NEWkn.step {ρ : ℕ → ℕ} (A : α) (hρ : List.NEWkn Γ Δ ρ)
    : List.NEWkn (A :: Γ) Δ (Nat.succ ∘ ρ)
  := λn hΔ => have ⟨hΔ, hρ⟩ := hρ n hΔ; ⟨Nat.succ_lt_succ hΔ, hρ⟩

theorem List.NEWkn.step_tail {ρ : ℕ → ℕ} (h : List.NEWkn (A :: Γ) Δ (Nat.succ ∘ ρ)) : List.NEWkn Γ Δ ρ
  := λi hΔ => have ⟨hΔ, hρ⟩ := h i hΔ; ⟨Nat.lt_of_succ_lt_succ hΔ, hρ⟩

theorem List.NEWkn.step_iff (A) (Γ Δ : List α) (ρ : ℕ → ℕ)
  : List.NEWkn (A :: Γ) Δ (Nat.succ ∘ ρ) ↔ List.NEWkn Γ Δ ρ
  := ⟨
    List.NEWkn.step_tail,
    List.NEWkn.step A
  ⟩

theorem List.NEWkn.stepn_append {ρ : ℕ → ℕ} (Ξ : List α) (hρ : List.NEWkn Γ Δ ρ)
    : List.NEWkn (Ξ ++ Γ) Δ (Nat.stepnWk Ξ.length ρ)
  := by induction Ξ with
    | nil => exact hρ
    | cons A Ξ I =>
      rw [List.length, Nat.stepnWk_succ']
      exact I.step _

theorem List.NEWkn.stepn_append' {ρ : ℕ → ℕ} (Ξ : List α) (hΞ : Ξ.length = n)
  (hρ : List.NEWkn Γ Δ ρ) : List.NEWkn (Ξ ++ Γ) Δ (Nat.stepnWk n ρ) := hΞ ▸ hρ.stepn_append Ξ


variable [PartialOrder α] {Γ Δ Ξ : List α}

/-- The function `ρ` weakens `Γ` to `Δ` -/
def List.FWkn (Γ Δ : List α) (ρ : Fin Δ.length → Fin Γ.length) : Prop
  := Fin.FWkn Γ.get Δ.get ρ

theorem List.FWkn.get {Γ Δ : List α} {ρ : Fin Δ.length → Fin Γ.length} (h : List.FWkn Γ Δ ρ)
  : ∀i, Γ.get (ρ i) ≤ Δ.get i := h

theorem List.FWkn.getElem {Γ Δ : List α} {ρ : Fin Δ.length → Fin Γ.length} (h : List.FWkn Γ Δ ρ)
  : ∀i, Γ[ρ i] ≤ Δ[i] := h

theorem List.FWkn.id (Γ : List α) : List.FWkn Γ Γ id := le_refl _

theorem List.FWkn.comp {ρ : Fin Δ.length → Fin Γ.length} {σ : Fin Ξ.length → Fin Δ.length}
  (hρ : List.FWkn Γ Δ ρ) (hσ : List.FWkn Δ Ξ σ) : List.FWkn Γ Ξ (ρ ∘ σ)
  := Fin.FWkn.comp hρ hσ

theorem List.FWkn.lift {ρ : Fin Δ.length → Fin Γ.length} (hAB : A ≤ B) (hρ : List.FWkn Γ Δ ρ)
    : List.FWkn (A :: Γ) (B :: Δ) (Fin.liftWk ρ)
  := λi => by cases i using Fin.cases with
  | zero => exact hAB
  | succ i => exact hρ i

theorem List.FWkn.step {ρ : Fin Δ.length → Fin Γ.length} (A : α) (hρ : List.FWkn Γ Δ ρ)
  : List.FWkn (A :: Γ) Δ (Fin.stepWk ρ) := λi => hρ i

/-- The list `Γ` weakens to `Δ` -/
def List.FWkns (Γ Δ : List α) : Prop := ∃ρ, List.FWkn Γ Δ ρ ∧ StrictMono ρ

theorem List.FWkns.refl (Γ : List α) : List.FWkns Γ Γ
  := ⟨id, List.FWkn.id Γ, strictMono_id⟩

theorem List.FWkns.trans (hAB : List.FWkns Γ Δ) (hBC : List.FWkns Δ Ξ) : List.FWkns Γ Ξ
  := match hAB, hBC with
  | ⟨ρ, hAB, hρ⟩, ⟨σ, hBC, hσ⟩ => ⟨ρ ∘ σ, List.FWkn.comp hAB hBC, hρ.comp hσ⟩

theorem List.FWkns.len_le (hAB : List.FWkns Γ Δ) : Δ.length ≤ Γ.length
  := match hAB with | ⟨ρ, _, hρ⟩ => by {
    have h := Fintype.card_fin _ ▸ Fintype.card_fin _ ▸ Fintype.card_le_of_injective _ hρ.injective;
    simp only [Fintype.card_fin] at h
    exact h
  }

theorem List.FWkns.antisymm (hAB : List.FWkns Γ Δ) (hBA : List.FWkns Δ Γ) : Γ = Δ :=
  -- TODO: why does le_antisymm not work here?
  have len_eq : Γ.length = Δ.length := le_antisymm_iff.mpr ⟨hBA.len_le, hAB.len_le⟩
  match hAB, hBA with
  | ⟨ρ, hAB, hρ⟩, ⟨σ, hBA, hσ⟩
    => by
      cases Fin.strictMono_eq_cast hρ len_eq.symm
      cases Fin.strictMono_eq_cast hσ len_eq
      exact List.ext_get len_eq λi h h' => le_antisymm_iff.mpr ⟨hAB ⟨i, h'⟩, hBA ⟨i, h⟩⟩

/-- The function `ρ` weakens `Γ` to `Δ` -/
def List.NWkn (Γ Δ : List α) (ρ : ℕ → ℕ) : Prop
  := ∀n, (hΔ : n < Δ.length) → ∃hΓ : ρ n < Γ.length, Γ.get ⟨ρ n , hΓ⟩ ≤ Δ.get ⟨n, hΔ⟩

theorem List.NWkn.bounded {ρ : ℕ → ℕ} (h : List.NWkn Γ Δ ρ) (n : ℕ) (hΔ : n < Δ.length)
  : ρ n < Γ.length := match h n hΔ with | ⟨hΓ, _⟩ => hΓ

-- TODO: abbrev, or remove?
/-- Restrict `ρ` from a function on `ℕ` to indices into `Δ` -/
def List.NWkn.toFinWk {ρ : ℕ → ℕ} (h : List.NWkn Γ Δ ρ) : Fin (Δ.length) → Fin (Γ.length)
  := Fin.wkOfBounded ρ h.bounded

theorem List.NWkn.toFWkn (Γ Δ : List α) (ρ : ℕ → ℕ)
  (h : List.NWkn Γ Δ ρ) : List.FWkn Γ Δ (List.NWkn.toFinWk h)
  := λ⟨i, hi⟩ => have ⟨_, h⟩ := h i hi; h

theorem List.NWkn_iff (Γ Δ : List α) (ρ : ℕ → ℕ)
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

theorem List.NWkn.id (Γ : List α) : List.NWkn Γ Γ id
  := λ_ hΓ => ⟨hΓ, le_refl _⟩

theorem List.NWkn.len_le {Γ Δ : List α} (h : List.NWkn Γ Δ ρ) (hρ : StrictMono ρ)
  : Δ.length ≤ Γ.length
  := FWkns.len_le ⟨_, h.toFWkn, Fin.wkOfBounded_strictMono hρ⟩

theorem List.NWkn.id_len_le {Γ Δ : List α} (h : List.NWkn Γ Δ _root_.id)
  : Δ.length ≤ Γ.length := h.len_le strictMono_id

theorem List.NWkn.drop_all (Γ : List α) (ρ) : List.NWkn Γ [] ρ
  := λi h => by cases h

theorem List.NWkn.comp {ρ : ℕ → ℕ} {σ : ℕ → ℕ} (hρ : List.NWkn Γ Δ ρ) (hσ : List.NWkn Δ Ξ σ)
  : List.NWkn Γ Ξ (ρ ∘ σ) := λn hΞ =>
    have ⟨hΔ, hσ⟩ := hσ n hΞ;
    have ⟨hΓ, hρ⟩ := hρ _ hΔ;
    ⟨hΓ, le_trans hρ hσ⟩

theorem List.NWkn.lift {ρ : ℕ → ℕ} (hAB : A ≤ B) (hρ : List.NWkn Γ Δ ρ)
  : List.NWkn (A :: Γ) (B :: Δ) (Nat.liftWk ρ) := λn hΔ => match n with
  | 0 => ⟨Nat.zero_lt_succ _, hAB⟩
  | n+1 => have ⟨hΔ, hρ⟩ := hρ n (Nat.lt_of_succ_lt_succ hΔ); ⟨Nat.succ_lt_succ hΔ, hρ⟩

theorem List.NWkn.lift_tail {ρ : ℕ → ℕ} (h : List.NWkn (left :: Γ) (right :: Δ) (Nat.liftWk ρ))
    : List.NWkn Γ Δ ρ
  := λi hΔ => have ⟨hΔ, hρ⟩ := h i.succ (Nat.succ_lt_succ hΔ); ⟨Nat.lt_of_succ_lt_succ hΔ, hρ⟩

theorem List.NWkn.lift_head {ρ : ℕ → ℕ} (h : List.NWkn (left :: Γ) (right :: Δ) (Nat.liftWk ρ))
  : left ≤ right
  := (h 0 (Nat.zero_lt_succ _)).2

theorem List.NWkn.lift_iff (A B) (Γ Δ : List α) (ρ : ℕ → ℕ)
  : List.NWkn (A :: Γ) (B :: Δ) (Nat.liftWk ρ) ↔ A ≤ B ∧ List.NWkn Γ Δ ρ
  := ⟨
    λh => ⟨h.lift_head, List.NWkn.lift_tail h⟩,
    λ⟨hAB, hρ⟩ => List.NWkn.lift hAB hρ
  ⟩

theorem List.NWkn.lift_id (hρ : List.NWkn Γ Δ _root_.id) (h : A ≤ B)
  : List.NWkn (A :: Γ) (B :: Δ) _root_.id := Nat.liftWk_id ▸ hρ.lift h

theorem List.NWkn.lift_id_tail (h : List.NWkn (left :: Γ) (right :: Δ) _root_.id)
    : List.NWkn Γ Δ _root_.id
  := (Nat.liftWk_id ▸ h).lift_tail

theorem List.NWkn.lift_id_head (h : List.NWkn (left :: Γ) (right :: Δ) _root_.id)
  : left ≤ right
  := (Nat.liftWk_id ▸ h).lift_head

theorem List.NWkn.lift_id_iff (h : List.NWkn (left :: Γ) (right :: Δ) _root_.id)
  : left ≤ right ∧ List.NWkn Γ Δ _root_.id
  := ⟨h.lift_id_head, h.lift_id_tail⟩

theorem List.NWkn.lift₂ {ρ : ℕ → ℕ} (hAB₁ : A₁ ≤ B₁) (hAB₂ : A₂ ≤ B₂) (hρ : List.NWkn Γ Δ ρ)
    : List.NWkn (A₁ :: A₂ :: Γ) (B₁ :: B₂ :: Δ) (Nat.liftWk (Nat.liftWk ρ))
  := (hρ.lift hAB₂).lift hAB₁

theorem List.NWkn.liftn₂ {ρ : ℕ → ℕ} (hAB₁ : A₁ ≤ B₁) (hAB₂ : A₂ ≤ B₂) (hρ : List.NWkn Γ Δ ρ)
    : List.NWkn (A₁ :: A₂ :: Γ) (B₁ :: B₂ :: Δ) (Nat.liftnWk 2 ρ)
  := by rw [Nat.liftnWk_eq_iterate_liftWk]; exact lift₂ hAB₁ hAB₂ hρ

theorem List.NWkn.liftn_append {ρ : ℕ → ℕ} (Ξ : List α) (hρ : List.NWkn Γ Δ ρ)
    : List.NWkn (Ξ ++ Γ) (Ξ ++ Δ) (Nat.liftnWk Ξ.length ρ) := by
  induction Ξ with
  | nil => exact hρ
  | cons A Ξ I =>
    rw [List.length, Nat.liftnWk_succ']
    exact I.lift (le_refl _)

theorem List.NWkn.liftn_append' {ρ : ℕ → ℕ} (Ξ : List α) (hΞ : Ξ.length = n) (hρ : List.NWkn Γ Δ ρ)
    : List.NWkn (Ξ ++ Γ) (Ξ ++ Δ) (Nat.liftnWk n ρ)
  := hΞ ▸ hρ.liftn_append Ξ

-- TODO: pointwise liftn

theorem List.NWkn.step {ρ : ℕ → ℕ} (A : α) (hρ : List.NWkn Γ Δ ρ)
    : List.NWkn (A :: Γ) Δ (Nat.succ ∘ ρ)
  := λn hΔ => have ⟨hΔ, hρ⟩ := hρ n hΔ; ⟨Nat.succ_lt_succ hΔ, hρ⟩

theorem List.NWkn.step_tail {ρ : ℕ → ℕ} (h : List.NWkn (A :: Γ) Δ (Nat.succ ∘ ρ)) : List.NWkn Γ Δ ρ
  := λi hΔ => have ⟨hΔ, hρ⟩ := h i hΔ; ⟨Nat.lt_of_succ_lt_succ hΔ, hρ⟩

theorem List.NWkn.step_iff (A) (Γ Δ : List α) (ρ : ℕ → ℕ)
  : List.NWkn (A :: Γ) Δ (Nat.succ ∘ ρ) ↔ List.NWkn Γ Δ ρ
  := ⟨
    List.NWkn.step_tail,
    List.NWkn.step A
  ⟩

theorem List.NWkn.stepn_append {ρ : ℕ → ℕ} (Ξ : List α) (hρ : List.NWkn Γ Δ ρ)
    : List.NWkn (Ξ ++ Γ) Δ (Nat.stepnWk Ξ.length ρ)
  := by induction Ξ with
    | nil => exact hρ
    | cons A Ξ I =>
      rw [List.length, Nat.stepnWk_succ']
      exact I.step _

theorem List.NWkn.stepn_append' {ρ : ℕ → ℕ} (Ξ : List α) (hΞ : Ξ.length = n) (hρ : List.NWkn Γ Δ ρ)
  : List.NWkn (Ξ ++ Γ) Δ (Nat.stepnWk n ρ) := hΞ ▸ hρ.stepn_append Ξ

-- TODO: step₂, stepn₂, stepn

-- TODO: if the order is discrete, weakenings are unique iff there are no duplicates in the source

-- TODO: if the order is discrete and there are no duplicates in the source, then the are none
--       in the target

theorem List.NEWkn.toNWkn (Γ Δ : List α) (ρ : ℕ → ℕ)
  (h : List.NEWkn Γ Δ ρ) : List.NWkn Γ Δ ρ
  := λn hΔ => match h n hΔ with | ⟨hΓ, h⟩ => ⟨hΓ, le_of_eq h⟩

/-- The list Γ has a member compatible with `A` at index `n` -/
def List.FVar (Γ : List α) (n : Fin Γ.length) (A : α) : Prop := Γ.get n ≤ A

theorem List.FVar.le_trg {A A' : α} {n : Fin Γ.length} (h : List.FVar Γ n A) (hA : A ≤ A')
  : List.FVar Γ n A' := le_trans h hA

theorem List.FVar.head_le {A A' : α} (h : A ≤ A') : List.FVar (A :: Γ) ⟨0, by simp⟩ A'
  := h

theorem List.FVar.head (A : α) : List.FVar (A :: Γ) ⟨0, by simp⟩ A := le_refl _

theorem List.FVar.tail (A : α) (h : List.FVar Γ n B) : List.FVar (A :: Γ) n.succ B
  := h

/-- The list Γ has a member compatible with `A` at index `n` -/
structure List.Var (Γ : List α) (n : ℕ) (A : α) : Prop where
  length : n < Γ.length
  get : Γ.FVar ⟨n, length⟩ A

theorem List.Var.le_trg {A A' : α} {n : ℕ} (h : List.Var Γ n A) (hA : A ≤ A') : List.Var Γ n A'
  := ⟨h.length, le_trans h.get hA⟩

theorem List.Var.head_le {A A' : α} (h : A ≤ A') : List.Var (A :: Γ) 0 A'
  := ⟨Nat.zero_lt_succ _, h⟩

theorem List.Var.head (A : α) : List.Var (A :: Γ) 0 A := ⟨Nat.zero_lt_succ _, le_refl _⟩

theorem List.Var.tail (A : α) (h : List.Var Γ n B) : List.Var (A :: Γ) (n+1) B
  := ⟨Nat.succ_lt_succ h.length, h.get⟩

-- TODO: Var.wkn

-- TODO: inductive weakening, associated lore
