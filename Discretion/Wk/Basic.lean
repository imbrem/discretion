import Discretion.Wk.Fun
import Mathlib.Data.Fintype.Card

def Fin.FWkn [PartialOrder α] {n m : Nat}
  (Γ : Fin n → α) (Δ : Fin m → α) (ρ : Fin m → Fin n) : Prop
  := (Γ ∘ ρ) ≤ Δ

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

-- TODO: inductive weakening, associated lore
