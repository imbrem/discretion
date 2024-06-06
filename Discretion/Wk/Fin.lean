import Discretion.Wk.Fun

variable [PartialOrder α]

/-- The function `ρ` weakens `Γ` to `Δ` -/
def Fin.FWkn {n m : Nat} (Γ : Fin n → α) (Δ : Fin m → α) (ρ : Fin m → Fin n) : Prop
  := (Γ ∘ ρ) ≤ Δ

theorem Fin.FWkn.id {n : Nat} (Γ : Fin n → α) : Fin.FWkn Γ Γ id := le_refl _

-- theorem Fin.FWkn.comp {ρ : Fin m → Fin n} {σ : Fin o → Fin m}
--   (hρ : Fin.FWkn Γ Δ ρ) (hσ : Fin.FWkn Δ Ξ σ) : Fin.FWkn Γ Ξ (ρ ∘ σ)
--   := λ_ => le_trans (hρ _) (hσ _)
