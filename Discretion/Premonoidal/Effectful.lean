import Mathlib.Order.BoundedOrder.Basic

import Discretion.Premonoidal.Braided
import Discretion.Premonoidal.Distributive
import Discretion.Premonoidal.Predicate.Basic
import Discretion.Premonoidal.Property.Braided
import Discretion.Premonoidal.Property.Commutative

namespace CategoryTheory

open MonoidalCategory

open Monoidal

open MorphismProperty

-- TODO: EffectSystem ==> EffectfulCategory; then EffectSystem is purely an algebra on E?

class EffectSystem
  (C : Type v) [Category C] [MonoidalCategoryStruct C] [BraidedCategoryStruct C]
  (E : Type u) [PartialOrder E] [BoundedOrder E]
  : Type _ where
  eff : E →o MorphismProperty C
  eff_top : eff ⊤ = ⊤
  eff_braided : ∀e, (eff e).IsBraided
  commutes : E → E → Prop
  commutes_symm : ∀e₁ e₂, commutes e₁ e₂ → commutes e₂ e₁
  commutes_anti_right : ∀e₁ e₂ e₂', e₂ ≤ e₂' → commutes e₁ e₂' → commutes e₁ e₂
  central_bot : commutes ⊥ ⊤
  eff_commutes : ∀e₁ e₂, commutes e₁ e₂ → Commutes (eff e₁) (eff e₂)

attribute [simp] EffectSystem.eff_top

namespace EffectSystem

variable
  (C : Type v)
  [Category C] [MonoidalCategoryStruct C] [BraidedCategoryStruct C]
  {E : Type u} [PartialOrder E] [BoundedOrder E]
  [EffectSystem C E]

-- TODO: make typeclasses?

class Commutes (e₁ e₂ : E) : Prop where
  prop : commutes C e₁ e₂

abbrev Commutative (e : E) : Prop := Commutes C e e

abbrev Central (e : E) : Prop := Commutes C e ⊤

end EffectSystem

namespace EffectSystem

variable
  {C : Type v}
  [Category C] [MonoidalCategoryStruct C] [BraidedCategoryStruct C]
  {E : Type u} [PartialOrder E] [BoundedOrder E]
  [S : EffectSystem C E]

theorem Commutes.symm {e₁ e₂ : E} [h : Commutes C e₁ e₂] : Commutes C e₂ e₁
  := ⟨commutes_symm _ _ h.prop⟩

theorem commutes_anti_left (e₁ e₁' e₂ : E) (h : e₁ ≤ e₁') (h' : commutes C e₁' e₂)
  : commutes C e₁ e₂ := commutes_symm _ _ (commutes_anti_right _ _ _ h (commutes_symm _ _ h'))

theorem commutes_anti (e₁ e₁' e₂ e₂' : E) (h₁ : e₁ ≤ e₁') (h₂ : e₂ ≤ e₂') (h : commutes C e₁' e₂')
  : commutes C e₁ e₂ := commutes_anti_right _ _ _ h₂ (commutes_anti_left _ _ _ h₁ h)

theorem Commutes.anti {e₁ e₁' e₂ e₂' : E} [h : Commutes C e₁' e₂'] (h₁ : e₁ ≤ e₁') (h₂ : e₂ ≤ e₂')
  : Commutes C e₁ e₂ := ⟨commutes_anti _ _ _ _ h₁ h₂ h.prop⟩

instance Commutes.central_left {e₁ e₂ : E} [h : Central C e₁] : Commutes C e₁ e₂
  := anti (h := h) (le_refl _) (by simp)

instance Commutes.central_right {e₁ e₂ : E} [h : Central C e₂] : Commutes C e₁ e₂
  := symm

theorem Commutative.anti {e e' : E} (h' : e ≤ e') [h : Commutative C e']  : Commutative C e
  := Commutes.anti h' h'

theorem Central.anti {e e' : E} (h' : e ≤ e') [h : Central C e'] : Central C e
  := Commutes.anti h' (le_refl _)

instance Central.bot : Central C (⊥ : E) := ⟨central_bot⟩

instance instIsBraidedEff {e : E} : (S.eff e).IsBraided := eff_braided e

-- TODO: commutes instance; merge central and commutes for MorphismProperty?

instance Central.eff_central {e : E} [h : Central C e] : (S.eff e).Central
  := Central.of_commutes_top (h := by convert eff_commutes _ _ h.prop; rw [eff_top])

-- TODO: Singleton E ==> IsMonoidal C (since Central (eff ⊤ = ⊤))

end EffectSystem

namespace Monoidal
