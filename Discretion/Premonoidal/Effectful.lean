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

class EffectSystem
  (C : Type v) [Category C] [MonoidalCategoryStruct C] [BraidedCategoryStruct C]
  (E : Type u) [PartialOrder E] [BoundedOrder E]
  : Type _ where
  eff : E →o MorphismProperty C
  eff_top : eff ⊤ = ⊤
  -- TODO: merge to IsBraided or smt?
  eff_monoidal : ∀e, (eff e).IsMonoidal
  eff_braided : ∀e, (eff e).ContainsBraidings
  commutes : E → E → Prop
  commutes_symm : ∀e₁ e₂, commutes e₁ e₂ ↔ commutes e₂ e₁
  commutes_mono : ∀e₁ e₂ e₂', e₂ ≤ e₂' → commutes e₁ e₂' → commutes e₁ e₂
  commutes_bot : ∀e, commutes ⊥ e
  eff_commutes : ∀e₁ e₂, commutes e₁ e₂ → Commutes (eff e₁) (eff e₂)

attribute [simp] EffectSystem.eff_top

namespace EffectSystem

variable
  (C : Type v)
  [Category C] [MonoidalCategoryStruct C] [BraidedCategoryStruct C]
  {E : Type u} [PartialOrder E] [BoundedOrder E]
  [EffectSystem C E]

-- TODO: make typeclasses?

abbrev commutative (e : E) : Prop := commutes C e e

abbrev central (e : E) : Prop := commutes C e ⊤

theorem eff_central_central {e : E} (h : central C e) : (eff (C := C) e).Central
  := Central.of_commutes_top (h := by convert eff_commutes _ _ h; rw [eff_top])

instance eff_bot_central : (eff (C := C) (E := E) ⊥).Central
  := eff_central_central C (commutes_bot ⊤)

end EffectSystem

namespace Monoidal
