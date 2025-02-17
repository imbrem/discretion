import Mathlib.Order.BoundedOrder.Basic

import Discretion.Premonoidal.Braided
import Discretion.Premonoidal.Distributive
import Discretion.Premonoidal.Predicate.Basic
import Discretion.Premonoidal.Property.Braided
import Discretion.Premonoidal.Property.Commutative
import Discretion.Premonoidal.Quant
import Discretion.EffectSystem.Basic

import Discretion.Poset2.Basic

namespace CategoryTheory

open MonoidalCategory

open Monoidal

open MorphismProperty

open HasCommRel

class EffectfulCategory
  (C : Type v) [Category C] [MonoidalCategoryStruct C] [BraidedCategoryStruct C]
  (E : Type u) [EffectSystem E] where
  eff : E →o MorphismProperty C
  eff_top : eff ⊤ = ⊤
  eff_monoidal : ∀e, (eff e).IsMonoidal
  eff_braided : ∀e, (eff e).IsBraided
  eff_comm : ∀{e e' : E}, e ⇌ e' → Commutes (eff e) (eff e')

abbrev EffectfulCategory.pure [Category C] [MonoidalCategoryStruct C] [BraidedCategoryStruct C]
  (E : Type u) [EffectSystem E] [EC : EffectfulCategory C E] : MorphismProperty C
  := EC.eff ⊥

variable {C : Type v} [Category C] [MonoidalCategoryStruct C] [BraidedCategoryStruct C]
  {E : Type u} [EffectSystem E] [EC : EffectfulCategory C E]

class EffectfulCategory.HasEff (e : E) {X Y : C} (f : X ⟶ Y) : Prop where
  has_eff : EC.eff e f

theorem EffectfulCategory.HasEff.mono {e e' : E} (h : e ≤ e') {X Y : C} {f : X ⟶ Y}
  [hf : HasEff e f] : HasEff e' f where
  has_eff := EC.eff.monotone' h _ hf.has_eff

instance EffectfulCategory.HasEff.id (e : E) {X : C} : HasEff e (𝟙 X) where
  has_eff := (EC.eff_monoidal e).id_mem X

instance EffectfulCategory.HasEff.comp {e : E} {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)
  [hf : HasEff e f] [hg : HasEff e g] : HasEff e (f ≫ g) where
  has_eff := (EC.eff_monoidal e).comp_mem f g hf.has_eff hg.has_eff

instance EffectfulCategory.HasEff.whiskerRight {e : E} {X Y Z : C} (f : X ⟶ Y)
  [hf : HasEff e f] : HasEff e (f ▷ Z) where
  has_eff := (EC.eff_monoidal e).whiskerRight_mem f hf.has_eff

instance EffectfulCategory.HasEff.whiskerLeft {e : E} {X Y Z : C} (f : X ⟶ Y)
  [hf : HasEff e f] : HasEff e (Z ◁ f) where
  has_eff := (EC.eff_monoidal e).whiskerLeft_mem f hf.has_eff

instance EffectfulCategory.HasEff.tensorHom [IsBinoidal C]
  {e : E} {X Y X' Y' : C} (f : X ⟶ Y) (g : X' ⟶ Y')
  [hf : HasEff e f] [hg : HasEff e g] : HasEff e (f ⊗ g) where
  has_eff := have _ := (EC.eff_monoidal e); MorphismProperty.tensorHom_mem hf.has_eff hg.has_eff

instance EffectfulCategory.HasEff.associator_hom {e : E} {X Y Z : C} : HasEff e (α_ X Y Z).hom where
  has_eff := (EC.eff_monoidal e).associator_hom_mem

instance EffectfulCategory.HasEff.associator_inv {e : E} {X Y Z : C} : HasEff e (α_ X Y Z).inv where
  has_eff := (EC.eff_monoidal e).associator_inv_mem

instance EffectfulCategory.HasEff.leftUnitor_hom {e : E} {X : C} : HasEff e (λ_ X).hom where
  has_eff := (EC.eff_monoidal e).leftUnitor_hom_mem

instance EffectfulCategory.HasEff.leftUnitor_inv {e : E} {X : C} : HasEff e (λ_ X).inv where
  has_eff := (EC.eff_monoidal e).leftUnitor_inv_mem

instance EffectfulCategory.HasEff.rightUnitor_hom {e : E} {X : C} : HasEff e (ρ_ X).hom where
  has_eff := (EC.eff_monoidal e).rightUnitor_hom_mem

instance EffectfulCategory.HasEff.rightUnitor_inv {e : E} {X : C} : HasEff e (ρ_ X).inv where
  has_eff := (EC.eff_monoidal e).rightUnitor_inv_mem

instance EffectfulCategory.HasEff.braiding_hom {e : E} {X Y : C} : HasEff e (σ_ X Y) where
  has_eff := (EC.eff_braided e).braiding_hom_mem

abbrev EffectfulCategory.IsPure {X Y : C} (f : X ⟶ Y) : Prop := HasEff (E := E) ⊥ f

namespace Monoidal
