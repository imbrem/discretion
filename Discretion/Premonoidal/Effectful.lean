import Mathlib.Order.BoundedOrder.Basic

import Discretion.Monoidal.Braided.Basic
import Discretion.Premonoidal.Predicate.Basic
import Discretion.Premonoidal.Property.Braided
import Discretion.Premonoidal.Property.Commutative
import Discretion.Premonoidal.Quant
import Discretion.Premonoidal.BraidedHelpers
import Discretion.EffectSystem.Basic

import Discretion.Poset2.Basic

namespace CategoryTheory

open PremonoidalCategory MonoidalCategory'
open scoped MonoidalCategory

open MorphismProperty

open HasCommRel


class EffectfulCategory
  (C : Type v) [Category C] [PremonoidalCategory C] [BraidedCategory' C]
  (ε : Type u) [EffectSystem ε] where
  eff : ε →o MorphismProperty C
  eff_top : eff ⊤ = ⊤
  eff_monoidal : ∀e, (eff e).IsMonoidal
  eff_braided : ∀e, (eff e).IsBraided
  eff_comm : ∀{e e' : ε}, e ⇌ e' → Commutes (eff e) (eff e')

variable {C : Type v} [Category C] [PremonoidalCategory C] [BraidedCategory' C]
  {ε : Type u} [EffectSystem ε] [EC : EffectfulCategory C ε]

abbrev EffectfulCategory.pure : MorphismProperty C := EC.eff ⊥

class EffectfulCategory.HasEff (e : ε) {X Y : C} (f : X ⟶ Y) : Prop where
  has_eff : EC.eff e f

theorem EffectfulCategory.HasEff.mono {e e' : ε} (h : e ≤ e') {X Y : C} {f : X ⟶ Y}
  [hf : HasEff e f] : HasEff e' f where
  has_eff := EC.eff.monotone' h _ hf.has_eff

theorem EffectfulCategory.HasEff.of_pure {X Y : C} {f : X ⟶ Y} (hf : EC.pure f) : EC.HasEff e f
  := mono bot_le (hf := ⟨hf⟩)

@[simp]
instance EffectfulCategory.HasEff.top {X Y : C} (f : X ⟶ Y) : EC.HasEff ⊤ f where
  has_eff := by rw [EC.eff_top]; trivial

@[simp]
theorem EffectfulCategory.mem_eff_top {X Y : C} {f : X ⟶ Y} : EC.eff ⊤ f
  := by rw [EC.eff_top]; trivial

@[simp]
instance EffectfulCategory.HasEff.id {e : ε} {X : C} : HasEff e (𝟙 X) where
  has_eff := (EC.eff_monoidal e).id_mem X

@[simp]
instance EffectfulCategory.HasEff.eq_hom {e : ε} {X Y : C} (h : X = Y) : HasEff e (eqToHom h)
  := by cases h; exact id

instance EffectfulCategory.HasEff.comp {e : ε} {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)
  [hf : HasEff e f] [hg : HasEff e g] : HasEff e (f ≫ g) where
  has_eff := (EC.eff_monoidal e).comp_mem f g hf.has_eff hg.has_eff

instance EffectfulCategory.HasEff.whiskerRight {e : ε} {X Y Z : C} (f : X ⟶ Y)
  [hf : HasEff e f] : HasEff e (f ▷ Z) where
  has_eff := (EC.eff_monoidal e).whiskerRight_mem f hf.has_eff

instance EffectfulCategory.HasEff.whiskerLeft {e : ε} {X Y Z : C} (f : X ⟶ Y)
  [hf : HasEff e f] : HasEff e (Z ◁ f) where
  has_eff := (EC.eff_monoidal e).whiskerLeft_mem f hf.has_eff

instance EffectfulCategory.HasEff.tensorHom
  {e : ε} {X Y X' Y' : C} (f : X ⟶ Y) (g : X' ⟶ Y')
  [hf : HasEff e f] [hg : HasEff e g] : HasEff e (f ⊗ g) where
  has_eff := have _ := (EC.eff_monoidal e); MorphismProperty.tensorHom_mem hf.has_eff hg.has_eff

@[simp]
instance EffectfulCategory.HasEff.associator_hom {e : ε} {X Y Z : C} : HasEff e (α_ X Y Z).hom where
  has_eff := (EC.eff_monoidal e).associator_hom_mem

@[simp]
instance EffectfulCategory.HasEff.associator_inv {e : ε} {X Y Z : C} : HasEff e (α_ X Y Z).inv where
  has_eff := (EC.eff_monoidal e).associator_inv_mem

@[simp]
instance EffectfulCategory.HasEff.leftUnitor_hom {e : ε} {X : C} : HasEff e (λ_ X).hom where
  has_eff := (EC.eff_monoidal e).leftUnitor_hom_mem

@[simp]
instance EffectfulCategory.HasEff.leftUnitor_inv {e : ε} {X : C} : HasEff e (λ_ X).inv where
  has_eff := (EC.eff_monoidal e).leftUnitor_inv_mem

@[simp]
instance EffectfulCategory.HasEff.rightUnitor_hom {e : ε} {X : C} : HasEff e (ρ_ X).hom where
  has_eff := (EC.eff_monoidal e).rightUnitor_hom_mem

@[simp]
instance EffectfulCategory.HasEff.rightUnitor_inv {e : ε} {X : C} : HasEff e (ρ_ X).inv where
  has_eff := (EC.eff_monoidal e).rightUnitor_inv_mem

@[simp]
instance EffectfulCategory.HasEff.braiding_hom {e : ε} {X Y : C} : HasEff e (β'_ X Y).hom where
  has_eff := (EC.eff_braided e).braiding_hom_mem

@[simp]
instance EffectfulCategory.HasEff.braiding_inv {e : ε} {X Y : C} : HasEff e (β'_ X Y).inv where
  has_eff := (EC.eff_braided e).braiding_inv_mem

@[simp]
instance EffectfulCategory.HasEff.assoc_inner {e : ε} {X Y Z W : C} : HasEff e (αi_ X Y Z W).hom
  := by simp only [MonoidalCategory'.assoc_inner]; infer_instance

@[simp]
instance EffectfulCategory.HasEff.assoc_inner_inv {e : ε} {X Y Z W : C} : HasEff e (αi_ X Y Z W).inv
  := by simp only [MonoidalCategory'.assoc_inner]; infer_instance

@[simp]
instance EffectfulCategory.HasEff.swap_inner {e : ε} {X Y Z W : C} : HasEff e (βi_ X Y Z W).hom
  := by simp only [MonoidalCategory'.swap_inner]; infer_instance

@[simp]
instance EffectfulCategory.HasEff.swap_inner_inv {e : ε} {X Y Z W : C} : HasEff e (βi_ X Y Z W).inv
  := by simp only [MonoidalCategory'.swap_inner]; infer_instance

abbrev EffectfulCategory.IsPure {X Y : C} (f : X ⟶ Y) : Prop := HasEff (ε := ε) ⊥ f

theorem EffectfulCategory.pure_commutes_eff (e : ε) : Commutes (EC.pure) (EC.eff e)
  := EC.eff_comm commutes_bot_left

theorem EffectfulCategory.pure_central : Central (EC.pure)
  := Central.of_commutes_top (h := by convert pure_commutes_eff ⊤; rw [EC.eff_top])

theorem EffectfulCategory.pure_hom_central {f : X ⟶ Y} (h : EC.pure f) : Central f
  := pure_central.central h

theorem EffectfulCategory.HasEff.pure_central (f : X ⟶ Y) [hf : EC.HasEff ⊥ f] : Central f
  := pure_hom_central hf.has_eff

@[reassoc]
theorem EffectfulCategory.eff_comm_exchange
  {X₁ Y₁ X₂ Y₂ : C} {el er : ε} (h : el ⇌ er)
    (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) [hf : EC.HasEff el f] [hg : EC.HasEff er g] :
    f ▷ X₂ ≫ Y₁ ◁ g = X₁ ◁ g ≫ f ▷ Y₂
    := (EC.eff_comm h).left_exchange f g hf.has_eff hg.has_eff

namespace Monoidal
