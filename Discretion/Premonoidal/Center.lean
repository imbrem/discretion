import Discretion.Premonoidal.Category
import Discretion.Premonoidal.Property

namespace CategoryTheory

namespace MorphismProperty

open Monoidal

def center (C) [Category C] [MonoidalCategoryStruct C] : MorphismProperty C
  := λ_ _  f => Monoidal.Central f

variable {C} [Category C] [MonoidalCategoryStruct C]

class Central (W : MorphismProperty C) : Prop where
  central {X Y : C} {f : X ⟶ Y} : W f → Monoidal.Central f

instance Central.instCenter : Central (center C) where
  central hf := hf

section IsPremonoidal

variable [IsPremonoidal C]

theorem StableUnderInverse.center : StableUnderInverse (center C)
  := λ_ _ _ hf => Monoidal.Central.inv_hom (hf := hf)

theorem IsStableUnderInverse.instCenter : IsStableUnderInverse (center C) where
  stable_under_inverse := StableUnderInverse.center

instance ContainsMonoidal.instCenter : ContainsMonoidal (center C) where
  id_mem _ := Monoidal.Central.id
  comp_mem _ _ hf hg := Monoidal.Central.comp (hf := hf) (hg := hg)
  whiskerLeft_mem _ hf := Monoidal.Central.whiskerLeft (hf := hf)
  whiskerRight_mem _ hf := Monoidal.Central.whiskerRight (hf := hf)
  associator_hom_mem := associator_central
  associator_inv_mem := associator_inv_central
  leftUnitor_hom_mem := leftUnitor_central
  leftUnitor_inv_mem := leftUnitor_inv_central
  rightUnitor_hom_mem := rightUnitor_central
  rightUnitor_inv_mem := rightUnitor_inv_central

section IsBraided

variable [BraidedCategoryStruct C] [IsBraided C]

instance ContainsBraidings.instCenter
  [BraidedCategoryStruct C] [IsBraided C] : ContainsBraidings (center C) where
  braiding_hom_mem := braiding_central
  braiding_inv_mem := braiding_inv_central

end IsBraided

end IsPremonoidal
