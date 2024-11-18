import Discretion.Premonoidal.Category
import Discretion.MorphismProperty.Basic

namespace CategoryTheory

namespace MorphismProperty

def center (C) [Category C] [MonoidalCategoryStruct C] : MorphismProperty C
  := λ_ _  f => Monoidal.Central f

variable {C} [Category C] [MonoidalCategoryStruct C]

class Central (W : MorphismProperty C) : Prop where
  central {X Y : C} {f : X ⟶ Y} : W f → Monoidal.Central f

instance Central.instCenter : Central (center C) where
  central hf := hf

variable [IsPremonoidal C]

instance IsMultiplicative.instCenter : IsMultiplicative (center C) where
  id_mem _ := Monoidal.Central.id
  comp_mem _ _ hf hg := Monoidal.Central.comp (hf := hf) (hg := hg)

theorem StableUnderInverse.center : StableUnderInverse (center C)
  := λ_ _ _ hf => Monoidal.Central.inv_hom (hf := hf)

theorem IsStableUnderInverse.instCenter : IsStableUnderInverse (center C) where
  stable_under_inverse := StableUnderInverse.center
