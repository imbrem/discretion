import Discretion.Premonoidal.Property.Basic
import Discretion.Premonoidal.Property.WideSubcategory
import Discretion.Premonoidal.Distributive
import Discretion.MorphismProperty.BinaryProducts

namespace CategoryTheory.MorphismProperty

open Limits

open MonoidalCategory

open Monoidal

variable {C} [Category C] [MonoidalCategoryStruct C]

section HasBinaryCoproducts

variable [HasBinaryCoproducts C]

theorem distl_mem {W : MorphismProperty C}
  [ContainsInjections W] [ContainsCoprodDesc W]
  [IsStableUnderWhisker W] [IsStableUnderComposition W]
  {X Y Z : C} : W (δl_ X Y Z)
  := coprod_desc_mem (whiskerLeft_mem inl_mem) (whiskerLeft_mem inr_mem)

theorem distr_mem {W : MorphismProperty C}
  [ContainsInjections W] [ContainsCoprodDesc W]
  [IsStableUnderWhisker W] [IsStableUnderComposition W]
  {X Y Z : C} : W (δr_ X Y Z)
  := coprod_desc_mem (whiskerRight_mem inl_mem) (whiskerRight_mem inr_mem)

end HasBinaryCoproducts

variable [CategoryTheory.IsDistributive C]

class IsDistributive (W : MorphismProperty C)
  extends IsMonoidal W, ContainsCoproducts W : Type _ where
  distl_inv_mem : ∀{X Y Z : C}, W (inv (δl_ X Y Z))
  distr_inv_mem : ∀{X Y Z : C}, W (inv (δr_ X Y Z))

variable [CategoryTheory.IsPremonoidal C] {W : MorphismProperty C} [IsDistributive W]

-- NOTE: this doesn't work since we require closure for chosen coproducts, rather than arbitrary
-- ones...
-- OPTION 1: change distl to work over arbitrary coproducts, as well as changing e.g. IsDistributive
-- OPTION 2: change monoidal structure to fix some coproducts...
-- instance IsDistributive.has_distributors : HasDistributors (WideSubcategory W) where
--   left_iso {X Y Z} :=
--     have h := IsIso.instDistl (C := C) (X := X.obj) (Y := Y.obj) (Z := Z.obj);
--     ⟨⟨inv (I := sorry) (δl_ X.obj Y.obj Z.obj), sorry⟩, sorry, sorry⟩
--   right_iso := sorry
--   has_colimit := sorry
