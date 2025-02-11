import Discretion.Elgot.Category
import Discretion.Distributive.Category

namespace CategoryTheory

open MonoidalCategory

open Monoidal

open ChosenFiniteCoproducts

variable {C : Type u} [Category C] [MonoidalCategoryStruct C] [ChosenFiniteCoproducts C] [Iterate C]

class IsStrongElgot (C : Type _)
  [Category C] [MonoidalCategoryStruct C] [ChosenFiniteCoproducts C] [Iterate C]
  extends IsPremonoidal C, DistributiveCategory C, Iterate.Conway C : Prop
  where
  iterate_whiskerLeft : ∀ {X Y : C} (Z : C) (f : X ⟶ Y ⊕ₒ X),
    iterate ((Z ◁ f) ≫ inv (δl_ Z Y X)) = Z ◁ iterate f
  iterate_whiskerRight : ∀ {X Y : C} (f : X ⟶ Y ⊕ₒ X) (Z : C),
    iterate ((f ▷ Z) ≫ inv (δr_ Y X Z)) = iterate f ▷ Z

namespace Monoidal

theorem iterate_whiskerLeft [IsStrongElgot C] {X Y : C} (Z : C) (f : X ⟶ Y ⊕ₒ X)
  : iterate ((Z ◁ f) ≫ inv (δl_ Z Y X)) = Z ◁ iterate f
  := IsStrongElgot.iterate_whiskerLeft Z f

theorem iterate_whiskerRight [IsStrongElgot C] {X Y : C} (f : X ⟶ Y ⊕ₒ X) (Z : C)
  : iterate ((f ▷ Z) ≫ inv (δr_ Y X Z)) = iterate f ▷ Z
  := IsStrongElgot.iterate_whiskerRight f Z

end Monoidal
