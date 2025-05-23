import Discretion.Elgot.Iterate
import Discretion.Distributive.Category

namespace CategoryTheory

open scoped MonoidalCategory

open MonoidalCategory' DistributiveCategory

open ChosenFiniteCoproducts

variable {C : Type u} [Category C] [MonoidalCategoryStruct C] [ChosenFiniteCoproducts C]
                      [DistributiveCategory C] [Iterate C]

class Iterate.Strong (C : Type _)
  [Category C] [MonoidalCategoryStruct C] [ChosenFiniteCoproducts C] [DistributiveCategory C]
  [Iterate C] : Prop extends Iterate.Conway C
  where
  iterate_whiskerLeft : ∀ {X Y : C} (Z : C) (f : X ⟶ Y ⊕ₒ X),
    iterate ((Z ◁ f) ≫ (∂L Z Y X).inv) = Z ◁ iterate f
  iterate_whiskerRight : ∀ {X Y : C} (f : X ⟶ Y ⊕ₒ X) (Z : C),
    iterate ((f ▷ Z) ≫ (∂R Y X Z).inv) = iterate f ▷ Z

namespace Monoidal

theorem iterate_whiskerLeft [Iterate.Strong C] {X Y : C} (Z : C) (f : X ⟶ Y ⊕ₒ X)
  : iterate ((Z ◁ f) ≫ (∂L Z Y X).inv) = Z ◁ iterate f
  := Iterate.Strong.iterate_whiskerLeft Z f

theorem iterate_whiskerRight [Iterate.Strong C] {X Y : C} (f : X ⟶ Y ⊕ₒ X) (Z : C)
  : iterate ((f ▷ Z) ≫ (∂R Y X Z).inv) = iterate f ▷ Z
  := Iterate.Strong.iterate_whiskerRight f Z

end Monoidal
