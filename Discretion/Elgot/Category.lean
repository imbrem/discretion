import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts

import Discretion.MorphismProperty.BinaryProducts

namespace CategoryTheory

open Limits

class CoprodFix (C : Type u) [Category C] [HasBinaryCoproducts C] where
  iterate {X Y : C} : (X ⟶ Y ⨿ X) → (X ⟶ Y)
  fixpoint {X Y : C} {f : X ⟶ Y ⨿ X}
    : f ≫ coprod.desc (𝟙 Y) (iterate f) = iterate f

class CoprodFix.Uniform (C : Type u) [Category C] [HasBinaryCoproducts C] [CoprodFix C]
  (W : MorphismProperty C) : Prop where
  uniform {X Y : C} {f : Y ⟶ Z ⨿ Y} {g : X ⟶ Z ⨿ X} {h : X ⟶ Y}
    : W h → h ≫ f = g ≫ coprod.map (𝟙 Z) h → h ≫ iterate f = iterate g

class CoprodFix.Conway (C : Type u) [Category C] [HasBinaryCoproducts C] [CoprodFix C] : Prop
  where
  naturality {X Y Z : C} {f : X ⟶ Y ⨿ X} {g : Y ⟶ Z}
    : iterate (f ≫ coprod.map g (𝟙 X)) = (iterate f) ≫ g
  dinaturality {X Y Z : C} {f : X ⟶ Y ⨿ Z} {g : Z ⟶ Y ⨿ X}
    : f ≫ coprod.desc (𝟙 Y) (iterate (g ≫ coprod.desc coprod.inl f))
      = iterate (f ≫ coprod.desc coprod.inl g)
  codiag {X Y : C} {f : X ⟶ (Y ⨿ X) ⨿ X}
    : iterate (iterate f) = iterate (f ≫ coprod.desc (𝟙 (Y ⨿ X)) coprod.inr)

-- theorem CoprodFix.Uniform.toConway {C : Type u} [Category C] [HasBinaryCoproducts C] [CoprodFix C]
--   {W : MorphismProperty C} [W.PreservedByCoprod] [CoprodFix.Uniform C W]
--   (naturality : ∀{X Y Z : C} {f : X ⟶ Y ⨿ X} {g : Y ⟶ Z},
--     iterate (f ≫ coprod.map g (𝟙 X)) = (iterate f) ≫ g)
--   (codiag : ∀{X Y : C} {f : X ⟶ (Y ⨿ X) ⨿ X},
--     iterate (iterate f) = iterate (f ≫ coprod.desc (𝟙 (Y ⨿ X)) coprod.inr))
--   : CoprodFix.Conway C where
--   naturality := naturality
--   codiag := codiag
--   dinaturality := sorry

end CategoryTheory
