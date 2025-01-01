import Mathlib.CategoryTheory.Monoidal.Category
import Discretion.Utils.Category

namespace CategoryTheory

class CompMonotone (C : Type u) [CategoryStruct C] [∀X Y : C, LE (X ⟶ Y)] : Prop where
  comp_mono_right : ∀{X Y Z : C} (f : X ⟶ Y) (g h : Y ⟶ Z), g ≤ h → (f ≫ g) ≤ (f ≫ h)
  comp_mono_left : ∀{X Y Z : C} (f g : X ⟶ Y) (h : Y ⟶ Z), f ≤ g → (f ≫ h) ≤ (g ≫ h)

open MonoidalCategory

class WhiskeringMonotone (C : Type u) [Category C] [MonoidalCategoryStruct C] [∀X Y : C, LE (X ⟶ Y)]
  : Prop where
  whiskerRight_mono : ∀{X Y Z : C} (f g : X ⟶ Y), f ≤ g → (f ▷ Z) ≤ (g ▷ Z)
  whiskerLeft_mono : ∀{X Y Z : C} (f g : Y ⟶ Z), f ≤ g → (X ◁ f) ≤ (X ◁ g)

-- TODO:  the Kleisli category of an ordered monad is
