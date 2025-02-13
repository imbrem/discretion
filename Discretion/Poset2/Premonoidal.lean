import Discretion.Poset2.Basic
import Discretion.Premonoidal.Category

namespace CategoryTheory

open MonoidalCategory

class WhiskerMono (C : Type u) [Category C] [MonoidalCategoryStruct C] [∀X Y : C, LE (X ⟶ Y)]
  : Prop where
  whiskerRight_mono : ∀{X Y Z : C} (f g : X ⟶ Y), f ≤ g → (f ▷ Z) ≤ (g ▷ Z)
  whiskerLeft_mono : ∀{X Y Z : C} (f g : Y ⟶ Z), f ≤ g → (X ◁ f) ≤ (X ◁ g)

instance Disc2.instMonoidalCategoryStruct {C : Type u} [Category C]
  [ℳ : MonoidalCategoryStruct C] : MonoidalCategoryStruct (Disc2 C) := ℳ

instance Disc2.instWhiskeringMono {C : Type u} [Category C] [MonoidalCategoryStruct C]
  : WhiskerMono (Disc2 C) where
  whiskerRight_mono f g fg := by cases fg; rfl
  whiskerLeft_mono f g fg := by cases fg; rfl

instance Disc2.instIsPremonoidal {C : Type u} [Category C] [MonoidalCategoryStruct C]
  [H : IsPremonoidal C] : IsPremonoidal (Disc2 C) := H

instance Disc2.instIsMonoidal {C : Type u} [Category C] [MonoidalCategoryStruct C]
  [H : IsMonoidal C] : IsMonoidal (Disc2 C) := H

instance Disc2.instMonoidalCategory {C : Type u} [Category C] [ℳ : MonoidalCategory C]
  : MonoidalCategory (Disc2 C) := ℳ

end CategoryTheory
