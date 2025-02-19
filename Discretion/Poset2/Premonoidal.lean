import Discretion.Poset2.Basic
import Discretion.Monoidal.Category

namespace CategoryTheory

open MonoidalCategory

class WhiskerMono (C : Type u) [Category C] [MonoidalCategoryStruct C] [Refines C]
  : Prop where
  whiskerRight_mono : ∀{X Y Z : C} (f g : X ⟶ Y), f ↠ g → (f ▷ Z) ↠ (g ▷ Z)
  whiskerLeft_mono : ∀{X Y Z : C} (f g : Y ⟶ Z), f ↠ g → (X ◁ f) ↠ (X ◁ g)

instance WhiskeringMono.ofDiscrete {C : Type u}
  [Category C] [MonoidalCategoryStruct C] [Poset2 C] [RefinesIsDiscrete C]
  : WhiskerMono C where
  whiskerRight_mono f g ff' := by cases (eq_of_refines ff'); rfl
  whiskerLeft_mono f g ff' := by cases (eq_of_refines ff'); rfl

class MonPoset2 (C : Type u) [Category C] [MonoidalCategoryStruct C]
  extends Poset2 C, WhiskerMono C

instance MonPoset2.instMk {C : Type u} [Category C] [MonoidalCategoryStruct C]
  [Poset2 C] [WhiskerMono C] : MonPoset2 C := ⟨⟩

instance Disc2.instMonoidalCategoryStruct {C : Type u} [Category C]
  [ℳ : MonoidalCategoryStruct C] : MonoidalCategoryStruct (Disc2 C) := ℳ

instance Disc2.instPremonoidalCategory {C : Type u} [Category C] [MonoidalCategoryStruct C]
  [ℳ : PremonoidalCategory C] : PremonoidalCategory (Disc2 C) := ℳ

instance Disc2.instMonoidalCategory {C : Type u} [Category C] [ℳ : MonoidalCategory C]
  : MonoidalCategory (Disc2 C) := ℳ

instance Disc2.instMonoidalCategory' {C : Type u} [Category C] [ℳ : MonoidalCategory' C]
  : MonoidalCategory' (Disc2 C) := ℳ

end CategoryTheory
