import Mathlib.CategoryTheory.Category.Basic
import Discretion.Order.Basic

namespace CategoryTheory

class CompMono (C : Type u) [CategoryStruct C] [∀X Y : C, LE (X ⟶ Y)] : Prop where
  comp_mono_right : ∀{X Y Z : C} (f : X ⟶ Y) (g h : Y ⟶ Z), g ≤ h → (f ≫ g) ≤ (f ≫ h)
  comp_mono_left : ∀{X Y Z : C} (f g : X ⟶ Y) (h : Y ⟶ Z), f ≤ g → (f ≫ h) ≤ (g ≫ h)

def Disc2 (C : Type u) := C

instance Disc2.instQuiver {C : Type u} [𝒞 : Quiver C] : Quiver (Disc2 C) := 𝒞

instance Disc2.instPartialOrderHom {C : Type u} [𝒞 : Quiver C] {X Y : C} : PartialOrder (X ⟶ Y)
  := DiscretePartialOrder _

instance Disc2.instCategoryStruct {C : Type u} [𝒞 : CategoryStruct C]
  : CategoryStruct (Disc2 C) := 𝒞

instance Disc2.instCompMono {C : Type u} [CategoryStruct C]
  : CompMono (Disc2 C) where
  comp_mono_right f g h hgh := by cases hgh; rfl
  comp_mono_left f g h fgh := by cases fgh; rfl

instance Disc2.instCategory {C : Type u} [𝒞 : Category C] : Category (Disc2 C) := 𝒞

structure Poset2 (C : Type u) [Quiver C] (_O : ∀X Y : C, LE (X ⟶ Y)) where
  obj : C

instance Poset2.instQuiver {C : Type u} [Quiver C] {O : ∀X Y : C, LE (X ⟶ Y)}
  : Quiver (Poset2 C O) where Hom := λX Y => X.obj ⟶ Y.obj

instance Poset2.instLEHom {C : Type u} [Quiver C] {O : ∀X Y : C, LE (X ⟶ Y)} {X Y : Poset2 C O}
  : LE (X ⟶ Y) := O X.obj Y.obj

instance Poset2.instCategoryStruct {C : Type u} [𝒞 : CategoryStruct C] {O : ∀X Y : C, LE (X ⟶ Y)}
  : CategoryStruct (Poset2 C O) where
  id X := 𝟙 X.obj
  comp := 𝒞.comp

-- NOTE: this does _not_ necessarily satisfy `CompMono`; you need to prove that for your given `O`

end CategoryTheory
