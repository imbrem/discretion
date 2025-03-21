import Mathlib.CategoryTheory.Category.Basic
import Discretion.Utils.OrderUnbundled
import Discretion.Order.Basic

namespace CategoryTheory

class Refines (C : Type u) [Quiver C] where
  refines : ∀{X Y : C}, (X ⟶ Y) → (X ⟶ Y) → Prop

infix:50 " ↠ "  => Refines.refines

infix:50 " ↞ " => (λf g => g ↠ f)

class CompMono (C : Type u) [CategoryStruct C] [Refines C] : Prop where
  refines_comp : ∀{X Y Z : C} {f f' : X ⟶ Y} {g g' : Y ⟶ Z}, f ↠ f' → g ↠ g' → f ≫ g ↠ f' ≫ g'

export CompMono (refines_comp)

class RefinesIsDiscrete (C : Type u) [Quiver C] [Refines C] : Prop where
  eq_of_refines {X Y : C} {f g : X ⟶ Y} : f ↠ g -> f = g

export RefinesIsDiscrete (eq_of_refines)

class RefinesIsPreorder (C : Type u) [Quiver C] [Refines C] : Prop where
  refines_is_preorder : ∀{X Y : C}, IsPreorder (X ⟶ Y) Refines.refines

@[simp, refl]
theorem refines_refl {C : Type u} [Quiver C] [Refines C] [RefinesIsPreorder C]
  {X Y : C} (f : X ⟶ Y) : f ↠ f := RefinesIsPreorder.refines_is_preorder.refl f

@[simp]
theorem refines_of_eq {C : Type u} [Quiver C] [Refines C] [RefinesIsPreorder C]
  {X Y : C} {f g : X ⟶ Y} (h : f = g) : f ↠ g := by cases h; rfl

theorem refines_trans {C : Type u} [Quiver C] [Refines C] [RefinesIsPreorder C]
  {X Y : C} {f g h : X ⟶ Y} : f ↠ g -> g ↠ h -> f ↠ h
  := RefinesIsPreorder.refines_is_preorder.trans f g h

instance Refines.instTrans {C : Type u} [Quiver C] [Refines C] [RefinesIsPreorder C] {X Y : C}
  : Trans (α := X ⟶ Y) (· ↠ ·) (· ↠ ·) (· ↠ ·) where trans := refines_trans

class RefinesIsPartialOrder (C : Type u) [Quiver C] [Refines C] : Prop extends RefinesIsPreorder C
  where
  refines_is_partial_order : ∀{X Y : C}, IsPartialOrder (X ⟶ Y) Refines.refines
  refines_is_preorder := refines_is_partial_order.toIsPreorder

theorem refines_antisymm {C : Type u} [Quiver C] [Refines C] [RefinesIsPartialOrder C]
  {X Y : C} {f g : X ⟶ Y} : f ↠ g -> g ↠ f -> f = g
  := RefinesIsPartialOrder.refines_is_partial_order.antisymm f g

class Poset2 (C : Type u) [CategoryStruct C]
  extends Refines C, CompMono C, RefinesIsPartialOrder C

instance Poset2.instMk {C : Type u}
  [CategoryStruct C] [Refines C] [CompMono C] [RefinesIsPartialOrder C]
  : Poset2 C := ⟨⟩

def Disc2 (C : Type u) := C

instance Disc2.instQuiver {C : Type u} [𝒞 : Quiver C] : Quiver (Disc2 C)
  := 𝒞

instance Disc2.instRefines {C : Type u} [𝒞 : Quiver C] : Refines (Disc2 C) where
  refines := (· = ·)

instance Disc2.instDiscreteRefines {C : Type u} [𝒞 : Quiver C] : RefinesIsDiscrete (Disc2 C)
  where
  eq_of_refines h := h

instance Disc2.instCategoryStruct {C : Type u} [𝒞 : CategoryStruct C] : CategoryStruct (Disc2 C)
  := 𝒞

instance Disc2.instCategory {C : Type u} [𝒞 : Category C] : Category (Disc2 C)
  := 𝒞

instance CompMono.ofDiscrete {C : Type u}
  [CategoryStruct C] [Refines C] [RefinesIsDiscrete C] [RefinesIsPreorder C]
  : CompMono C where
  refines_comp h h' := by cases (eq_of_refines h); cases (eq_of_refines h'); rfl

end CategoryTheory
