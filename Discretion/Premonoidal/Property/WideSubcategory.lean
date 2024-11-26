import Discretion.Premonoidal.Property.Basic
import Discretion.Premonoidal.Property.Braided
import Mathlib.CategoryTheory.Widesubcategory

namespace CategoryTheory

variable {C : Type u} [Category C]

@[ext]
theorem WideSubcategory.hom_ext {W : MorphismProperty C} [W.IsMultiplicative]
  {X Y : WideSubcategory W} (f g : X ⟶ Y)
  (h : f.val = g.val) : f = g := by cases f; cases g; cases h; rfl

variable [MonoidalCategoryStruct C] [IsPremonoidal C]

open MonoidalCategory

open Monoidal

open MorphismProperty

instance WideSubcategory.monoidalCategoryStruct (W : MorphismProperty C) [W.IsMonoidal]
  : MonoidalCategoryStruct (WideSubcategory W) where
  tensorObj X Y := ⟨X.obj ⊗ Y.obj⟩
  whiskerLeft Z X Y f := ⟨Z.obj ◁ f.val, whiskerLeft_mem f.prop⟩
  whiskerRight f Z := ⟨f.val ▷ Z.obj, whiskerRight_mem f.prop⟩
  tensorHom f g := ⟨f.val ⊗ g.val, tensorHom_mem f.prop g.prop⟩
  tensorUnit := ⟨𝟙_ C⟩
  associator X Y Z := ⟨
      ⟨(α_ _ _ _).hom, associator_hom_mem⟩, ⟨(α_ _ _ _).inv, associator_inv_mem⟩,
      by ext; simp, by ext; simp
    ⟩
  leftUnitor X := ⟨
      ⟨(λ_ _).hom, leftUnitor_hom_mem⟩, ⟨(λ_ _).inv, leftUnitor_inv_mem⟩,
      by ext; simp, by ext; simp
    ⟩
  rightUnitor X := ⟨
      ⟨(ρ_ _).hom, rightUnitor_hom_mem⟩, ⟨(ρ_ _).inv, rightUnitor_inv_mem⟩,
      by ext; simp, by ext; simp
    ⟩

-- TODO: WideSubcategory is in and of itself monoidal

-- TODO: WideSubcategory also inherits braidedness
