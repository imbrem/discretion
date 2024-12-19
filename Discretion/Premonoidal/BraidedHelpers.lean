import Discretion.Premonoidal.Braided
import Discretion.Premonoidal.Predicate.Basic
import Discretion.Premonoidal.Property.Braided
import Discretion.Premonoidal.Quant
import Mathlib.CategoryTheory.Monoidal.Subcategory

namespace CategoryTheory

open MonoidalCategory

open Monoidal

namespace Monoidal

variable {C : Type u} [Category C] [MonoidalCategoryStruct C] [BraidedCategoryStruct C]

def swap_inner
  (X Y Z W : C) : (X ⊗ Y) ⊗ (Z ⊗ W) ⟶ (X ⊗ Z) ⊗ (Y ⊗ W)
  := (α_ X Y (Z ⊗ W)).hom
  ≫ X ◁ ((α_ Y Z W).inv
  ≫ σ_ Y Z ▷ W
  ≫ (α_ Z Y W).hom)
  ≫ (α_ X Z (Y ⊗ W)).inv

def swap_inner_inv
  (X Y Z W : C) : (X ⊗ Y) ⊗ (Z ⊗ W) ⟶ (X ⊗ Z) ⊗ (Y ⊗ W)
  := (α_ X Y (Z ⊗ W)).hom
  ≫ X ◁ ((α_ Y Z W).inv
  ≫ (BraidedCategoryStruct.braiding Z Y).inv ▷ W
  ≫ (α_ Z Y W).hom)
  ≫ (α_ X Z (Y ⊗ W)).inv

variable [IsPremonoidal C]

@[simp]
theorem swap_inner_swap_inner_inv
  (X Y Z W : C) : swap_inner X Y Z W ≫ swap_inner_inv X Z Y W = 𝟙 _ := by
  simp only [swap_inner, swap_inner_inv, Category.assoc, Iso.inv_hom_id_assoc]
  apply (cancel_epi (α_ X Y (Z ⊗ W)).inv).mp
  apply (cancel_mono (α_ X Y (Z ⊗ W)).hom).mp
  simp only [Iso.inv_hom_id_assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id, ←
    whiskerLeft_comp, Iso.hom_inv_id_assoc]
  rw [<-Category.assoc _ _ (α_ _ _ _).hom, <-whiskerRight_comp]
  simp

@[simp]
theorem swap_inner_inv_swap_inner
  (X Y Z W : C) : swap_inner_inv X Y Z W ≫ swap_inner X Z Y W = 𝟙 _ := by
  simp only [swap_inner, swap_inner_inv, Category.assoc, Iso.inv_hom_id_assoc]
  apply (cancel_epi (α_ X Y (Z ⊗ W)).inv).mp
  apply (cancel_mono (α_ X Y (Z ⊗ W)).hom).mp
  simp only [Iso.inv_hom_id_assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id, ←
    whiskerLeft_comp, Iso.hom_inv_id_assoc]
  rw [<-Category.assoc _ _ (α_ _ _ _).hom, <-whiskerRight_comp]
  simp

instance IsIso.swap_inner {X Y Z W : C} : IsIso (swap_inner X Y Z W)
  := ⟨_, swap_inner_swap_inner_inv X Y Z W, swap_inner_inv_swap_inner X Z Y W⟩

instance IsIso.swap_inner_inv {X Y Z W : C} : IsIso (swap_inner_inv X Y Z W)
  := ⟨_, swap_inner_inv_swap_inner X Y Z W, swap_inner_swap_inner_inv X Z Y W⟩

variable [IsSymmetric C]

@[simp]
theorem swap_inner_inv_eq_swap_inner
  (X Y Z W : C) : swap_inner_inv X Y Z W = swap_inner X Y Z W := by
  simp [swap_inner, swap_inner_inv]

@[simp]
theorem swap_inner_swap_inner
  (X Y Z W : C) : swap_inner X Y Z W ≫ swap_inner X Z Y W = 𝟙 _
  := by rw [<-swap_inner_inv_eq_swap_inner, swap_inner_inv_swap_inner]

theorem swap_inner_inv_swap_inner_inv
  (X Y Z W : C) : swap_inner_inv X Y Z W ≫ swap_inner_inv X Z Y W = 𝟙 _
  := by simp

end Monoidal
