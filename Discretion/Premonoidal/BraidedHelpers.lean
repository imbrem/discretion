import Discretion.Monoidal.Braided.Basic
import Discretion.Premonoidal.Predicate.Basic
import Discretion.Premonoidal.Property.Braided
import Discretion.Premonoidal.Quant
import Mathlib.CategoryTheory.Monoidal.Subcategory

namespace CategoryTheory

open scoped MonoidalCategory
open PremonoidalCategory MonoidalCategory'

namespace MonoidalCategory'

variable {C : Type u} [Category C]

section MonoidalCategoryStruct

variable [MonoidalCategoryStruct C]

def assoc_inner_hom
  (X Y Z W : C)
  : (X ⊗ Y) ⊗ (Z ⊗ W) ⟶ X ⊗ (Y ⊗ Z) ⊗ W
  := (α_ X Y (Z ⊗ W)).hom ≫ X ◁ (α_ Y Z W).inv

def assoc_inner_inv
  (X Y Z W : C)
  : X ⊗ (Y ⊗ Z) ⊗ W ⟶ (X ⊗ Y) ⊗ (Z ⊗ W)
  := X ◁ (α_ Y Z W).hom ≫ (α_ X Y (Z ⊗ W)).inv

end MonoidalCategoryStruct

variable [PremonoidalCategory C]

@[simp]
theorem assoc_inner_hom_assoc_inner_inv
  (X Y Z W : C) : assoc_inner_hom X Y Z W ≫ assoc_inner_inv X Y Z W = 𝟙 _ := by
  simp [assoc_inner_hom, assoc_inner_inv, <-whiskerLeft_comp_assoc]

@[simp]
theorem assoc_inner_inv_assoc_inner_hom
  (X Y Z W : C) : assoc_inner_inv X Y Z W ≫ assoc_inner_hom X Y Z W = 𝟙 _ := by
  simp [assoc_inner_hom, assoc_inner_inv, <-whiskerLeft_comp]

@[simp]
instance assoc_inner_hom_central (X Y Z W : C) : Central (assoc_inner_hom X Y Z W) := by
  simp only [assoc_inner_hom]; infer_instance

@[simp]
instance assoc_inner_inv_central (X Y Z W : C) : Central (assoc_inner_inv X Y Z W) := by
  simp only [assoc_inner_inv]; infer_instance

def assoc_inner
  (X Y Z W : C) : (X ⊗ Y) ⊗ (Z ⊗ W) ≅ X ⊗ (Y ⊗ Z) ⊗ W
  := ⟨
    assoc_inner_hom X Y Z W,
    assoc_inner_inv X Y Z W,
    assoc_inner_hom_assoc_inner_inv X Y Z W,
    assoc_inner_inv_assoc_inner_hom X Y Z W
  ⟩

scoped notation "αi_" => assoc_inner

@[simp]
instance assoc_inner_central (X Y Z W : C) : Central (αi_ X Y Z W).hom := by
  simp only [assoc_inner]; infer_instance
section BraidedCategory

variable [BraidedCategory' C]

def swap_inner_hom
  (X Y Z W : C) : (X ⊗ Y) ⊗ (Z ⊗ W) ⟶ (X ⊗ Z) ⊗ (Y ⊗ W)
  := (αi_ X Y Z W).hom
  ≫ X ◁ (β'_ Y Z).hom ▷ W
  ≫ (αi_ X Z Y W).inv

def swap_inner_inv
  (X Y Z W : C) : (X ⊗ Z) ⊗ (Y ⊗ W) ⟶ (X ⊗ Y) ⊗ (Z ⊗ W)
  := (αi_ X Z Y W).hom
  ≫ X ◁ (β'_ Y Z).inv ▷ W
  ≫ (αi_ X Y Z W).inv

@[simp]
instance swap_inner_hom_central (X Y Z W : C) : Central (swap_inner_hom X Y Z W) := by
  simp only [swap_inner_hom]; infer_instance

@[simp]
instance swap_inner_inv_central (X Y Z W : C) : Central (swap_inner_inv X Y Z W) := by
  simp only [swap_inner_inv]; infer_instance

@[simp]
theorem swap_inner_hom_swap_inner_inv
  (X Y Z W : C) : swap_inner_hom X Y Z W ≫ swap_inner_inv X Y Z W = 𝟙 _ := by
  simp only [
    swap_inner_hom, swap_inner_inv, Category.assoc, Iso.inv_hom_id_assoc, assoc_inner_hom,
    assoc_inner_inv, assoc_inner
  ]
  apply (cancel_epi (α_ X Y (Z ⊗ W)).inv).mp
  apply (cancel_mono (α_ X Y (Z ⊗ W)).hom).mp
  simp only [Iso.inv_hom_id_assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id, ←
    whiskerLeft_comp, Iso.hom_inv_id_assoc]
  rw [<-Category.assoc _ _ (α_ _ _ _).hom, <-comp_whiskerRight]
  simp

@[simp]
theorem swap_inner_inv_swap_inner_hom
  (X Y Z W : C) : swap_inner_inv X Y Z W ≫ swap_inner_hom X Y Z W = 𝟙 _ := by
  simp only [
    swap_inner_hom, swap_inner_inv, Category.assoc, Iso.inv_hom_id_assoc, assoc_inner_hom,
    assoc_inner_inv, assoc_inner
  ]
  apply (cancel_epi (α_ X Z (Y ⊗ W)).inv).mp
  apply (cancel_mono (α_ X Z (Y ⊗ W)).hom).mp
  simp only [Iso.inv_hom_id_assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id, ←
    whiskerLeft_comp, Iso.hom_inv_id_assoc]
  rw [<-Category.assoc _ _ (α_ _ _ _).hom, <-comp_whiskerRight]
  simp

def swap_inner
  (X Y Z W : C) : (X ⊗ Y) ⊗ (Z ⊗ W) ≅ (X ⊗ Z) ⊗ (Y ⊗ W)
  := ⟨
    swap_inner_hom X Y Z W,
    swap_inner_inv X Y Z W,
    swap_inner_hom_swap_inner_inv X Y Z W,
    swap_inner_inv_swap_inner_hom X Y Z W
  ⟩

scoped notation "βi_" => swap_inner

@[simp]
instance swap_inner_central (X Y Z W : C) : Central (βi_ X Y Z W).hom := by
  simp only [swap_inner]; infer_instance

theorem assoc_inner_swap_inner
  (X Y Z W : C) :
  (αi_ X Y Z W).inv ≫ (βi_ X Y Z W).hom
  = X ◁ (β'_ Y Z).hom ▷ W ≫ (αi_ X Z Y W).inv := by simp [swap_inner, swap_inner_hom]

theorem assoc_inner_swap_inner_inv
  (X Y Z W : C) :
  (αi_ X Z Y W).inv ≫ (βi_ X Y Z W).inv
  = X ◁ (β'_ Y Z).inv ▷ W ≫ (αi_ X Y Z W).inv := by simp [swap_inner, swap_inner_inv]

theorem swap_inner_assoc_inner
  (X Y Z W : C) :
  (βi_ X Y Z W).hom ≫ (αi_ X Z Y W).hom
  = (αi_ X Y Z W).hom ≫ X ◁ (β'_ Y Z).hom ▷ W := by simp [swap_inner, swap_inner_hom]

theorem swap_inner_inv_assoc_inner
  (X Y Z W : C) :
  (βi_ X Y Z W).inv ≫ (αi_ X Y Z W).hom
  = (αi_ X Z Y W).hom ≫ X ◁ (β'_ Y Z).inv ▷ W := by simp [swap_inner, swap_inner_inv]

--TODO: swap_inner and unitors...

end BraidedCategory

section SymmetricCategory

variable [SymmetricCategory' C]

theorem swap_inner_inv_eq_swap_inner_hom
  (X Y Z W : C) : swap_inner_inv X Z Y W = swap_inner_hom X Y Z W := by
  simp [swap_inner_hom, swap_inner_inv, SymmetricCategory'.braiding_swap_eq_inv_braiding]

@[simp]
theorem swap_inner_hom_swap_inner_hom
  (X Y Z W : C) : swap_inner_hom X Y Z W ≫ swap_inner_hom X Z Y W = 𝟙 _
  := by rw [<-swap_inner_inv_eq_swap_inner_hom, swap_inner_inv_swap_inner_hom]

@[simp]
theorem swap_inner_inv_swap_inner_inv
  (X Y Z W : C) : swap_inner_inv X Y Z W ≫ swap_inner_inv X Z Y W = 𝟙 _
  := by simp [swap_inner_inv_eq_swap_inner_hom]

theorem swap_inner_eq_inv
  (X Y Z W : C) : (βi_ X Y Z W).hom = (βi_ X Z Y W).inv := by
  simp [swap_inner, swap_inner_inv_eq_swap_inner_hom]

theorem swap_inner_swap_inner
  (X Y Z W : C) : (βi_ X Y Z W).hom ≫ (βi_ X Z Y W).hom = 𝟙 _ := by simp [swap_inner]

theorem swap_inner_swap_inner_inv
  (X Y Z W : C) : (βi_ X Y Z W).inv ≫ (βi_ X Z Y W).inv = 𝟙 _ := by simp [swap_inner]

end SymmetricCategory

end MonoidalCategory'

end CategoryTheory
