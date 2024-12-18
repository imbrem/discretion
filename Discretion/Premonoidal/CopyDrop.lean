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

def swap_ll_rr
  (X Y Z W : C) : (X ⊗ Y) ⊗ (Z ⊗ W) ⟶ (X ⊗ Z) ⊗ (Y ⊗ W)
  := (α_ X Y (Z ⊗ W)).hom
  ≫ X ◁ ((α_ Y Z W).inv
  ≫ σ_ Y Z ▷ W
  ≫ (α_ Z Y W).hom)
  ≫ (α_ X Z (Y ⊗ W)).inv

def swap_inv_ll_rr
  (X Y Z W : C) : (X ⊗ Y) ⊗ (Z ⊗ W) ⟶ (X ⊗ Z) ⊗ (Y ⊗ W)
  := (α_ X Y (Z ⊗ W)).hom
  ≫ X ◁ ((α_ Y Z W).inv
  ≫ (BraidedCategoryStruct.braiding Z Y).inv ▷ W
  ≫ (α_ Z Y W).hom)
  ≫ (α_ X Z (Y ⊗ W)).inv

variable [IsPremonoidal C]

@[simp]
theorem swap_ll_rr_swap_inv_ll_rr
  (X Y Z W : C) : swap_ll_rr X Y Z W ≫ swap_inv_ll_rr X Z Y W = 𝟙 _ := by
  simp only [swap_ll_rr, swap_inv_ll_rr, Category.assoc, Iso.inv_hom_id_assoc]
  apply (cancel_epi (α_ X Y (Z ⊗ W)).inv).mp
  apply (cancel_mono (α_ X Y (Z ⊗ W)).hom).mp
  simp only [Iso.inv_hom_id_assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id, ←
    whiskerLeft_comp, Iso.hom_inv_id_assoc]
  rw [<-Category.assoc _ _ (α_ _ _ _).hom, <-whiskerRight_comp]
  simp

@[simp]
theorem swap_inv_ll_rr_swap_ll_rr
  (X Y Z W : C) : swap_inv_ll_rr X Y Z W ≫ swap_ll_rr X Z Y W = 𝟙 _ := by
  simp only [swap_ll_rr, swap_inv_ll_rr, Category.assoc, Iso.inv_hom_id_assoc]
  apply (cancel_epi (α_ X Y (Z ⊗ W)).inv).mp
  apply (cancel_mono (α_ X Y (Z ⊗ W)).hom).mp
  simp only [Iso.inv_hom_id_assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id, ←
    whiskerLeft_comp, Iso.hom_inv_id_assoc]
  rw [<-Category.assoc _ _ (α_ _ _ _).hom, <-whiskerRight_comp]
  simp

instance IsIso.swap_ll_rr {X Y Z W : C} : IsIso (swap_ll_rr X Y Z W)
  := ⟨_, swap_ll_rr_swap_inv_ll_rr X Y Z W, swap_inv_ll_rr_swap_ll_rr X Z Y W⟩

instance IsIso.swap_inv_ll_rr {X Y Z W : C} : IsIso (swap_inv_ll_rr X Y Z W)
  := ⟨_, swap_inv_ll_rr_swap_ll_rr X Y Z W, swap_ll_rr_swap_inv_ll_rr X Z Y W⟩

variable [IsSymmetric C]

@[simp]
theorem swap_inv_ll_rr_eq_swap_ll_rr
  (X Y Z W : C) : swap_inv_ll_rr X Y Z W = swap_ll_rr X Y Z W := by
  simp [swap_ll_rr, swap_inv_ll_rr]

@[simp]
theorem swap_ll_rr_swap_ll_rr
  (X Y Z W : C) : swap_ll_rr X Y Z W ≫ swap_ll_rr X Z Y W = 𝟙 _
  := by rw [<-swap_inv_ll_rr_eq_swap_ll_rr, swap_inv_ll_rr_swap_ll_rr]

theorem swap_inv_ll_rr_swap_inv_ll_rr
  (X Y Z W : C) : swap_inv_ll_rr X Y Z W ≫ swap_inv_ll_rr X Z Y W = 𝟙 _
  := by simp

end Monoidal

class CopyDrop (C : Type u) [Category C] [MonoidalCategoryStruct C] [HasQuant C] where
  copy : ∀ (X : C) [IsRelevant X], (X ⟶ X ⊗ X)
  drop : ∀ (X : C) [IsAffine X], (X ⟶ 𝟙_ C)

namespace Monoidal

scoped notation "Δ_" => CopyDrop.copy

scoped notation "!_" => CopyDrop.drop

end Monoidal

variable {C : Type u} [Category C] [HasQuant C] [MonoidalCategoryStruct C] [CopyDrop C]

class Copyable {X Y : C} (f : X ⟶ Y) where
  copy_hom_ltimes : [IsRelevant X] → [IsRelevant Y] → f ≫ Δ_ Y = Δ_ X ≫ (f ⋉ f)
  copy_hom_rtimes : [IsRelevant X] → [IsRelevant Y] → f ≫ Δ_ Y = Δ_ X ≫ (f ⋊ f)

instance Copyable.id {X : C} [IsPremonoidal C] : Copyable (𝟙 X) := ⟨by simp, by simp⟩

class Droppable {X Y : C} (f : X ⟶ Y) where
  drop_hom : [IsAffine X] → [IsAffine Y] → f ≫ !_ Y = !_ X

instance Droppable.id {X : C} : Droppable (𝟙 X) := ⟨by simp⟩

instance Droppable.comp {X Y Z : C} [IsAffine Y]
  (f : X ⟶ Y) (g : Y ⟶ Z) [Droppable f] [Droppable g] : Droppable (f ≫ g)
  := ⟨by simp [Droppable.drop_hom]⟩

theorem Droppable.comp_of_imp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)
  [Droppable f] [Droppable g] (h : IsAffine X → IsAffine Y) : Droppable (f ≫ g)
  := open Classical in if hX : IsAffine X then
    have _ := h hX; comp f g
  else
    ⟨by simp [hX]⟩

class Discardable {X Y : C} (f : X ⟶ Y) extends Droppable f where
  copy_drop_left_res : [IsRelevant X] → [IsAffine Y] → Δ_ X ≫ (f ≫ !_ Y) ▷ X = (λ_ X).inv

class PureHom {X Y : C} (f : X ⟶ Y) extends Copyable f, Discardable f, Central f : Prop

instance {X Y : C} {f : X ⟶ Y} [Copyable f] [Discardable f] [Central f] : PureHom f := ⟨⟩

namespace Monoidal

theorem copy_hom_ltimes {X Y : C} [IsRelevant X] [IsRelevant Y] (f : X ⟶ Y) [Copyable f]
  : f ≫ Δ_ Y = Δ_ X ≫ (f ⋉ f) := Copyable.copy_hom_ltimes

theorem copy_hom_rtimes {X Y : C} [IsRelevant X] [IsRelevant Y] (f : X ⟶ Y) [Copyable f]
  : f ≫ Δ_ Y = Δ_ X ≫ (f ⋊ f) := Copyable.copy_hom_rtimes

@[simp]
theorem drop_hom {X Y : C} [IsAffine X] [IsAffine Y] (f : X ⟶ Y) [Droppable f]
  : f ≫ !_ Y = !_ X := Droppable.drop_hom

@[simp]
theorem copy_drop_left_res {X Y : C} [IsRelevant X] [IsAffine Y] (f : X ⟶ Y) [Discardable f]
  : Δ_ X ≫ (f ≫ !_ Y) ▷ X = (λ_ X).inv := Discardable.copy_drop_left_res

end Monoidal

open MorphismProperty
