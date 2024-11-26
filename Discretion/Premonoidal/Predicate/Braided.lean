import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Limits.Shapes.Terminal

import Discretion.Premonoidal.Predicate.Basic
import Discretion.Premonoidal.Property.Braided

namespace CategoryTheory

open MonoidalCategory
open Limits
open MorphismProperty

variable {C : Type _} [Category C] [MonoidalCategoryStruct C]

open Monoidal

inductive SymmOps : C → C → Prop where
  | assoc : ∀{X Y Z}, SymmOps (X ⊗ (Y ⊗ Z)) ((X ⊗ Y) ⊗ Z)
  | assoc_inv : ∀{X Y Z}, SymmOps ((X ⊗ Y) ⊗ Z) (X ⊗ (Y ⊗ Z))
  | left_unit : ∀{X}, SymmOps (𝟙_ C ⊗ X) X
  | left_unit_inv : ∀{X}, SymmOps X (𝟙_ C ⊗ X)
  | right_unit : ∀{X}, SymmOps (X ⊗ 𝟙_ C) X
  | right_unit_inv : ∀{X}, SymmOps X (X ⊗ 𝟙_ C)
  | swap : ∀{X Y}, SymmOps (X ⊗ Y) (Y ⊗ X)

theorem SymmOps.symm {X Y : C} (h : SymmOps X Y) : SymmOps Y X := by cases h <;> constructor

instance SymmOps.is_symm : IsSymm C SymmOps where symm _ _ := symm

theorem AssocOps.le_symm : AssocOps (C := C) ≤ SymmOps (C := C)
  := λ _ _ h => by cases h <;> constructor

class SymmEqv (X Y : C) : Prop where
  prop : TensorClosure SymmOps X Y

theorem SymmEqv.refl {X : C} : SymmEqv X X where
  prop := TensorClosure.refl

theorem SymmEqv.symm (X Y : C) [SymmEqv X Y] : SymmEqv Y X where
  prop := SymmEqv.prop.symm

theorem SymmEqv.trans (X Y Z : C) [SymmEqv X Y] [SymmEqv Y Z]
  : SymmEqv X Z where
  prop := SymmEqv.prop.trans (SymmEqv.prop (X := Y) (Y := Z))

instance SymmEqv.of_assoc {X Y : C} [AssocEqv X Y] : SymmEqv X Y where
  prop := AssocEqv.prop.mono AssocOps.le_symm

theorem SymmEqv.assoc {X Y Z : C} : SymmEqv (X ⊗ (Y ⊗ Z)) ((X ⊗ Y) ⊗ Z) := inferInstance

theorem SymmEqv.assoc_inv {X Y Z : C} : SymmEqv ((X ⊗ Y) ⊗ Z) (X ⊗ (Y ⊗ Z)) := inferInstance

theorem SymmEqv.left_unit {X : C} : SymmEqv (𝟙_ C ⊗ X) X := inferInstance

theorem SymmEqv.left_unit_inv {X : C} : SymmEqv X (𝟙_ C ⊗ X) := inferInstance

theorem SymmEqv.right_unit {X : C} : SymmEqv (X ⊗ 𝟙_ C) X := inferInstance

theorem SymmEqv.right_unit_inv {X : C} : SymmEqv X (X ⊗ 𝟙_ C) := inferInstance

instance SymmEqv.swap {X Y : C} : SymmEqv (X ⊗ Y) (Y ⊗ X) := ⟨TensorClosure.base SymmOps.swap⟩

class RespectsSymm (P : C → Prop) : Prop where
  eqv_iff : ∀(X Y : C) [SymmEqv X Y], P X ↔ P Y

instance RespectsSymm.instStrongMonoidalPredicate {P : C → Prop} [StrongMonoidalPredicate P]
  : RespectsSymm P where
  eqv_iff := λX Y ⟨h⟩ => by
    induction h with
    | refl => rfl
    | trans hf hg If Ig => exact (If ⟨hf⟩).trans (Ig ⟨hg⟩)
    | tensor_left hf If => simp [prop_tensor_iff, If ⟨hf⟩]
    | tensor_right hf If => simp [prop_tensor_iff, If ⟨hf⟩]
    | base h => cases h <;> simp only [prop_tensor_iff, prop_id, and_assoc] <;> simp [and_comm]

-- TODO: RespectsSymm ==> RespectsAssoc

-- TODO: RespectsIso ==> RespectsBraid

variable [BraidedCategoryStruct C]
