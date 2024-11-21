import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Limits.Shapes.Terminal

import Discretion.Premonoidal.Predicate.Basic
import Discretion.Premonoidal.Property.Braided

namespace CategoryTheory

open MonoidalCategory
open Limits
open MorphismProperty

variable {C : Type _} [Category C] [MonoidalCategoryStruct C] [BraidedCategoryStruct C]

open Monoidal

inductive SymmOps : C → C → Prop where
  | assoc : ∀{X Y Z}, SymmOps (X ⊗ (Y ⊗ Z)) ((X ⊗ Y) ⊗ Z)
  | assoc_inv : ∀{X Y Z}, SymmOps ((X ⊗ Y) ⊗ Z) (X ⊗ (Y ⊗ Z))
  | left_unit : ∀{X}, SymmOps (𝟙_ C ⊗ X) X
  | left_unit_inv : ∀{X}, SymmOps X (𝟙_ C ⊗ X)
  | right_unit : ∀{X}, SymmOps (X ⊗ 𝟙_ C) X

class BraidedEquivalent (X Y : C) : Prop where
  prop : ∃f: X ⟶ Y, braided C f

instance BraidedEquivalent.refl {X : C} : BraidedEquivalent X X where
  prop := ⟨𝟙 X, braided.id⟩

-- TODO: BraidedEquivalent.symm

theorem BraidedEquivalent.trans {X Y Z : C}
  : BraidedEquivalent X Y → BraidedEquivalent Y Z → BraidedEquivalent X Z
  | ⟨f, hf⟩, ⟨g, hg⟩ => ⟨f ≫ g, hf.comp hg⟩

-- instance BraidedEquivalent.ofMonoidalEquivalent {X Y : C} [MonoidalEquivalent X Y]
--   : BraidedEquivalent X Y where
--   prop := ⟨reassoc_eqv X Y, reassoc_spec X Y⟩

class RespectsBraid (P : C → Prop) : Prop where
  eqv_iff : ∀(X Y : C) [BraidedEquivalent X Y], P X ↔ P Y

-- TODO: RespectsBraid ==> RespectsAssoc

-- TODO: RespectsIso ==> RespectsBraid

instance RespectsBraid.instStrongMonoidalPredicate {P : C → Prop} [StrongMonoidalPredicate P]
  : RespectsBraid P where
  eqv_iff := λX Y ⟨f, h⟩ => by
    induction h using braided.induction' with
    | id => rfl
    | comp hf hg If Ig => exact (If ⟨_, hf⟩).trans (Ig ⟨_, hg⟩)
    | whiskerLeft hf If => simp [prop_tensor_iff, If ⟨_, hf⟩]
    | whiskerRight hf If => simp [prop_tensor_iff, If ⟨_, hf⟩]
    | _ => simp only [prop_tensor_iff, prop_id, and_assoc] <;> simp [and_comm]
