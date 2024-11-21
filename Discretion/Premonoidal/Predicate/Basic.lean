import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Limits.Shapes.Terminal

import Discretion.Premonoidal.Property.Basic
import Discretion.Premonoidal.Property.Braided

namespace CategoryTheory

open MonoidalCategory
open Limits
open MorphismProperty

variable {C : Type _} [Category C] [MonoidalCategoryStruct C]

open Monoidal

namespace Monoidal

inductive TensorClosure (R : C → C → Prop) : C → C → Prop where
  | refl : ∀{X}, TensorClosure R X X
  | trans : ∀{X Y Z}, TensorClosure R X Y → TensorClosure R Y Z → TensorClosure R X Z
  | tensor_right : ∀{X Y Z}, R X Y → TensorClosure R (X ⊗ Z) (Y ⊗ Z)
  | tensor_left : ∀{X Y Z}, R X Y → TensorClosure R (Z ⊗ X) (Z ⊗ Y)
  | base : ∀{X Y}, R X Y → TensorClosure R X Y

inductive AssocOps : C → C → Prop where
  | assoc : ∀{X Y Z}, AssocOps (X ⊗ (Y ⊗ Z)) ((X ⊗ Y) ⊗ Z)
  | assoc_inv : ∀{X Y Z}, AssocOps ((X ⊗ Y) ⊗ Z) (X ⊗ (Y ⊗ Z))
  | left_unit : ∀{X}, AssocOps (𝟙_ C ⊗ X) X
  | left_unit_inv : ∀{X}, AssocOps X (𝟙_ C ⊗ X)
  | right_unit : ∀{X}, AssocOps (X ⊗ 𝟙_ C) X
  | right_unit_inv : ∀{X}, AssocOps X (X ⊗ 𝟙_ C)

class AssocEqv (X Y : C) : Prop where
  prop : ∃f: X ⟶ Y, monoidal C f

theorem AssocEqv.trans {X Y Z : C}
  : AssocEqv X Y → AssocEqv Y Z → AssocEqv X Z
  | ⟨f, hf⟩, ⟨g, hg⟩ => ⟨f ≫ g, hf.comp hg⟩

-- TODO: AssocEqv iff TensorClosure (AssocOps)

instance AssocEqv.refl (X : C) : AssocEqv X X where
  prop := ⟨𝟙 X, monoidal.id⟩

noncomputable def reassoc_eqv (X Y : C) [AssocEqv X Y] : X ⟶ Y
  := Classical.choose AssocEqv.prop

noncomputable def reassoc_spec (X Y : C) [AssocEqv X Y] : monoidal C (reassoc_eqv X Y)
  := Classical.choose_spec AssocEqv.prop

-- TODO: reassoc becomes the associator, etc, under coherence

end Monoidal

class MonoidalPredicate' (P : C → Prop) : Prop where
  prop_id : P (𝟙_ C) := by aesop_cat
  prop_tensor : ∀ {X Y}, P X → P Y → P (X ⊗ Y) := by aesop_cat

class RespectsAssoc (P : C → Prop) : Prop where
  eqv_iff : ∀(X Y : C) [AssocEqv X Y], P X ↔ P Y

class CoherentMonoidalPredicate (P : C → Prop)
  extends MonoidalPredicate' P, RespectsAssoc P : Prop where

-- TODO: RespectsIso ==> RespectsAssoc

class StrongMonoidalPredicate (P : C → Prop) extends MonoidalPredicate' P : Prop where
  prop_tensor_left : ∀ {X Y}, P (X ⊗ Y) → P X := by aesop_cat
  prop_tensor_right : ∀ {X Y}, P (X ⊗ Y) → P Y := by aesop_cat

instance StrongMonoidalPredicate.instTop : StrongMonoidalPredicate (⊤ : C → Prop) where
  prop_id := trivial
  prop_tensor _ _ := trivial
  prop_tensor_left _ := trivial
  prop_tensor_right _ := trivial

namespace Monoidal

theorem prop_id {P : C → Prop} [MonoidalPredicate' P] : P (𝟙_ C) := MonoidalPredicate'.prop_id

theorem prop_tensor {P : C → Prop} [MonoidalPredicate' P] {X Y : C} : P X → P Y → P (X ⊗ Y)
  := MonoidalPredicate'.prop_tensor

theorem prop_tensor_left {P : C → Prop} [StrongMonoidalPredicate P] {X Y : C} : P (X ⊗ Y) → P X
  := StrongMonoidalPredicate.prop_tensor_left

theorem prop_tensor_right {P : C → Prop} [StrongMonoidalPredicate P] {X Y : C} : P (X ⊗ Y) → P Y
  := StrongMonoidalPredicate.prop_tensor_right

theorem prop_tensor_iff {P : C → Prop} [StrongMonoidalPredicate P] {X Y : C}
  : P (X ⊗ Y) ↔ P X ∧ P Y
  := ⟨λh => ⟨prop_tensor_left h, prop_tensor_right h⟩, λ⟨h1, h2⟩ => prop_tensor h1 h2⟩

theorem prop_eqv {P : C → Prop} [RespectsAssoc P] {X Y : C} [AssocEqv X Y]
  : P X ↔ P Y := RespectsAssoc.eqv_iff X Y

end Monoidal

instance MonoidalPredicate'.inf {P Q : C → Prop} [MonoidalPredicate' P] [MonoidalPredicate' Q]
  : MonoidalPredicate' (P ⊓ Q) where
  prop_id := ⟨prop_id, prop_id⟩
  prop_tensor h1 h2 := ⟨prop_tensor h1.1 h2.1, prop_tensor h1.2 h2.2⟩

instance StrongMonoidalPredicate.inf {P Q : C → Prop}
  [StrongMonoidalPredicate P] [StrongMonoidalPredicate Q]
  : StrongMonoidalPredicate (P ⊓ Q) where
  prop_tensor_left h := ⟨prop_tensor_left h.1, prop_tensor_left h.2⟩
  prop_tensor_right h := ⟨prop_tensor_right h.1, prop_tensor_right h.2⟩

instance RespectsAssoc.instStrongMonoidalPredicate {P : C → Prop} [StrongMonoidalPredicate P]
  : RespectsAssoc P where
  eqv_iff := λX Y ⟨f, h⟩ => by
    induction h using monoidal.induction' with
    | id => rfl
    | comp hf hg If Ig => exact (If ⟨_, hf⟩).trans (Ig ⟨_, hg⟩)
    | whiskerLeft hf If => simp [prop_tensor_iff, If ⟨_, hf⟩]
    | whiskerRight hf If => simp [prop_tensor_iff, If ⟨_, hf⟩]
    | _ => simp [prop_tensor_iff, prop_id, and_assoc]
