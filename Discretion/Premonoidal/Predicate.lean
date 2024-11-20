import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Limits.Shapes.Terminal

import Discretion.Premonoidal.Property.Basic
import Discretion.Premonoidal.Property.Braided

namespace CategoryTheory

open MonoidalCategory
open Limits
open MorphismProperty

variable {C : Type _} [Category C]

class CartesianPredicate (P : C → Prop) : Prop where
  prop_terminal : [HasTerminal C] → P (⊤_ C) := by aesop_cat
  prop_prod : ∀ {X Y} [HasBinaryProduct X Y], P X → P Y → P (X ⨯ Y) := by aesop_cat

class StrongCartesianPredicate (P : C → Prop) extends CartesianPredicate P : Prop where
  prop_prod_left : ∀ {X Y} [HasBinaryProduct X Y], P (X ⨯ Y) → P X := by aesop_cat
  prop_prod_right : ∀ {X Y} [HasBinaryProduct X Y], P (X ⨯ Y) → P Y := by aesop_cat

instance StrongCartesianPredicate.instTop : StrongCartesianPredicate (⊤ : C → Prop) where
  prop_terminal := trivial
  prop_prod _ _ := trivial
  prop_prod_left _ := trivial
  prop_prod_right _ := trivial

class CoCartesianPredicate (P : C → Prop) : Prop where
  prop_initial : [HasInitial C] → P (⊥_ C) := by aesop_cat
  prop_coprod : ∀ {X Y} [HasBinaryCoproduct X Y], P X → P Y → P (X ⨿ Y) := by aesop_cat

class StrongCoCartesianPredicate (P : C → Prop) extends CoCartesianPredicate P : Prop where
  prop_coprod_left : ∀ {X Y} [HasBinaryCoproduct X Y], P (X ⨿ Y) → P X := by aesop_cat
  prop_coprod_right : ∀ {X Y} [HasBinaryCoproduct X Y], P (X ⨿ Y) → P Y := by aesop_cat

instance StrongCoCartesianPredicate.instTop : StrongCoCartesianPredicate (⊤ : C → Prop) where
  prop_initial := trivial
  prop_coprod _ _ := trivial
  prop_coprod_left _ := trivial
  prop_coprod_right _ := trivial

namespace Monoidal

theorem prop_terminal {P : C → Prop} [CartesianPredicate P] [HasTerminal C] : P (⊤_ C)
  := CartesianPredicate.prop_terminal

theorem prop_prod {P : C → Prop} [CartesianPredicate P] {X Y : C} [HasBinaryProduct X Y]
  : P X → P Y → P (X ⨯ Y) := CartesianPredicate.prop_prod

theorem prop_prod_left {P : C → Prop} [StrongCartesianPredicate P] {X Y : C} [HasBinaryProduct X Y]
  : P (X ⨯ Y) → P X := StrongCartesianPredicate.prop_prod_left

theorem prop_prod_right {P : C → Prop} [StrongCartesianPredicate P] {X Y : C} [HasBinaryProduct X Y]
  : P (X ⨯ Y) → P Y := StrongCartesianPredicate.prop_prod_right

theorem prop_prod_iff {P : C → Prop} [StrongCartesianPredicate P] {X Y : C} [HasBinaryProduct X Y]
  : P (X ⨯ Y) ↔ P X ∧ P Y
  := ⟨λh => ⟨prop_prod_left h, prop_prod_right h⟩, λ⟨h1, h2⟩ => prop_prod h1 h2⟩

theorem prop_initial {P : C → Prop} [CoCartesianPredicate P] [HasInitial C] : P (⊥_ C)
  := CoCartesianPredicate.prop_initial

theorem prop_coprod {P : C → Prop} [CoCartesianPredicate P] {X Y : C} [HasBinaryCoproduct X Y]
  : P X → P Y → P (X ⨿ Y) := CoCartesianPredicate.prop_coprod

theorem prop_coprod_left {P : C → Prop} [StrongCoCartesianPredicate P]
  {X Y : C} [HasBinaryCoproduct X Y]
  : P (X ⨿ Y) → P X := StrongCoCartesianPredicate.prop_coprod_left

theorem prop_coprod_right {P : C → Prop} [StrongCoCartesianPredicate P]
  {X Y : C} [HasBinaryCoproduct X Y]
  : P (X ⨿ Y) → P Y := StrongCoCartesianPredicate.prop_coprod_right

theorem prop_coprod_iff {P : C → Prop} [StrongCoCartesianPredicate P]
  {X Y : C} [HasBinaryCoproduct X Y]
  : P (X ⨿ Y) ↔ P X ∧ P Y
  := ⟨λh => ⟨prop_coprod_left h, prop_coprod_right h⟩, λ⟨h1, h2⟩ => prop_coprod h1 h2⟩

end Monoidal

open Monoidal

instance CartesianPredicate.inf {P Q : C → Prop} [CartesianPredicate P] [CartesianPredicate Q]
  : CartesianPredicate (P ⊓ Q) where
  prop_terminal := ⟨prop_terminal, prop_terminal⟩
  prop_prod h1 h2 := ⟨prop_prod h1.1 h2.1, prop_prod h1.2 h2.2⟩

instance StrongCartesianPredicate.inf {P Q : C → Prop}
  [StrongCartesianPredicate P] [StrongCartesianPredicate Q]
  : StrongCartesianPredicate (P ⊓ Q) where
  prop_prod_left h := ⟨prop_prod_left h.1, prop_prod_left h.2⟩
  prop_prod_right h := ⟨prop_prod_right h.1, prop_prod_right h.2⟩

instance CoCartesianPredicate.inf {P Q : C → Prop} [CoCartesianPredicate P] [CoCartesianPredicate Q]
  : CoCartesianPredicate (P ⊓ Q) where
  prop_initial := ⟨prop_initial, prop_initial⟩
  prop_coprod h1 h2 := ⟨prop_coprod h1.1 h2.1, prop_coprod h1.2 h2.2⟩

instance StrongCoCartesianPredicate.inf {P Q : C → Prop}
  [StrongCoCartesianPredicate P] [StrongCoCartesianPredicate Q]
  : StrongCoCartesianPredicate (P ⊓ Q) where
  prop_coprod_left h := ⟨prop_coprod_left h.1, prop_coprod_left h.2⟩
  prop_coprod_right h := ⟨prop_coprod_right h.1, prop_coprod_right h.2⟩

variable [MonoidalCategoryStruct C]

class MonoidalEquivalent (X Y : C) : Prop where
  prop : ∃f: X ⟶ Y, monoidal C f

instance MonoidalEquivalent.refl (X : C) : MonoidalEquivalent X X where
  prop := ⟨𝟙 X, monoidal.id⟩

-- theorem MonoidalEquivalent.symm {X Y : C} (h : MonoidalEquivalent X Y) : MonoidalEquivalent Y X
--   := sorry

theorem MonoidalEquivalent.trans {X Y Z : C}
  : MonoidalEquivalent X Y → MonoidalEquivalent Y Z → MonoidalEquivalent X Z
  | ⟨f, hf⟩, ⟨g, hg⟩ => ⟨f ≫ g, hf.comp hg⟩

-- TODO: tensor?

namespace Monoidal

noncomputable def reassoc_eqv (X Y : C) [MonoidalEquivalent X Y] : X ⟶ Y
  := Classical.choose MonoidalEquivalent.prop

noncomputable def reassoc_spec (X Y : C) [MonoidalEquivalent X Y] : monoidal C (reassoc_eqv X Y)
  := Classical.choose_spec MonoidalEquivalent.prop

-- TODO: reassoc becomes the associator, etc, under coherence

end Monoidal

class MonoidalPredicate' (P : C → Prop) : Prop where
  prop_id : P (𝟙_ C) := by aesop_cat
  prop_tensor : ∀ {X Y}, P X → P Y → P (X ⊗ Y) := by aesop_cat

class RespectsAssoc (P : C → Prop) : Prop where
  eqv_iff : ∀(X Y : C) [MonoidalEquivalent X Y], P X ↔ P Y

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

theorem prop_eqv {P : C → Prop} [RespectsAssoc P] {X Y : C} [MonoidalEquivalent X Y]
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

variable [BraidedCategoryStruct C]

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
