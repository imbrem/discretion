import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Limits.Shapes.Terminal

import Discretion.Premonoidal.Property.Basic

namespace CategoryTheory

open MonoidalCategory
open Limits
open MorphismProperty

variable {C : Type _} [Category C] [MonoidalCategoryStruct C]

class MonoidalEquivalent (X Y : C) : Prop where
  prop : ∃f: X ⟶ Y, monoidal C f

instance MonoidalEquivalent.refl (X : C) : MonoidalEquivalent X X where
  prop := ⟨𝟙 X, monoidal.id⟩

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

class StrongMonoidalPredicate (P : C → Prop) extends MonoidalPredicate' P : Prop where
  prop_tensor_left : ∀ {X Y}, P (X ⊗ Y) → P X := by aesop_cat
  prop_tensor_right : ∀ {X Y}, P (X ⊗ Y) → P Y := by aesop_cat

class CartesianPredicate (P : C → Prop) : Prop where
  prop_terminal : [HasTerminal C] → P (⊤_ C) := by aesop_cat
  prop_prod : ∀ {X Y} [HasBinaryProduct X Y], P X → P Y → P (X ⨯ Y) := by aesop_cat

class StrongCartesianPredicate (P : C → Prop) extends CartesianPredicate P : Prop where
  prop_prod_left : ∀ {X Y} [HasBinaryProduct X Y], P (X ⨯ Y) → P X := by aesop_cat
  prop_prod_right : ∀ {X Y} [HasBinaryProduct X Y], P (X ⨯ Y) → P Y := by aesop_cat

class CoCartesianPredicate (P : C → Prop) : Prop where
  prop_initial : [HasInitial C] → P (⊥_ C) := by aesop_cat
  prop_coprod : ∀ {X Y} [HasBinaryCoproduct X Y], P X → P Y → P (X ⨿ Y) := by aesop_cat

class StrongCoCartesianPredicate (P : C → Prop) extends CoCartesianPredicate P : Prop where
  prop_coprod_left : ∀ {X Y} [HasBinaryCoproduct X Y], P (X ⨿ Y) → P X := by aesop_cat
  prop_coprod_right : ∀ {X Y} [HasBinaryCoproduct X Y], P (X ⨿ Y) → P Y := by aesop_cat
