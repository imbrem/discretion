import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Limits.Shapes.Terminal

namespace CategoryTheory

open MonoidalCategory
 open Limits

variable {C : Type u} [Category.{v} C] [MonoidalCategoryStruct C]

class MonoidalPredicate' (P : C → Prop) : Prop where
  prop_id : P (𝟙_ C) := by aesop_cat
  prop_tensor : ∀ {X Y}, P X → P Y → P (X ⊗ Y) := by aesop_cat

class CartesianPredicate (P : C → Prop) : Prop where
  prop_terminal : [HasTerminal C] → P (⊤_ C) := by aesop_cat
  prop_prod : ∀ {X Y} [HasBinaryProduct X Y], P X → P Y → P (X ⨯ Y) := by aesop_cat

class CoCartesianPredicate (P : C → Prop) : Prop where
  prop_initial : [HasInitial C] → P (⊥_ C) := by aesop_cat
  prop_prod : ∀ {X Y} [HasBinaryCoproduct X Y], P X → P Y → P (X ⨿ Y) := by aesop_cat
