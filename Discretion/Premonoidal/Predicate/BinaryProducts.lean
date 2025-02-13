import Discretion.Premonoidal.Property.Basic
import Discretion.Premonoidal.Property.Braided
import Discretion.ChosenFiniteCoproducts

namespace CategoryTheory

open MonoidalCategory
open MorphismProperty
open ChosenFiniteCoproducts

variable {C : Type _} [Category C]

section Product

variable [ChosenFiniteProducts C]

class CartesianPredicate (P : C → Prop) : Prop where
  prop_terminal : P (𝟙_ C) := by aesop_cat
  prop_prod : ∀ {X Y}, P X → P Y → P (X ⊗ Y) := by aesop_cat

class StrongCartesianPredicate (P : C → Prop) extends CartesianPredicate P : Prop where
  prop_prod_left : ∀ {X Y}, P (X ⊗ Y) → P X := by aesop_cat
  prop_prod_right : ∀ {X Y}, P (X ⊗ Y) → P Y := by aesop_cat

instance StrongCartesianPredicate.instTop : StrongCartesianPredicate (⊤ : C → Prop) where
  prop_terminal := trivial
  prop_prod _ _ := trivial
  prop_prod_left _ := trivial
  prop_prod_right _ := trivial

end Product

section Coproduct

variable [ChosenFiniteCoproducts C]

class CoCartesianPredicate (P : C → Prop) : Prop where
  prop_initial : P (𝟘_ C) := by aesop_cat
  prop_coprod : ∀ {X Y}, P X → P Y → P (X ⊕ₒ Y) := by aesop_cat

class StrongCoCartesianPredicate (P : C → Prop) extends CoCartesianPredicate P : Prop where
  prop_coprod_left : ∀ {X Y}, P (X ⊕ₒ Y) → P X := by aesop_cat
  prop_coprod_right : ∀ {X Y}, P (X ⊕ₒ Y) → P Y := by aesop_cat

instance StrongCoCartesianPredicate.instTop : StrongCoCartesianPredicate (⊤ : C → Prop) where
  prop_initial := trivial
  prop_coprod _ _ := trivial
  prop_coprod_left _ := trivial
  prop_coprod_right _ := trivial

end Coproduct

namespace Monoidal

-- section Product

-- theorem prop_terminal {P : C → Prop} [CartesianPredicate P] [HasTerminal C] : P (⊤_ C)
--   := CartesianPredicate.prop_terminal

-- theorem prop_prod {P : C → Prop} [CartesianPredicate P] {X Y : C} [HasBinaryProduct X Y]
--   : P X → P Y → P (X ⨯ Y) := CartesianPredicate.prop_prod

-- theorem prop_prod_left {P : C → Prop} [StrongCartesianPredicate P] {X Y : C} [HasBinaryProduct X Y]
--   : P (X ⨯ Y) → P X := StrongCartesianPredicate.prop_prod_left

-- theorem prop_prod_right {P : C → Prop} [StrongCartesianPredicate P] {X Y : C} [HasBinaryProduct X Y]
--   : P (X ⨯ Y) → P Y := StrongCartesianPredicate.prop_prod_right

-- theorem prop_prod_iff {P : C → Prop} [StrongCartesianPredicate P] {X Y : C} [HasBinaryProduct X Y]
--   : P (X ⨯ Y) ↔ P X ∧ P Y
--   := ⟨λh => ⟨prop_prod_left h, prop_prod_right h⟩, λ⟨h1, h2⟩ => prop_prod h1 h2⟩

-- theorem prop_initial {P : C → Prop} [CoCartesianPredicate P] [HasInitial C] : P (⊥_ C)
--   := CoCartesianPredicate.prop_initial

-- theorem prop_coprod {P : C → Prop} [CoCartesianPredicate P] {X Y : C} [HasBinaryCoproduct X Y]
--   : P X → P Y → P (X ⨿ Y) := CoCartesianPredicate.prop_coprod

-- theorem prop_coprod_left {P : C → Prop} [StrongCoCartesianPredicate P]
--   {X Y : C} [HasBinaryCoproduct X Y]
--   : P (X ⨿ Y) → P X := StrongCoCartesianPredicate.prop_coprod_left

-- theorem prop_coprod_right {P : C → Prop} [StrongCoCartesianPredicate P]
--   {X Y : C} [HasBinaryCoproduct X Y]
--   : P (X ⨿ Y) → P Y := StrongCoCartesianPredicate.prop_coprod_right

-- theorem prop_coprod_iff {P : C → Prop} [StrongCoCartesianPredicate P]
--   {X Y : C} [HasBinaryCoproduct X Y]
--   : P (X ⨿ Y) ↔ P X ∧ P Y
--   := ⟨λh => ⟨prop_coprod_left h, prop_coprod_right h⟩, λ⟨h1, h2⟩ => prop_coprod h1 h2⟩

-- end Monoidal

open Monoidal

-- instance CartesianPredicate.inf {P Q : C → Prop} [CartesianPredicate P] [CartesianPredicate Q]
--   : CartesianPredicate (P ⊓ Q) where
--   prop_terminal := ⟨prop_terminal, prop_terminal⟩
--   prop_prod h1 h2 := ⟨prop_prod h1.1 h2.1, prop_prod h1.2 h2.2⟩

-- instance StrongCartesianPredicate.inf {P Q : C → Prop}
--   [StrongCartesianPredicate P] [StrongCartesianPredicate Q]
--   : StrongCartesianPredicate (P ⊓ Q) where
--   prop_prod_left h := ⟨prop_prod_left h.1, prop_prod_left h.2⟩
--   prop_prod_right h := ⟨prop_prod_right h.1, prop_prod_right h.2⟩

-- instance CoCartesianPredicate.inf {P Q : C → Prop} [CoCartesianPredicate P] [CoCartesianPredicate Q]
--   : CoCartesianPredicate (P ⊓ Q) where
--   prop_initial := ⟨prop_initial, prop_initial⟩
--   prop_coprod h1 h2 := ⟨prop_coprod h1.1 h2.1, prop_coprod h1.2 h2.2⟩

-- instance StrongCoCartesianPredicate.inf {P Q : C → Prop}
--   [StrongCoCartesianPredicate P] [StrongCoCartesianPredicate Q]
--   : StrongCoCartesianPredicate (P ⊓ Q) where
--   prop_coprod_left h := ⟨prop_coprod_left h.1, prop_coprod_left h.2⟩
--   prop_coprod_right h := ⟨prop_coprod_right h.1, prop_coprod_right h.2⟩
