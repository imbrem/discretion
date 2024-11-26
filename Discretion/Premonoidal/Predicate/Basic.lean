import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import Mathlib.Order.Defs

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
  | tensor_right : ∀{X Y Z}, TensorClosure R X Y → TensorClosure R (X ⊗ Z) (Y ⊗ Z)
  | tensor_left : ∀{X Y Z}, TensorClosure R X Y → TensorClosure R (Z ⊗ X) (Z ⊗ Y)
  | base : ∀{X Y}, R X Y → TensorClosure R X Y
  | trans : ∀{X Y Z}, TensorClosure R X Y → TensorClosure R Y Z → TensorClosure R X Z

-- @[simp]
theorem TensorClosure.bot : TensorClosure (C := C) ⊥ = Eq := by
  ext X Y; constructor
  · intro h; induction h with | base h => exact h.elim | _ => simp [*]
  · intro h; cases h; constructor

-- @[simp]
theorem TensorClosure.top : TensorClosure (C := C) ⊤ = ⊤
  := by ext X Y; simp [TensorClosure.base (R := ⊤) trivial]

theorem TensorClosure.increasing {R : C → C → Prop} : R ≤ TensorClosure R
  := λ _ _ => TensorClosure.base

-- @[simp]
theorem TensorClosure.idem {R : C → C → Prop} : TensorClosure (TensorClosure R) = TensorClosure R
  := le_antisymm
      (λ _ _ h => by induction h with
      | base h => exact h
      | trans => apply trans <;> assumption
      | _ => constructor <;> assumption)
      increasing

theorem TensorClosure.mono {R S : C → C → Prop} (h : R ≤ S) : TensorClosure R ≤ TensorClosure S
  := λ x y h => by induction h with
    | base h' => exact base (h _ _ h')
    | trans => apply trans <;> assumption
    | _ => constructor <;> assumption

theorem TensorClosure.symm {R : C → C → Prop} [IsSymm C R] {X Y : C} (h : TensorClosure R X Y)
  : TensorClosure R Y X := by induction h with
  | base h => exact base (IsSymm.symm _ _ h)
  | trans _ _ I I' => exact trans I' I
  | _ => constructor <;> assumption

instance TensorClosure.is_symm {R : C → C → Prop} [IsSymm C R] : IsSymm C (TensorClosure R) where
  symm _ _ := symm

inductive AssocOps : C → C → Prop where
  | assoc : ∀{X Y Z}, AssocOps (X ⊗ (Y ⊗ Z)) ((X ⊗ Y) ⊗ Z)
  | assoc_inv : ∀{X Y Z}, AssocOps ((X ⊗ Y) ⊗ Z) (X ⊗ (Y ⊗ Z))
  | left_unit : ∀{X}, AssocOps (𝟙_ C ⊗ X) X
  | left_unit_inv : ∀{X}, AssocOps X (𝟙_ C ⊗ X)
  | right_unit : ∀{X}, AssocOps (X ⊗ 𝟙_ C) X
  | right_unit_inv : ∀{X}, AssocOps X (X ⊗ 𝟙_ C)

theorem AssocOps.symm {X Y : C} (h : AssocOps X Y) : AssocOps Y X := by cases h <;> constructor

instance AssocOps.is_symm : IsSymm C AssocOps where symm _ _ := symm

class AssocEqv (X Y : C) : Prop where
  prop : TensorClosure AssocOps X Y

instance AssocEqv.refl (X : C) : AssocEqv X X where
  prop := TensorClosure.refl

instance AssocEqv.tensor_right {X Y Z : C} [AssocEqv X Y] : AssocEqv (X ⊗ Z) (Y ⊗ Z) where
  prop := TensorClosure.tensor_right AssocEqv.prop

instance AssocEqv.tensor_left {X Y Z : C} [AssocEqv X Y] : AssocEqv (Z ⊗ X) (Z ⊗ Y) where
  prop := TensorClosure.tensor_left AssocEqv.prop

instance AssocEqv.assoc {X Y Z : C} : AssocEqv (X ⊗ (Y ⊗ Z)) ((X ⊗ Y) ⊗ Z) where
  prop := TensorClosure.base AssocOps.assoc

instance AssocEqv.assoc_inv {X Y Z : C} : AssocEqv ((X ⊗ Y) ⊗ Z) (X ⊗ (Y ⊗ Z)) where
  prop := TensorClosure.base AssocOps.assoc_inv

instance AssocEqv.left_unit {X : C} : AssocEqv (𝟙_ C ⊗ X) X where
  prop := TensorClosure.base AssocOps.left_unit

instance AssocEqv.left_unit_inv {X : C} : AssocEqv X (𝟙_ C ⊗ X) where
  prop := TensorClosure.base AssocOps.left_unit_inv

instance AssocEqv.right_unit {X : C} : AssocEqv (X ⊗ 𝟙_ C) X where
  prop := TensorClosure.base AssocOps.right_unit

instance AssocEqv.right_unit_inv {X : C} : AssocEqv X (X ⊗ 𝟙_ C) where
  prop := TensorClosure.base AssocOps.right_unit_inv

theorem AssocEqv.symm (X Y : C) [AssocEqv X Y] : AssocEqv Y X where
  prop := AssocEqv.prop.symm

theorem AssocEqv.trans (X Y Z : C) [AssocEqv X Y] [AssocEqv Y Z] : AssocEqv X Z where
  prop := TensorClosure.trans (X := X) (Y := Y) (Z := Z) AssocEqv.prop AssocEqv.prop

theorem TensorClosure.exists {X Y : C} (h : TensorClosure AssocOps X Y) : ∃f : X ⟶ Y, monoidal C f
  := by induction h with
  | refl => exact ⟨𝟙 _, monoidal.id⟩
  | tensor_right h I => exact ⟨I.choose ▷ _, monoidal.whiskerRight I.choose_spec⟩
  | tensor_left h I => exact ⟨_ ◁ I.choose, monoidal.whiskerLeft I.choose_spec⟩
  | trans h1 h2 I1 I2 => exact ⟨I1.choose ≫ I2.choose, monoidal.comp I1.choose_spec I2.choose_spec⟩
  | base h => cases h <;> exact ⟨_, monoidal.s (by constructor)⟩

theorem TensorClosure.of_hom {X Y : C} (f : X ⟶ Y) (hf : monoidal C f) : TensorClosure AssocOps X Y
  := by induction hf using monoidal.induction with
  | comp => apply TensorClosure.trans <;> assumption
  | s h => apply TensorClosure.base; cases h <;> constructor
  | _ => constructor <;> assumption

theorem TensorClosure.exists_iff {X Y : C} : TensorClosure AssocOps X Y ↔ ∃f : X ⟶ Y, monoidal C f
  := ⟨TensorClosure.exists, λ⟨f, hf⟩ => of_hom f hf⟩

noncomputable def reassoc (X Y : C) [AssocEqv X Y] : X ⟶ Y
  := Classical.choose AssocEqv.prop.exists

noncomputable def reassoc_spec (X Y : C) [AssocEqv X Y] : monoidal C (reassoc X Y)
  := Classical.choose_spec AssocEqv.prop.exists

-- TODO: by coherence, composition of reassoc gives reassoc

-- TODO: reassoc becomes the associator, etc, under coherence

end Monoidal

class MonoidalPredicate' (P : C → Prop) : Prop where
  prop_id : P (𝟙_ C) := by aesop_cat
  prop_tensor : ∀ {X Y}, P X → P Y → P (X ⊗ Y) := by aesop_cat

class RespectsAssoc (P : C → Prop) : Prop where
  eqv_iff : ∀(X Y : C) [AssocEqv X Y], P X ↔ P Y

-- TODO: RespectsIso ==> RespectsAssoc

class ReflectsTensor (P : C → Prop) : Prop where
  prop_tensor_left : ∀ {X Y}, P (X ⊗ Y) → P X
  prop_tensor_right : ∀ {X Y}, P (X ⊗ Y) → P Y

class StrongMonoidalPredicate (P : C → Prop) extends MonoidalPredicate' P, ReflectsTensor P

instance {P : C → Prop} [MonoidalPredicate' P] [ReflectsTensor P] : StrongMonoidalPredicate P where

instance StrongMonoidalPredicate.instTop : StrongMonoidalPredicate (⊤ : C → Prop) where
  prop_id := trivial
  prop_tensor _ _ := trivial
  prop_tensor_left _ := trivial
  prop_tensor_right _ := trivial

theorem StrongMonoidalPredicate.mk' {P : C → Prop}
  (prop_id : P (𝟙_ C))
  (prop_tensor_iff : ∀{X Y : C}, P (X ⊗ Y) ↔ P X ∧ P Y)
  : StrongMonoidalPredicate P where
  prop_tensor_left h := (prop_tensor_iff.mp h).1
  prop_tensor_right h := (prop_tensor_iff.mp h).2

namespace Monoidal

theorem prop_id {P : C → Prop} [MonoidalPredicate' P] : P (𝟙_ C) := MonoidalPredicate'.prop_id

theorem prop_tensor {P : C → Prop} [MonoidalPredicate' P] {X Y : C} : P X → P Y → P (X ⊗ Y)
  := MonoidalPredicate'.prop_tensor

theorem prop_tensor_left {P : C → Prop} [ReflectsTensor P] {X Y : C} : P (X ⊗ Y) → P X
  := ReflectsTensor.prop_tensor_left

theorem prop_tensor_right {P : C → Prop} [ReflectsTensor P] {X Y : C} : P (X ⊗ Y) → P Y
  := ReflectsTensor.prop_tensor_right

theorem prop_tensor_iff {P : C → Prop} [StrongMonoidalPredicate P] [ReflectsTensor P] {X Y : C}
  : P (X ⊗ Y) ↔ P X ∧ P Y
  := ⟨λh => ⟨prop_tensor_left h, prop_tensor_right h⟩, λ⟨h1, h2⟩ => prop_tensor h1 h2⟩

theorem prop_eqv {P : C → Prop} [RespectsAssoc P] {X Y : C} [AssocEqv X Y]
  : P X ↔ P Y := RespectsAssoc.eqv_iff X Y

end Monoidal

instance MonoidalPredicate'.inf {P Q : C → Prop} [MonoidalPredicate' P] [MonoidalPredicate' Q]
  : MonoidalPredicate' (P ⊓ Q) where
  prop_id := ⟨prop_id, prop_id⟩
  prop_tensor h1 h2 := ⟨prop_tensor h1.1 h2.1, prop_tensor h1.2 h2.2⟩

instance ReflectsTensor.inf {P Q : C → Prop} [ReflectsTensor P] [ReflectsTensor Q]
  : ReflectsTensor (P ⊓ Q) where
  prop_tensor_left h := ⟨prop_tensor_left h.1, prop_tensor_left h.2⟩
  prop_tensor_right h := ⟨prop_tensor_right h.1, prop_tensor_right h.2⟩

theorem StrongMonoidalPredicate.inf {P Q : C → Prop}
  [StrongMonoidalPredicate P] [StrongMonoidalPredicate Q]
  : StrongMonoidalPredicate (P ⊓ Q) := inferInstance

instance RespectsAssoc.instStrongMonoidalPredicate {P : C → Prop} [StrongMonoidalPredicate P]
  : RespectsAssoc P where
  eqv_iff := λX Y ⟨h⟩ => by
    induction h with
    | refl => rfl
    | trans hf hg If Ig => exact (If ⟨hf⟩).trans (Ig ⟨hg⟩)
    | tensor_left hf If => simp [prop_tensor_iff, If ⟨hf⟩]
    | tensor_right hf If => simp [prop_tensor_iff, If ⟨hf⟩]
    | base h => cases h <;> simp [prop_tensor_iff, prop_id, and_assoc]
