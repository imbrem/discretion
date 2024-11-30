import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import Mathlib.CategoryTheory.Iso
import Mathlib.Order.Basic

import Discretion.Premonoidal.Property.Basic
import Discretion.Premonoidal.Property.Braided

namespace CategoryTheory

open MonoidalCategory
open Limits
open MorphismProperty

variable {C : Type _} [Category C]

open Monoidal

namespace Monoidal

class RespectsIso (P : C → Prop) : Prop where
  prop_iso_iff : ∀{X Y : C} (f : X ⟶ Y) [IsIso f], (P X ↔ P Y)

theorem RespectsIso.mk' {P : C → Prop}
  (prop_iso : ∀{X Y : C} (f : X ⟶ Y) [IsIso f], P X → P Y)
  : RespectsIso P where
  prop_iso_iff f := ⟨prop_iso f, prop_iso (inv f)⟩

theorem prop_iso_iff {P : C → Prop} [RespectsIso P] {X Y : C} (f : X ⟶ Y) [IsIso f]
  : P X ↔ P Y := RespectsIso.prop_iso_iff f

theorem prop_iso {P : C → Prop} [RespectsIso P] {X Y : C} (f : X ⟶ Y) [IsIso f]
  : P X → P Y := (prop_iso_iff f).mp

variable [MonoidalCategoryStruct C]

class RespectsCentralIso (P : C → Prop) : Prop where
  prop_iso_iff : ∀{X Y : C} (f : X ⟶ Y) [IsIso f] [Central f], (P X ↔ P Y)

theorem RespectsCentralIso.mk' [IsPremonoidal C] {P : C → Prop}
  (prop_iso : ∀{X Y : C} (f : X ⟶ Y) [IsIso f] [Central f], P X → P Y)
  : RespectsCentralIso P where
  prop_iso_iff f := ⟨prop_iso f, prop_iso (inv f)⟩

instance RespectsIso.respects_central {P : C → Prop} [RespectsIso P]
  : RespectsCentralIso P where
  prop_iso_iff := λf => RespectsIso.prop_iso_iff f

theorem prop_central_iso_iff {P : C → Prop} [RespectsCentralIso P]
  {X Y : C} (f : X ⟶ Y) [IsIso f] [Central f]
  : P X ↔ P Y := RespectsCentralIso.prop_iso_iff f

theorem prop_central_iso {P : C → Prop} [RespectsCentralIso P]
  {X Y : C} (f : X ⟶ Y) [IsIso f] [Central f]
  : P X → P Y := (prop_central_iso_iff f).mp

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

theorem TensorClosure.exists_monoidal {X Y : C} (h : TensorClosure AssocOps X Y)
  : ∃f : X ⟶ Y, monoidal C f
  := by induction h with
  | refl => exact ⟨𝟙 _, monoidal.id⟩
  | tensor_right h I => exact ⟨I.choose ▷ _, monoidal.whiskerRight I.choose_spec⟩
  | tensor_left h I => exact ⟨_ ◁ I.choose, monoidal.whiskerLeft I.choose_spec⟩
  | trans h1 h2 I1 I2 => exact ⟨I1.choose ≫ I2.choose, monoidal.comp I1.choose_spec I2.choose_spec⟩
  | base h => cases h <;> exact ⟨_, monoidal.s (by constructor)⟩

theorem TensorClosure.of_monoidal {X Y : C} (f : X ⟶ Y) (hf : monoidal C f)
  : TensorClosure AssocOps X Y
  := by induction hf using monoidal.induction with
  | comp => apply TensorClosure.trans <;> assumption
  | s h => apply TensorClosure.base; cases h <;> constructor
  | _ => constructor <;> assumption

theorem TensorClosure.exists_monoidal_iff {X Y : C}
  : TensorClosure AssocOps X Y ↔ ∃f : X ⟶ Y, monoidal C f
  := ⟨TensorClosure.exists_monoidal, λ⟨f, hf⟩ => of_monoidal f hf⟩

noncomputable def reassoc (X Y : C) [AssocEqv X Y] : X ⟶ Y
  := Classical.choose AssocEqv.prop.exists_monoidal

noncomputable def reassoc_spec (X Y : C) [AssocEqv X Y] : monoidal C (reassoc X Y)
  := Classical.choose_spec AssocEqv.prop.exists_monoidal

-- TODO: by coherence, composition of reassoc gives reassoc

-- TODO: in particular, reassoc X X is the identity, and hence reassoc is always an isomorphism

-- TODO: reassoc becomes the associator, etc, under coherence

class Predicate (P : C → Prop) : Prop where
  prop_id : P (𝟙_ C) := by aesop_cat
  prop_tensor : ∀ {X Y}, P X → P Y → P (X ⊗ Y) := by aesop_cat

class RespectsAssoc (P : C → Prop) : Prop where
  prop_eqv_iff : ∀(X Y : C) [AssocEqv X Y], P X ↔ P Y

theorem RespectsAssoc.mk' {P : C → Prop}
  (prop_eqv : ∀(X Y : C) [AssocEqv X Y], P X → P Y)
  : RespectsAssoc P where
  prop_eqv_iff X Y := ⟨prop_eqv X Y, have _ := AssocEqv.symm X Y; prop_eqv Y X⟩

class ReflectsTensor (P : C → Prop) : Prop where
  prop_tensor_left : ∀ {X Y}, P (X ⊗ Y) → P X
  prop_tensor_right : ∀ {X Y}, P (X ⊗ Y) → P Y

class StrongPredicate (P : C → Prop) extends Predicate P, ReflectsTensor P

instance {P : C → Prop} [Predicate P] [ReflectsTensor P] : StrongPredicate P where

instance StrongPredicate.instTop : StrongPredicate (⊤ : C → Prop) where
  prop_id := trivial
  prop_tensor _ _ := trivial
  prop_tensor_left _ := trivial
  prop_tensor_right _ := trivial

theorem StrongPredicate.mk' {P : C → Prop}
  (prop_id : P (𝟙_ C))
  (prop_tensor_iff : ∀{X Y : C}, P (X ⊗ Y) ↔ P X ∧ P Y)
  : StrongPredicate P where
  prop_tensor_left h := (prop_tensor_iff.mp h).1
  prop_tensor_right h := (prop_tensor_iff.mp h).2

theorem prop_id {P : C → Prop} [Predicate P] : P (𝟙_ C) := Predicate.prop_id

theorem prop_tensor {P : C → Prop} [Predicate P] {X Y : C} : P X → P Y → P (X ⊗ Y)
  := Predicate.prop_tensor

theorem prop_tensor_left {P : C → Prop} [ReflectsTensor P] {X Y : C} : P (X ⊗ Y) → P X
  := ReflectsTensor.prop_tensor_left

theorem prop_tensor_right {P : C → Prop} [ReflectsTensor P] {X Y : C} : P (X ⊗ Y) → P Y
  := ReflectsTensor.prop_tensor_right

theorem prop_tensor_iff {P : C → Prop} [StrongPredicate P] {X Y : C}
  : P (X ⊗ Y) ↔ P X ∧ P Y
  := ⟨λh => ⟨prop_tensor_left h, prop_tensor_right h⟩, λ⟨h1, h2⟩ => prop_tensor h1 h2⟩

theorem prop_assoc_eqv_iff {P : C → Prop} [RespectsAssoc P] {X Y : C} [AssocEqv X Y]
  : P X ↔ P Y := RespectsAssoc.prop_eqv_iff X Y

theorem prop_assoc_eqv {P : C → Prop} [RespectsAssoc P] {X Y : C} [AssocEqv X Y]
  : P X → P Y := prop_assoc_eqv_iff.mp

instance Predicate.inf {P Q : C → Prop} [Predicate P] [Predicate Q]
  : Predicate (P ⊓ Q) where
  prop_id := ⟨prop_id, prop_id⟩
  prop_tensor h1 h2 := ⟨prop_tensor h1.1 h2.1, prop_tensor h1.2 h2.2⟩

instance ReflectsTensor.inf {P Q : C → Prop} [ReflectsTensor P] [ReflectsTensor Q]
  : ReflectsTensor (P ⊓ Q) where
  prop_tensor_left h := ⟨prop_tensor_left h.1, prop_tensor_left h.2⟩
  prop_tensor_right h := ⟨prop_tensor_right h.1, prop_tensor_right h.2⟩

theorem StrongPredicate.inf {P Q : C → Prop}
  [StrongPredicate P] [StrongPredicate Q]
  : StrongPredicate (P ⊓ Q) := inferInstance

instance RespectsAssoc.instStrongPredicate {P : C → Prop} [StrongPredicate P]
  : RespectsAssoc P where
  prop_eqv_iff := λX Y ⟨h⟩ => by
    induction h with
    | refl => rfl
    | trans hf hg If Ig => exact (If ⟨hf⟩).trans (Ig ⟨hg⟩)
    | tensor_left hf If => simp [prop_tensor_iff, If ⟨hf⟩]
    | tensor_right hf If => simp [prop_tensor_iff, If ⟨hf⟩]
    | base h => cases h <;> simp [prop_tensor_iff, prop_id, and_assoc]

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
  prop_eqv_iff : ∀(X Y : C) [SymmEqv X Y], P X ↔ P Y

theorem RespectsSymm.mk' {P : C → Prop}
  (prop_eqv : ∀X Y [SymmEqv X Y], P X → P Y) : RespectsSymm P where
  prop_eqv_iff := λX Y _ => ⟨prop_eqv X Y, have _ := SymmEqv.symm X Y; prop_eqv Y X⟩

instance RespectSymm.respects_assoc {P : C → Prop} [RespectsSymm P] : RespectsAssoc P where
  prop_eqv_iff := λX Y _ => RespectsSymm.prop_eqv_iff X Y

instance StrongPredicate.respects_symm {P : C → Prop} [StrongPredicate P]
  : RespectsSymm P where
  prop_eqv_iff := λX Y ⟨h⟩ => by
    induction h with
    | refl => rfl
    | trans hf hg If Ig => exact (If ⟨hf⟩).trans (Ig ⟨hg⟩)
    | tensor_left hf If => simp [prop_tensor_iff, If ⟨hf⟩]
    | tensor_right hf If => simp [prop_tensor_iff, If ⟨hf⟩]
    | base h => cases h <;> simp only [prop_tensor_iff, prop_id, and_assoc] <;> simp [and_comm]

theorem prop_symm_eqv_iff {P : C → Prop} [RespectsSymm P] {X Y : C} [SymmEqv X Y]
  : P X ↔ P Y := RespectsSymm.prop_eqv_iff X Y

theorem prop_symm_eqv {P : C → Prop} [RespectsSymm P] {X Y : C} [SymmEqv X Y]
  : P X → P Y := prop_symm_eqv_iff.mp

-- TODO: RespectsCentralIso ==> RespectsSymm
-- and therefore RespectsIso ==> RespectsCentralIso ==> RespectsSymm ==> RespectsAssoc

end Monoidal
