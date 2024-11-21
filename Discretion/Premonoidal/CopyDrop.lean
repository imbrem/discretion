import Discretion.Premonoidal.Braided
import Discretion.Premonoidal.Predicate.Basic
import Discretion.Premonoidal.Property.Braided
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

variable {C : Type u} [Category C]

class RelevantAffineStruct (C : Type u) [Category C]
  where
  relevant : C → Prop
  affine : C → Prop

section RelevantAffineStruct

variable [RelevantAffineStruct C]

class IsRelevant (X : C) : Prop where
  relevant : RelevantAffineStruct.relevant X

class IsAffine (X : C) : Prop where
  affine : RelevantAffineStruct.affine X

class IsIntuitionistic (X : C) extends IsRelevant X, IsAffine X : Prop

instance {X : C} [IsRelevant X] [IsAffine X] : IsIntuitionistic X := ⟨⟩

class AffineCat (C : Type u) [Category C] [RelevantAffineStruct C] : Prop where
  allAffine : ∀ (X : C), IsAffine X

instance IsAffine.instAffineCat [AffineCat C] {X : C} : IsAffine X := AffineCat.allAffine X

class RelevantCat (C : Type u) [Category C] [RelevantAffineStruct C] : Prop where
  allRelevant : ∀ (X : C), IsRelevant X

instance IsRelevant.instRelevantCat [RelevantCat C] {X : C} : IsRelevant X
  := RelevantCat.allRelevant X

class IntuitionisticCat (C : Type u) [Category C] [RelevantAffineStruct C]
  extends AffineCat C, RelevantCat C : Prop

instance [AffineCat C] [RelevantCat C] : IntuitionisticCat C := ⟨⟩

variable [MonoidalCategoryStruct C]

instance IsRelevant.instUnit [MonoidalPredicate' (IsRelevant (C := C))] : IsRelevant (𝟙_ C)
  := prop_id

instance IsRelevant.instTensor [MonoidalPredicate' (IsRelevant (C := C))]
  {X Y : C} [hX : IsRelevant X] [hY : IsRelevant Y] : IsRelevant (X ⊗ Y)
  := prop_tensor hX hY

instance IsAffine.instUnit [MonoidalPredicate' (IsAffine (C := C))] : IsAffine (𝟙_ C)
  := prop_id

instance IsAffine.instTensor [MonoidalPredicate' (IsAffine (C := C))]
  {X Y : C} [hX : IsAffine X] [hY : IsAffine Y] : IsAffine (X ⊗ Y)
  := prop_tensor hX hY

end RelevantAffineStruct

class CopyDropStruct (C : Type u) [Category C] [MonoidalCategoryStruct C]
  extends RelevantAffineStruct C where
  copy : ∀ (X : C) [IsRelevant X], (X ⟶ X ⊗ X)
  drop : ∀ (X : C) [IsAffine X], (X ⟶ 𝟙_ C)

namespace Monoidal

scoped notation "Δ_" => CopyDropStruct.copy

scoped notation "!_" => CopyDropStruct.drop

end Monoidal

variable [MonoidalCategoryStruct C] [CopyDropStruct C]

class Copyable {X Y : C} (f : X ⟶ Y) where
  copy_hom : [IsRelevant X] → [IsRelevant Y] → f ≫ Δ_ Y = Δ_ X ≫ (f ⊗ f)

class RelHom {X Y : C} (f : X ⟶ Y) extends Copyable f, Central f : Prop

instance {X Y : C} {f : X ⟶ Y} [Copyable f] [Central f] : RelHom f := ⟨⟩

class Droppable {X Y : C} (f : X ⟶ Y) where
  drop_hom : [IsAffine X] → [IsAffine Y] → f ≫ !_ Y = !_ X

class Discardable {X Y : C} (f : X ⟶ Y) extends Droppable f where
  copy_drop_left_res : [IsRelevant X] → [IsAffine Y] → Δ_ X ≫ (f ≫ !_ Y) ▷ X = (λ_ X).inv

class AffHom {X Y : C} (f : X ⟶ Y) extends Discardable f, Central f : Prop

instance {X Y : C} {f : X ⟶ Y} [Discardable f] [Central f] : AffHom f := ⟨⟩

class PureHom {X Y : C} (f : X ⟶ Y) extends Copyable f, Discardable f, Central f : Prop

instance {X Y : C} {f : X ⟶ Y} [Copyable f] [Discardable f] [Central f] : PureHom f := ⟨⟩

namespace Monoidal

theorem copy_hom {X Y : C} [IsRelevant X] [IsRelevant Y] (f : X ⟶ Y) [Copyable f]
  : f ≫ Δ_ Y = Δ_ X ≫ (f ⊗ f) := Copyable.copy_hom

@[simp]
theorem drop_hom {X Y : C} [IsAffine X] [IsAffine Y] (f : X ⟶ Y) [Droppable f]
  : f ≫ !_ Y = !_ X := Droppable.drop_hom

@[simp]
theorem copy_drop_left_res {X Y : C} [IsRelevant X] [IsAffine Y] (f : X ⟶ Y) [Discardable f]
  : Δ_ X ≫ (f ≫ !_ Y) ▷ X = (λ_ X).inv := Discardable.copy_drop_left_res

variable [IsPremonoidal C]

theorem copy_hom_ltimes {X Y : C} [IsRelevant X] [IsRelevant Y] (f : X ⟶ Y) [Copyable f]
  : f ≫ Δ_ Y = Δ_ X ≫ f ⋉ f := by simp [copy_hom, tensorHom_def]

end Monoidal

open MorphismProperty

class CopyDrop (C : Type u)
  [Category C] [MonoidalCategoryStruct C] [CopyDropStruct C] [BraidedCategoryStruct C]
  : Prop where
  relevant_monoidal : MonoidalPredicate' (IsRelevant (C := C))
  affine_monoidal : MonoidalPredicate' (IsAffine (C := C))
  relevant_assoc : RespectsAssoc (IsRelevant (C := C))
  affine_assoc : RespectsAssoc (IsAffine (C := C))
  affine_of_relevant : ∀ (X : C) [IsRelevant X] [IsAffine (X ⊗ X)], IsAffine X
  central_copy : ∀ (X : C) [IsRelevant X], Central (Δ_ X)
  central_drop : ∀ (X : C) [IsAffine X], Central (!_ X)
  drop_unit : !_ (𝟙_ C) = 𝟙 (𝟙_ C)
  pure_braided : ∀ {X Y : C} {f : X ⟶ Y}, braided C f → PureHom f
  commutative : ∀ (X : C) [IsRelevant X], Δ_ X ≫ σ_ X X = Δ_ X
  associative : ∀ (X : C) [IsRelevant X], Δ_ X ≫ Δ_ X ▷ X ≫ (α_ X X X).hom = Δ_ X ≫ X ◁ Δ_ X
  tensor_copy : ∀ (X Y : C) [IsRelevant X] [IsRelevant Y],
    (Δ_ X ⊗ Δ_ Y) ≫ swap_ll_rr X X Y Y = Δ_ (X ⊗ Y)
  tensor_drop : ∀ (X Y : C) [IsAffine X] [IsAffine Y], (!_ X ⊗ !_ Y) ≫ (λ_ _).hom = !_ (X ⊗ Y)

namespace Monoidal

variable [BraidedCategoryStruct C] [CopyDrop C]

instance MonoidalPredicate'.instRelevantMonoidal : MonoidalPredicate' (IsRelevant (C := C))
  := CopyDrop.relevant_monoidal

instance MonoidalPredicate'.instAffineMonoidal : MonoidalPredicate' (IsAffine (C := C))
  := CopyDrop.affine_monoidal

theorem affine_of_relevant (X : C) [IsRelevant X] [IsAffine (X ⊗ X)] : IsAffine X
  := CopyDrop.affine_of_relevant X

@[simp]
theorem drop_unit : !_ (𝟙_ C) = 𝟙 (𝟙_ C) := CopyDrop.drop_unit

theorem pure_braided {X Y : C} {f : X ⟶ Y} (h : braided C f) : PureHom f := CopyDrop.pure_braided h

@[simp]
instance pure_id (X : C) : PureHom (𝟙 X) := pure_braided (by simp)

@[simp]
instance pure_associator (X Y Z : C) : PureHom (α_ X Y Z).hom := pure_braided (by simp)

@[simp]
instance pure_leftUnitor (X : C) : PureHom (λ_ X).hom := pure_braided (by simp)

@[simp]
instance pure_rightUnitor (X : C) : PureHom (ρ_ X).hom := pure_braided (by simp)

@[simp]
instance pure_symmetry (X Y : C) : PureHom (σ_ X Y) := pure_braided (by simp)

@[simp]
theorem copy_comm (X : C) [IsRelevant X] : Δ_ X ≫ σ_ X X = Δ_ X := CopyDrop.commutative X

@[simp]
theorem copy_comm_inv (X : C) [IsRelevant X] : Δ_ X ≫ σ_' X X = Δ_ X
  := (cancel_mono (σ_ X X)).mp (by simp)

@[reassoc]
theorem copy_assoc (X : C) [IsRelevant X] : Δ_ X ≫ Δ_ X ▷ X ≫ (α_ X X X).hom = Δ_ X ≫ X ◁ Δ_ X
  := CopyDrop.associative X

@[reassoc]
theorem copy_assoc_inv (X : C) [IsRelevant X]
  : Δ_ X ≫ X ◁ Δ_ X ≫ (α_ X X X).inv = Δ_ X ≫ Δ_ X ▷ X
  := (cancel_mono (α_ X X X).hom).mp (by simp [copy_assoc])

theorem tensor_copy (X Y : C) [IsRelevant X] [IsRelevant Y]
  : (Δ_ X ⊗ Δ_ Y) ≫ swap_ll_rr X X Y Y = Δ_ (X ⊗ Y) := CopyDrop.tensor_copy X Y

theorem tensor_drop (X Y : C) [IsAffine X] [IsAffine Y]
  : (!_ X ⊗ !_ Y) ≫ (λ_ _).hom = !_ (X ⊗ Y) := CopyDrop.tensor_drop X Y

instance discardable_drop (X : C) [IsAffine X] : Discardable (!_ X) where
  drop_hom := by simp
  copy_drop_left_res := by intros; convert (pure_id X).copy_drop_left_res using 1; simp

@[reassoc, simp]
theorem copy_drop_left {X : C} [IsRelevant X] [IsAffine X]
  : Δ_ X ≫ !_ X ▷ X = (λ_ X).inv := by convert copy_drop_left_res (!_ X) using 1; simp

variable [IsPremonoidal C]

@[simp]
theorem copy_unit : Δ_ (𝟙_ C) = (λ_ (𝟙_ C)).inv := by convert copy_drop_left (X := 𝟙_ C); simp

@[simp]
instance pure_drop (X : C) [IsAffine X] : PureHom (!_ X) where
  toCentral := CopyDrop.central_drop X
  copy_hom := by intros; simp only [
    copy_unit, tensorHom_def, ←Category.assoc, copy_drop_left, <-leftUnitor_inv_naturality (X := X)
  ]

@[reassoc]
theorem copy3_assoc (X : C) [IsRelevant X]
  : Δ_ X ≫ Δ_ X ▷ X ≫ Δ_ X ▷ X ▷ X ≫ (α_ _ _ _).hom
  = Δ_ X ≫ Δ_ X ▷ X ≫ (X ⊗ X) ◁ Δ_ X
  := by
  have h := CopyDrop.central_copy X
  rw [
    associator_naturality_right, <-Category.assoc, <-Category.assoc, Category.assoc (f := Δ_ X),
    copy_assoc, Category.assoc, left_exchange
  ]

theorem copy_132 (X : C) [IsRelevant X]
  : Δ_ X ≫ Δ_ X ▷ X ≫ (α_ X X X).hom ≫ X ◁ (σ_ X X) = Δ_ X ≫ X ◁ Δ_ X
  := by rw [
    <-Category.assoc, <-Category.assoc, Category.assoc (f := Δ_ X), copy_assoc, Category.assoc,
    <-whiskerLeft_comp, copy_comm
  ]

theorem copy_213 (X : C) [IsRelevant X]
  : Δ_ X ≫ X ◁ Δ_ X ≫ (α_ X X X).inv ≫ (σ_ X X) ▷ X = Δ_ X ≫ Δ_ X ▷ X
  := by rw [
    <-Category.assoc, <-Category.assoc, Category.assoc (f := Δ_ X), copy_assoc_inv, Category.assoc,
    <-whiskerRight_comp, copy_comm
  ]

instance droppable_copy (X : C) [IsRelevant X] : Droppable (Δ_ X) where
  drop_hom := by
    intros
    simp only [← tensor_drop, tensorHom_def, ← Category.assoc, copy_drop_left]
    simp only [Category.assoc, leftUnitor_naturality, <-tensor_drop, tensorHom_def]
    rw [<-Category.assoc, Iso.inv_hom_id, Category.id_comp]

@[simp]
instance pure_copy (X : C) [IsRelevant X] : PureHom (Δ_ X) where
  toCentral := CopyDrop.central_copy X
  copy_hom := by
    intros
    rw [<-tensor_copy, swap_ll_rr, tensorHom_def]
    apply (cancel_mono (α_ _ _ _).hom).mp
    simp only [whiskerLeft_comp, Category.assoc, Iso.inv_hom_id, Category.comp_id,
      associator_naturality_left, copy_assoc_assoc]
    apply (cancel_mono (X ◁ (α_ X X X).inv)).mp
    simp only [← whiskerLeft_comp, Category.assoc, Iso.hom_inv_id, Category.comp_id, copy_assoc_inv]
    apply (cancel_mono (X ◁ (σ_' X X) ▷ X)).mp
    simp only [Category.assoc, ← whiskerLeft_comp, ← whiskerRight_comp, Iso.hom_inv_id,
      id_whiskerRight, Category.comp_id, copy_comm_inv]
    apply (cancel_mono (X ◁ (α_ X X X).hom)).mp
    simp only [Category.assoc, ← whiskerLeft_comp, Iso.inv_hom_id, whiskerLeft_id, Category.comp_id,
      copy_assoc]
    apply (cancel_mono (α_ _ _ _).inv).mp
    simp [associator_inv_naturality_left, copy_assoc_inv_assoc]
  copy_drop_left_res := by intros; have h := affine_of_relevant X; rw [drop_hom, copy_drop_left]

variable [IsBraided C]

theorem copy_hom_rtimes {X Y : C} [IsRelevant X] [IsRelevant Y] (f : X ⟶ Y) [Copyable f]
  : f ≫ Δ_ Y = Δ_ X ≫ f ⋊ f := calc
  _ = (f ≫ Δ_ Y) ≫ σ_ Y Y := by simp
  _ = Δ_ X ≫ (f ⋉ f) ≫ σ_ Y Y := by simp [copy_hom f, tensorHom_def]
  _ = _ := by rw [ltimes_braiding, <-Category.assoc, copy_comm]

theorem copy_swap {X Y : C} [IsRelevant X] [IsRelevant Y] (f : X ⟶ Y) [Copyable f]
  : Δ_ X ≫ f ⋉ f = Δ_ X ≫ f ⋊ f := by rw [<-copy_hom_ltimes, copy_hom_rtimes]

-- TODO: copy_drop_right

end Monoidal
