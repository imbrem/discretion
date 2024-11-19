import Discretion.Premonoidal.Braided
import Discretion.Premonoidal.Predicate
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

open MonoidalPredicate'

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

class Discardable {X Y : C} (f : X ⟶ Y) where
  drop_hom : [IsAffine X] → [IsAffine Y] → f ≫ !_ Y = !_ X
  copy_drop_left : [IsRelevant X] → [IsAffine Y] → Δ_ X ≫ (f ≫ !_ Y) ▷ X = (λ_ X).inv

class AffHom {X Y : C} (f : X ⟶ Y) extends Discardable f, Central f : Prop

instance {X Y : C} {f : X ⟶ Y} [Discardable f] [Central f] : AffHom f := ⟨⟩

class PureHom {X Y : C} (f : X ⟶ Y) extends Copyable f, Discardable f, Central f : Prop

instance {X Y : C} {f : X ⟶ Y} [Copyable f] [Discardable f] [Central f] : PureHom f := ⟨⟩

class CopyDrop (C : Type u)
  [Category C] [MonoidalCategoryStruct C] [CopyDropStruct C] [BraidedCategoryStruct C]
  : Prop where
  relevantMonoidal : MonoidalPredicate' (IsRelevant (C := C))
  affineMonoidal : MonoidalPredicate' (IsAffine (C := C))
  pure_copy : ∀ (X : C) [IsRelevant X], PureHom (Δ_ X)
  pure_drop : ∀ (X : C) [IsAffine X], PureHom (!_ X)
  pure_associator : ∀ (X Y Z : C), PureHom (α_ X Y Z).hom
  pure_leftUnitor : ∀ (X : C), PureHom (λ_ X).hom
  pure_rightUnitor : ∀ (X : C), PureHom (ρ_ X).hom
  pure_symmetry : ∀ (X Y : C), PureHom (σ_ X Y)
  commutative : ∀ (X : C) [IsRelevant X], Δ_ X ≫ σ_ X X = Δ_ X
  associative : ∀ (X : C) [IsRelevant X], Δ_ X ≫ Δ_ X ▷ X ≫ (α_ X X X).hom = Δ_ X ≫ X ◁ Δ_ X
  tensor_copy : ∀ (X Y : C) [IsRelevant X] [IsRelevant Y],
    (Δ_ X ⊗ Δ_ Y) ≫ swap_ll_rr X X Y Y = Δ_ (X ⊗ Y)
  tensor_drop : ∀ (X Y : C) [IsAffine X] [IsAffine Y], (!_ X ⊗ !_ Y) ≫ (λ_ _).hom = !_ (X ⊗ Y)

-- namespace Monoidal

--   scoped notation "Δ_" => CopyDrop.copy

--   scoped notation "!_" => CopyDrop.drop

--   variable {C : Type u}
--     [Category C] [MonoidalCategoryStruct C] [BraidedCategoryStruct C] [CopyDrop C]

--   @[simp]
--   instance central_copy (X : C) : Monoidal.Central (Δ_ X) := CopyDrop.central_copy X

--   @[simp]
--   instance central_drop (X : C) : Monoidal.Central (!_ X) := CopyDrop.central_drop X

--   @[simp]
--   theorem commutative (X : C) : Δ_ X ≫ σ_ X X = Δ_ X := CopyDrop.commutative X

--   theorem associative (X : C) : Δ_ X ≫ Δ_ X ▷ X ≫ (α_ X X X).hom = Δ_ X ≫ X ◁ Δ_ X
--     := CopyDrop.associative X

--   @[simp]
--   theorem unit_right (X : C) : Δ_ X ≫ X ◁ !_ X = (ρ_ X).inv := CopyDrop.unit_right X

--   theorem tensor_copy (X Y : C) : (Δ_ X ⊗ Δ_ Y) ≫ swap_ll_rr X X Y Y = Δ_ (X ⊗ Y)
--     := CopyDrop.tensor_copy X Y

--   theorem tensor_drop (X Y : C) : (!_ X ⊗ !_ Y) ≫ (λ_ _).hom = !_ (X ⊗ Y)
--     := CopyDrop.tensor_drop X Y

--   -- @[simp]
--   -- theorem unit_left (X : C) : Δ_ X ≫ !_ X ▷ X = (λ_ X).inv := sorry

--   def pil (X Y : C) : X ⊗ Y ⟶ X := (X ◁ !_ Y) ≫ (ρ_ X).hom

--   def pir (X Y : C) : X ⊗ Y ⟶ Y := (!_ X ▷ Y) ≫ (λ_ Y).hom

--   theorem copy_pil (X : C) : Δ_ X ≫ pil X X = 𝟙 X := by simp [pil, <-Category.assoc]

--   -- theorem copy_pir (X : C) : Δ_ X ≫ pir X X = 𝟙 X := by simp [pir, <-Category.assoc]

--   class Copyable {X Y : C} (f : X ⟶ Y) where
--     copy_hom : f ≫ Δ_ Y = Δ_ X ≫ (f ⊗ f)

--   theorem copy_hom {X Y : C} (f : X ⟶ Y) [Copyable f] : f ≫ Δ_ Y = Δ_ X ≫ (f ⊗ f)
--     := Copyable.copy_hom

--   class Droppable {X Y : C} (f : X ⟶ Y) where
--     drop_hom : f ≫ !_ Y = !_ X

--   theorem drop_hom {X Y : C} (f : X ⟶ Y) [Droppable f] : f ≫ !_ Y = !_ X
--     := Droppable.drop_hom

--   class Nonlinear {X Y : C} (f : X ⟶ Y) extends Copyable f, Droppable f, Central f

--   instance {X Y : C} {f : X ⟶ Y} [Copyable f] [Droppable f] [Central f] : Nonlinear f := ⟨⟩

-- end Monoidal
