import Discretion.Premonoidal.Braided

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

class CopyDrop (C : Type u) [Category C] [MonoidalCategoryStruct C] [BraidedCategoryStruct C]
  where
  copy : ∀ (X : C), X ⟶ X ⊗ X
  drop : ∀ (X : C), X ⟶ 𝟙_ C
  central_copy : ∀ (X : C), Monoidal.Central (copy X)
  central_drop : ∀ (X : C), Monoidal.Central (drop X)
  commutative : ∀ (X : C), copy X ≫ σ_ X X = copy X
  associative : ∀ (X : C), copy X ≫ copy X ▷ X ≫ (α_ X X X).hom = copy X ≫ X ◁ copy X
  unit_right : ∀ (X : C), copy X ≫ X ◁ drop X = (ρ_ X).inv
  tensor_copy : ∀ (X Y : C), (copy X ⊗ copy Y) ≫ swap_ll_rr X X Y Y = copy (X ⊗ Y)
  tensor_drop : ∀ (X Y : C), (drop X ⊗ drop Y) ≫ (λ_ _).hom = drop (X ⊗ Y)

namespace Monoidal

  scoped notation "Δ_" => CopyDrop.copy

  scoped notation "!_" => CopyDrop.drop

  variable {C : Type u}
    [Category C] [MonoidalCategoryStruct C] [BraidedCategoryStruct C] [CopyDrop C]

  @[simp]
  instance central_copy (X : C) : Monoidal.Central (Δ_ X) := CopyDrop.central_copy X

  @[simp]
  instance central_drop (X : C) : Monoidal.Central (!_ X) := CopyDrop.central_drop X

  @[simp]
  theorem commutative (X : C) : Δ_ X ≫ σ_ X X = Δ_ X := CopyDrop.commutative X

  theorem associative (X : C) : Δ_ X ≫ Δ_ X ▷ X ≫ (α_ X X X).hom = Δ_ X ≫ X ◁ Δ_ X
    := CopyDrop.associative X

  @[simp]
  theorem unit_right (X : C) : Δ_ X ≫ X ◁ !_ X = (ρ_ X).inv := CopyDrop.unit_right X

  theorem tensor_copy (X Y : C) : (Δ_ X ⊗ Δ_ Y) ≫ swap_ll_rr X X Y Y = Δ_ (X ⊗ Y)
    := CopyDrop.tensor_copy X Y

  theorem tensor_drop (X Y : C) : (!_ X ⊗ !_ Y) ≫ (λ_ _).hom = !_ (X ⊗ Y)
    := CopyDrop.tensor_drop X Y

  -- @[simp]
  -- theorem unit_left (X : C) : Δ_ X ≫ !_ X ▷ X = (λ_ X).inv := sorry

  def pil (X Y : C) : X ⊗ Y ⟶ X := (X ◁ !_ Y) ≫ (ρ_ X).hom

  def pir (X Y : C) : X ⊗ Y ⟶ Y := (!_ X ▷ Y) ≫ (λ_ Y).hom

  theorem copy_pil (X : C) : Δ_ X ≫ pil X X = 𝟙 X := by simp [pil, <-Category.assoc]

  -- theorem copy_pir (X : C) : Δ_ X ≫ pir X X = 𝟙 X := by simp [pir, <-Category.assoc]

  class Copyable {X Y : C} (f : X ⟶ Y) where
    copy_hom : f ≫ Δ_ Y = Δ_ X ≫ (f ⊗ f)

  theorem copy_hom {X Y : C} (f : X ⟶ Y) [Copyable f] : f ≫ Δ_ Y = Δ_ X ≫ (f ⊗ f)
    := Copyable.copy_hom

  class Droppable {X Y : C} (f : X ⟶ Y) where
    drop_hom : f ≫ !_ Y = !_ X

  theorem drop_hom {X Y : C} (f : X ⟶ Y) [Droppable f] : f ≫ !_ Y = !_ X
    := Droppable.drop_hom

  class Nonlinear {X Y : C} (f : X ⟶ Y) extends Copyable f, Droppable f, Central f

  instance {X Y : C} {f : X ⟶ Y} [Copyable f] [Droppable f] [Central f] : Nonlinear f := ⟨⟩

end Monoidal
