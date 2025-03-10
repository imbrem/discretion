import Discretion.Monoidal.Braided.Basic
import Discretion.Monoidal.CoherenceLemmas
import Discretion.Premonoidal.Category

namespace CategoryTheory

open scoped MonoidalCategory
open PremonoidalCategory MonoidalCategory' BraidedCategory'

namespace MonoidalCategory'

variable {C : Type u} [Category C] [PremonoidalCategory C]

def assoc_inner
  (X Y Z W : C) : (X ⊗ Y) ⊗ (Z ⊗ W) ≅ X ⊗ (Y ⊗ Z) ⊗ W
  := ⟨
    (α_ X Y (Z ⊗ W)).hom ≫ X ◁ (α_ Y Z W).inv,
    X ◁ (α_ Y Z W).hom ≫ (α_ X Y (Z ⊗ W)).inv,
    by simp [<-whiskerLeft_comp_assoc],
    by simp [<-whiskerLeft_comp]
  ⟩

scoped notation "αi_" => assoc_inner

@[simp]
instance assoc_inner_central (X Y Z W : C) : Central (αi_ X Y Z W).hom := by
  simp only [assoc_inner]; infer_instance
section BraidedCategory

variable [BraidedCategory' C]

def swap_inner
  (X Y Z W : C) : (X ⊗ Y) ⊗ (Z ⊗ W) ≅ (X ⊗ Z) ⊗ (Y ⊗ W)
  := ⟨
    (αi_ X Y Z W).hom
      ≫ X ◁ (β'_ Y Z).hom ▷ W
      ≫ (αi_ X Z Y W).inv,
    (αi_ X Z Y W).hom
      ≫ X ◁ (β'_ Y Z).inv ▷ W
      ≫ (αi_ X Y Z W).inv,
    by
      simp only [Category.assoc, Iso.inv_hom_id_assoc, assoc_inner]
      apply (cancel_epi (α_ X Y (Z ⊗ W)).inv).mp
      apply (cancel_mono (α_ X Y (Z ⊗ W)).hom).mp
      simp only [Iso.inv_hom_id_assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id, ←
        whiskerLeft_comp, Iso.hom_inv_id_assoc]
      rw [<-Category.assoc _ _ (α_ _ _ _).hom, <-comp_whiskerRight]
      simp,
    by
      simp only [Category.assoc, Iso.inv_hom_id_assoc, assoc_inner]
      apply (cancel_epi (α_ X Z (Y ⊗ W)).inv).mp
      apply (cancel_mono (α_ X Z (Y ⊗ W)).hom).mp
      simp only [Iso.inv_hom_id_assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id, ←
        whiskerLeft_comp, Iso.hom_inv_id_assoc]
      rw [<-Category.assoc _ _ (α_ _ _ _).hom, <-comp_whiskerRight]
      simp
  ⟩

scoped notation "βi_" => swap_inner

@[simp]
instance swap_inner_central (X Y Z W : C) : Central (βi_ X Y Z W).hom := by
  simp only [swap_inner]; infer_instance

@[reassoc]
theorem assoc_inner_swap_inner (X Y Z W : C)
  : (αi_ X Y Z W).inv ≫ (βi_ X Y Z W).hom
  = X ◁ (β'_ Y Z).hom ▷ W ≫ (αi_ X Z Y W).inv := by simp [swap_inner]

@[reassoc]
theorem assoc_inner_swap_inner_inv (X Y Z W : C)
  : (αi_ X Z Y W).inv ≫ (βi_ X Y Z W).inv
  = X ◁ (β'_ Y Z).inv ▷ W ≫ (αi_ X Y Z W).inv := by simp [swap_inner]

@[reassoc]
theorem swap_inner_assoc_inner (X Y Z W : C)
  : (βi_ X Y Z W).hom ≫ (αi_ X Z Y W).hom
  = (αi_ X Y Z W).hom ≫ X ◁ (β'_ Y Z).hom ▷ W := by simp [swap_inner]

@[reassoc]
theorem swap_inner_inv_assoc_inner (X Y Z W : C)
  : (βi_ X Y Z W).inv ≫ (αi_ X Y Z W).hom
  = (αi_ X Z Y W).hom ≫ X ◁ (β'_ Y Z).inv ▷ W := by simp [swap_inner]

@[reassoc (attr := simp)]
theorem swap_inner_leftUnitor {X Y Z : C}
  : (X ⊗ Y) ◁ (λ_ Z).inv ≫ (βi_ X Y (𝟙_ C) Z).hom = (α_ X Y Z).hom ≫ (ρ_ X).inv ▷ (Y ⊗ Z)
  := calc
  _ = (α_ X Y Z).hom ≫ X ◁ ((ρ_ _).inv ≫ (β'_ _ _).hom ≫ (λ_ _).hom) ▷ Z ≫ (ρ_ _).inv ▷ _
    := by simp only [swap_inner, assoc_inner]; premonoidal
  _ = _ := by rw [rightUnitor_inv_braiding'_assoc Y]; premonoidal

@[reassoc]
theorem swap_inner_ltimes_leftUnitor {X Y Z W : C} (f : X ⟶ Y ⊗ Z)
  : (f ⋉ (λ_ W).inv) ≫ (βi_ Y Z (𝟙_ C) W).hom = f ▷ W ≫ (α_ Y Z W).hom ≫ (ρ_ Y).inv ▷ (Z ⊗ W)
  := by simp only [Category.assoc, swap_inner_leftUnitor]

@[reassoc]
theorem swap_inner_tensor_leftUnitor {X Y Z W : C} (f : X ⟶ Y ⊗ Z)
  : (f ⊗ (λ_ W).inv) ≫ (βi_ Y Z (𝟙_ C) W).hom = f ▷ W ≫ (α_ Y Z W).hom ≫ (ρ_ Y).inv ▷ (Z ⊗ W)
  := by simp only [tensorHom_def, swap_inner_ltimes_leftUnitor]

@[reassoc]
theorem swap_inner_rtimes_leftUnitor {X Y Z W : C} (f : X ⟶ Y ⊗ Z)
  : (f ⋊ (λ_ W).inv) ≫ (βi_ Y Z (𝟙_ C) W).hom = f ▷ W ≫ (α_ Y Z W).hom ≫ (ρ_ Y).inv ▷ (Z ⊗ W)
  := by simp only [<-PremonoidalCategory.Central.right_exchange, swap_inner_ltimes_leftUnitor]

@[reassoc]
theorem swap_inner_naturality_left {X Y Y' Z W : C} (f : Y ⟶ Y')
  : (X ◁ f) ▷ (Z ⊗ W) ≫ (βi_ X Y' Z W).hom = (βi_ X Y Z W).hom ≫ (X ⊗ Z) ◁ (f ▷ W)
  := calc
  _ = (αi_ _ _ _ _).hom ≫ X ◁ (f ▷ Z ≫ (β'_ _ _).hom) ▷ W ≫ (αi_ _ _ _ _).inv
    := by simp only [swap_inner, assoc_inner]; premonoidal
  _ = _
    := by simp only [braiding_naturality_left, swap_inner, assoc_inner]; premonoidal

@[reassoc]
theorem swap_inner_naturality_right {X Y Z Z' W : C} (f : Z ⟶ Z')
  : (X ⊗ Y) ◁ (f ▷ W) ≫ (βi_ X Y Z' W).hom = (βi_ X Y Z W).hom ≫ (X ◁ f) ▷ (Y ⊗ W)
  := calc
  _ = (αi_ _ _ _ _).hom ≫ X ◁ (Y ◁ f ≫ (β'_ _ _).hom) ▷ W ≫ (αi_ _ _ _ _).inv
    := by simp only [swap_inner, assoc_inner]; premonoidal
  _ = _
    := by simp only [braiding_naturality_right, swap_inner, assoc_inner]; premonoidal

@[reassoc]
theorem swap_inner_naturality_outer_left {X X' Y Z W : C} (f : X ⟶ X')
  : (f ▷ Y) ▷ (Z ⊗ W) ≫ (βi_ X' Y Z W).hom = (βi_ X Y Z W).hom ≫ (f ▷ Z) ▷ (Y ⊗ W)
  := by calc
  _ = (αi_ _ _ _ _).hom ≫ f ▷ _ ≫ X' ◁ (β'_ _ _).hom ▷ W ≫ (αi_ _ _ _ _).inv
    := by simp only [swap_inner, assoc_inner]; premonoidal
  _ = _
    := by rw [Central.right_exchange_assoc]; simp only [swap_inner, assoc_inner]; premonoidal

@[reassoc]
theorem swap_inner_naturality_outer_right {X Y Z W W' : C} (f : W ⟶ W')
  : (X ⊗ Y) ◁ (Z ◁ f) ≫ (βi_ X Y Z W').hom = (βi_ X Y Z W).hom ≫ (X ⊗ Z) ◁ (Y ◁ f)
  := by calc
  _ = (αi_ _ _ _ _).hom ≫ X ◁ (_ ◁ f ≫ (β'_ Y Z).hom ▷ W') ≫ (αi_ _ _ _ _).inv
    := by simp only [swap_inner, assoc_inner]; premonoidal
  _ = _
    := by
    simp only [<-Central.left_exchange (f := (β'_ Y Z).hom) (g := f), swap_inner, assoc_inner]
    premonoidal

@[reassoc]
theorem swap_inner_naturality_tensor_middle {X₁ X₂ X₃ X₄ Y₁ Y₂ Y₃ Y₄ : C}
  (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (f₃ : X₃ ⟶ Y₃) (f₄ : X₄ ⟶ Y₄)
  [Central f₂] [Central f₃]
  : ((f₁ ⊗ f₂) ⊗ (f₃ ⊗ f₄)) ≫ (βi_ Y₁ Y₂ Y₃ Y₄).hom
  = (βi_ X₁ X₂ X₃ X₄).hom ≫ ((f₁ ⊗ f₃) ⊗ (f₂ ⊗ f₄))
  := calc
  _ = (f₁ ▷ _) ▷ _ ≫ _ ◁ (_ ◁ f₄) ≫ (_ ◁ f₂) ▷ _ ≫ _ ◁ (f₃ ▷ _) ≫ (βi_ Y₁ Y₂ Y₃ Y₄).hom
    := by rw [
      tensorHom_def (f := f₁),
      tensorHom_def_of_left (f := f₃),
      tensorHom_def, Category.assoc,
      comp_whiskerRight, PremonoidalCategory.whiskerLeft_comp,
      Category.assoc, Category.assoc,
      Central.left_exchange_assoc
    ]
  _ = _
    := by
    simp only [
      swap_inner_naturality_left_assoc,
      swap_inner_naturality_right,
      swap_inner_naturality_outer_left_assoc,
      swap_inner_naturality_outer_right_assoc]
    rw [
      tensorHom_def (f := f₁),
      tensorHom_def_of_left (f := f₂),
      tensorHom_def, comp_whiskerRight, Category.assoc, PremonoidalCategory.whiskerLeft_comp,
      Central.left_exchange_assoc (f := _ ◁ f₃),
    ]
    congr 3
    apply (Central.left_exchange _).symm

@[simp]
theorem swap_inner_tensorUnit_right
  {X Y Z : C}
  : (βi_ X Y (𝟙_ C) Z).hom = (α_ _ _ _).hom ≫ X ◁ Y ◁ (λ_ Z).hom ≫ (ρ_ X).inv ▷ _
  := by simp [swap_inner, assoc_inner]; premonoidal_coherence

@[simp]
theorem swap_inner_tensorUnit_left
  {X Y Z : C}
  : (βi_ X (𝟙_ C) Y Z).hom = (ρ_ _).hom ▷ _ ≫ (α_ _ _ _).inv ≫ _ ◁ (λ_ _).inv
  := by simp [swap_inner, assoc_inner]; premonoidal_coherence

@[reassoc]
theorem right_leftUnitor_inv_swap_inner
  {X Y Z : C} :
    (X ⊗ Y) ◁ (λ_ Z).inv ≫ (βi_ X Y (𝟙_ C) Z).hom
    = (α_ X Y Z).hom ≫ (ρ_ X).inv ▷ (Y ⊗ Z)
  := by simp; premonoidal_coherence

end BraidedCategory

section SymmetricCategory

variable [SymmetricCategory' C]

theorem swap_inner_eq_inv
  (X Y Z W : C) : (βi_ X Y Z W).hom = (βi_ X Z Y W).inv := by
  simp [swap_inner, SymmetricCategory'.braiding_swap_eq_inv_braiding]

@[simp, reassoc (attr := simp)]
theorem swap_inner_swap_inner
  (X Y Z W : C) : (βi_ X Y Z W).hom ≫ (βi_ X Z Y W).hom = 𝟙 _
  := by rw [swap_inner_eq_inv, Iso.inv_hom_id]

@[simp, reassoc (attr := simp)]
theorem swap_inner_swap_inner_inv
  (X Y Z W : C) : (βi_ X Y Z W).inv ≫ (βi_ X Z Y W).inv = 𝟙 _
  := by rw [<-swap_inner_eq_inv, Iso.hom_inv_id]

end SymmetricCategory

end MonoidalCategory'

end CategoryTheory
