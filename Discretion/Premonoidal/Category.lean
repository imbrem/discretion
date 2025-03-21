import Discretion.Monoidal.Category

namespace CategoryTheory

open scoped MonoidalCategory

open MonoidalCategoryStruct PremonoidalCategory

variable {C : Type u} [Category C] [PremonoidalCategory C]

namespace PremonoidalCategory

@[reassoc]
theorem tensor_comp_of_left {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : C}
  (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (g₁ : Y₁ ⟶ Z₁) (g₂ : Y₂ ⟶ Z₂) [Central g₁] :
    (f₁ ≫ g₁) ⊗ (f₂ ≫ g₂) = (f₁ ⊗ f₂) ≫ (g₁ ⊗ g₂)
    := by simp [tensorHom_def, Central.left_exchange_assoc]

@[reassoc]
theorem tensor_comp_of_right {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : C}
  (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (g₁ : Y₁ ⟶ Z₁) (g₂ : Y₂ ⟶ Z₂) [Central f₂] :
    (f₁ ≫ g₁) ⊗ (f₂ ≫ g₂) = (f₁ ⊗ f₂) ≫ (g₁ ⊗ g₂)
    := by simp [tensorHom_def, Central.right_exchange_assoc]

@[reassoc]
theorem tensorHom_def_of_left {X₁ Y₁ X₂ Y₂ : C} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) [Central f] :
    f ⊗ g = X₁ ◁ g ≫ f ▷ Y₂ := by simp [tensorHom_def, Central.left_exchange]

@[reassoc]
theorem tensorHom_def_of_right {X₁ Y₁ X₂ Y₂ : C} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) [Central g] :
    f ⊗ g = X₁ ◁ g ≫ f ▷ Y₂ := by simp [tensorHom_def, Central.right_exchange]

@[reassoc]
theorem left_exchange {X₁ Y₁ X₂ Y₂ : C} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) [Central f] :
    f ▷ X₂ ≫ Y₁ ◁ g = X₁ ◁ g ≫ f ▷ Y₂ := by simp [Central.left_exchange]

@[reassoc]
theorem right_exchange {X₁ Y₁ X₂ Y₂ : C} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) [Central g] :
    f ▷ X₂ ≫ Y₁ ◁ g = X₁ ◁ g ≫ f ▷ Y₂ := by simp [Central.right_exchange]

@[reassoc]
theorem whiskerLeft_swap_of_swap {X₁ Y₁ X₂ Y₂ Z : C} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂)
    (hfg : f ▷ X₂ ≫ Y₁ ◁ g = X₁ ◁ g ≫ f ▷ Y₂)
    : (Z ◁ f) ▷ X₂ ≫ (Z ⊗ Y₁) ◁ g = (Z ⊗ X₁) ◁ g ≫ (Z ◁ f) ▷ Y₂ := by
    rw [<-cancel_mono (f := (α_ _ _ _).hom)]
    simp only [whisker_assoc, tensor_whiskerLeft, Category.assoc, Iso.inv_hom_id_assoc,
      Iso.inv_hom_id, Category.comp_id, Iso.cancel_iso_hom_left]
    simp only [<-PremonoidalCategory.whiskerLeft_comp, hfg]

@[reassoc]
theorem swap_whiskerRight_of_swap {X₁ Y₁ X₂ Y₂ Z : C} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂)
    (hfg : f ▷ X₂ ≫ Y₁ ◁ g = X₁ ◁ g ≫ f ▷ Y₂)
    : f ▷ (X₂ ⊗ Z) ≫ Y₁ ◁ (g ▷ Z) = X₁ ◁ (g ▷ Z) ≫ f ▷ (Y₂ ⊗ Z) := by
    rw [<-cancel_mono (f := (α_ _ _ _).inv)]
    simp only [
        Category.assoc, associator_inv_naturality_left, associator_inv_naturality_middle,
        associator_inv_naturality_left_assoc, associator_inv_naturality_middle_assoc,
        <-comp_whiskerRight, hfg
    ]

end PremonoidalCategory

end CategoryTheory

--TODO: swap_whiskerRight_of_swap
