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
