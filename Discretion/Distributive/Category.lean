import Discretion.Monoidal.Category
import Discretion.ChosenFiniteCoproducts

namespace CategoryTheory

open scoped MonoidalCategory
open MonoidalCategory'

open PremonoidalCategory PremonoidalCategory.Central

open ChosenFiniteCoproducts

variable {C : Type u} [Category C] [CC : ChosenFiniteCoproducts C]

namespace ChosenFiniteCoproducts

@[reassoc]
theorem addHom_comp_addHom {X₁ X₂ X₃ Y₁ Y₂ Y₃ : C}
  (f₁ : X₁ ⟶ X₂) (f₂ : X₂ ⟶ X₃) (g₁ : Y₁ ⟶ Y₂) (g₂ : Y₂ ⟶ Y₃)
  : (f₁ ⊕ₕ g₁) ≫ (f₂ ⊕ₕ g₂) = (f₁ ≫ f₂) ⊕ₕ (g₁ ≫ g₂)
  := by simp [addHom, -desc_comp_inl_inr]

@[reassoc]
theorem addHom_id {X Y : C} : (𝟙 X) ⊕ₕ (𝟙 Y) = 𝟙 (X ⊕ₒ Y) := by
  simp [addHom, -desc_comp_inl_inr]

end ChosenFiniteCoproducts

section MonoidalCategoryStruct

variable [MonoidalCategoryStruct C]

namespace DistributiveCategory

def distl_hom (X Y Z : C) : (X ⊗ Y) ⊕ₒ (X ⊗ Z) ⟶ X ⊗ (Y ⊕ₒ Z)
  := desc (X ◁ inl _ _) (X ◁ inr _ _)

def distr_hom (X Y Z : C) : (X ⊗ Z) ⊕ₒ (Y ⊗ Z) ⟶ (X ⊕ₒ Y) ⊗ Z
  := desc (inl _ _ ▷ Z) (inr _ _ ▷ Z)

@[reassoc (attr := simp)]
theorem inl_distl_hom (X Y Z : C) : inl _ _ ≫ distl_hom X Y Z = X ◁ inl _ _ := by
  simp [distl_hom, left_exchange]

@[reassoc (attr := simp)]
theorem inr_distl_hom (X Y Z : C) : inr _ _ ≫ distl_hom X Y Z = X ◁ inr _ _ := by
  simp [distl_hom, right_exchange]

@[reassoc (attr := simp)]
theorem inl_distr_hom (X Y Z : C) : inl _ _ ≫ distr_hom X Y Z = inl _ _ ▷ Z := by
  simp [distr_hom, left_exchange]

@[reassoc (attr := simp)]
theorem inr_distr_hom (X Y Z : C) : inr _ _ ≫ distr_hom X Y Z = inr _ _ ▷ Z := by
  simp [distr_hom, right_exchange]

end DistributiveCategory

class DistributiveCategory (C: Type u)
  [Category C] [MonoidalCategoryStruct C] [ChosenFiniteCoproducts C]
  where
  distl_inv : ∀X Y Z: C, X ⊗ (Y ⊕ₒ Z) ⟶ (X ⊗ Y) ⊕ₒ (X ⊗ Z)
  distr_inv : ∀X Y Z: C, (X ⊕ₒ Y) ⊗ Z ⟶ (X ⊗ Z) ⊕ₒ (Y ⊗ Z)
  distl_comp_distl_inv : ∀X Y Z: C, DistributiveCategory.distl_hom X Y Z ≫ distl_inv X Y Z = 𝟙 _
  distr_comp_distr_inv : ∀X Y Z: C, DistributiveCategory.distr_hom X Y Z ≫ distr_inv X Y Z = 𝟙 _
  distl_inv_comp_distl : ∀X Y Z: C, distl_inv X Y Z ≫ DistributiveCategory.distl_hom X Y Z = 𝟙 _
  distr_inv_comp_distr : ∀X Y Z: C, distr_inv X Y Z ≫ DistributiveCategory.distr_hom X Y Z = 𝟙 _
  inl_central : ∀{X Y : C}, Central (inl _ _ : X ⟶ X ⊕ₒ Y)
  inr_central : ∀{X Y : C}, Central (inr _ _ : Y ⟶ X ⊕ₒ Y)

instance DistributiveCategory.instDistlHomIso [DistributiveCategory C] {X Y Z : C}
  : IsIso (distl_hom X Y Z)
  := ⟨⟨distl_inv X Y Z, distl_comp_distl_inv X Y Z, distl_inv_comp_distl X Y Z⟩⟩

instance DistributiveCategory.instDistrHomIso [DistributiveCategory C] {X Y Z : C}
  : IsIso (distr_hom X Y Z)
  := ⟨⟨distr_inv X Y Z, distr_comp_distr_inv X Y Z, distr_inv_comp_distr X Y Z⟩⟩

instance DistributiveCategory.instCentralInl [DistributiveCategory C] {X Y : C}
  : Central (inl _ _ : X ⟶ X ⊕ₒ Y) := DistributiveCategory.inl_central

instance DistributiveCategory.instCentralInr [DistributiveCategory C] {X Y : C}
  : Central (inr _ _ : Y ⟶ X ⊕ₒ Y) := DistributiveCategory.inr_central

def DistributiveCategory.distl [DistributiveCategory C] (X Y Z : C)
  : (X ⊗ Y) ⊕ₒ (X ⊗ Z) ≅ X ⊗ (Y ⊕ₒ Z)
  := ⟨distl_hom X Y Z, distl_inv X Y Z, distl_comp_distl_inv X Y Z, distl_inv_comp_distl X Y Z⟩

def DistributiveCategory.distr [DistributiveCategory C] (X Y Z : C)
  : (X ⊗ Z) ⊕ₒ (Y ⊗ Z) ≅ (X ⊕ₒ Y) ⊗ Z
  := ⟨distr_hom X Y Z, distr_inv X Y Z, distr_comp_distr_inv X Y Z, distr_inv_comp_distr X Y Z⟩

namespace DistributiveCategory

scoped notation "∂L" => DistributiveCategory.distl

scoped notation "∂R" => DistributiveCategory.distr

variable [DistributiveCategory C]

@[reassoc]
theorem distl_naturality_left {X Y Z X' : C} (f : X ⟶ X')
  : ((f ▷ Y) ⊕ₕ (f ▷ Z)) ≫ (∂L X' Y Z).hom = (∂L X Y Z).hom ≫ f ▷ (Y ⊕ₒ Z) := by
  simp [DistributiveCategory.distl, distl_hom, right_exchange, -desc_comp_inl_inr, addHom]

@[reassoc]
theorem distl_inv_naturality_left {X Y Z X' : C} (f : X ⟶ X')
  : f ▷ (Y ⊕ₒ Z) ≫ (∂L X' Y Z).inv = (∂L X Y Z).inv ≫ ((f ▷ Y) ⊕ₕ (f ▷ Z)) := by
  rw [<-cancel_mono (f := (∂L _ _ _).hom)]
  rw [Category.assoc, Category.assoc, distl_naturality_left]
  simp

@[reassoc (attr := simp)]
theorem inl_distl (X Y Z : C) : inl _ _ ≫ (∂L X Y Z).hom = X ◁ inl _ _ := inl_distl_hom X Y Z

@[reassoc (attr := simp)]
theorem inr_distl (X Y Z : C) : inr _ _ ≫ (∂L X Y Z).hom = X ◁ inr _ _ := inr_distl_hom X Y Z

@[reassoc (attr := simp)]
theorem inl_distr (X Y Z : C) : inl _ _ ≫ (∂R X Y Z).hom = inl _ _ ▷ Z := inl_distr_hom X Y Z

@[reassoc (attr := simp)]
theorem inr_distr (X Y Z : C) : inr _ _ ≫ (∂R X Y Z).hom = inr _ _ ▷ Z := inr_distr_hom X Y Z

end DistributiveCategory

end MonoidalCategoryStruct

namespace DistributiveCategory

variable [PremonoidalCategory C]

@[reassoc]
theorem distl_hom_naturality_right {X Y Z Y' Z' : C} (f : Y ⟶ Y') (g : Z ⟶ Z')
  : ((X ◁ f) ⊕ₕ (X ◁ g)) ≫ distl_hom X Y' Z' = distl_hom X Y Z ≫ X ◁ (f ⊕ₕ g) := by
  simp [addHom, -desc_comp_inl_inr, distl_hom, <-PremonoidalCategory.whiskerLeft_comp]

variable [DC : DistributiveCategory C]

@[reassoc]
theorem distl_naturality_right {X Y Z Y' Z' : C} (f : Y ⟶ Y') (g : Z ⟶ Z')
  :  ((X ◁ f) ⊕ₕ (X ◁ g)) ≫ (∂L X Y' Z').hom = (∂L X Y Z).hom ≫ X ◁ (f ⊕ₕ g)
  := distl_hom_naturality_right f g

@[reassoc]
theorem distl_inv_naturality_right {X Y Z Y' Z' : C} (f : Y ⟶ Y') (g : Z ⟶ Z')
  : X ◁ (f ⊕ₕ g) ≫ (∂L X Y' Z').inv = (∂L X Y Z).inv ≫ ((X ◁ f) ⊕ₕ (X ◁ g)) := by
  rw [<-cancel_mono (f := (∂L _ _ _).hom)]
  rw [Category.assoc, Category.assoc, distl_naturality_right]
  simp

instance Central.coprod {X Y Z : C} (f : X ⟶ Z) [Central f] (g : Y ⟶ Z) [Central g]
  : Central (desc f g) where
  left_exchange h := by
    rw [<-cancel_epi (f := distr_hom _ _ _)]
    ext <;> simp [
        PremonoidalCategory.ltimes, left_exchange_assoc, ← comp_whiskerRight,
        PremonoidalCategory.rtimes, <-comp_whiskerRight_assoc, left_exchange
      ]
  right_exchange h := by
    rw [<-cancel_epi (f := distl_hom _ _ _)]
    ext <;> simp [
        PremonoidalCategory.ltimes, ← right_exchange_assoc, ← PremonoidalCategory.whiskerLeft_comp,
        PremonoidalCategory.rtimes, ← PremonoidalCategory.whiskerLeft_comp_assoc, right_exchange
      ]

instance Central.distl_hom {X Y Z : C} : Central (distl_hom X Y Z)
  := by unfold DistributiveCategory.distl_hom; infer_instance

instance Central.distl {X Y Z : C} : Central (∂L X Y Z).hom := Central.distl_hom

instance Central.distr_hom {X Y Z : C} : Central (distr_hom X Y Z)
  := by unfold DistributiveCategory.distr_hom; infer_instance

instance Central.distr {X Y Z : C} : Central (∂R X Y Z).hom := Central.distr_hom

-- TODO: associators, unitors, etc. are all central

instance Central.addHom {X Y X' Y' : C} (f : X ⟶ Y) [Central f] (g : X' ⟶ Y') [Central g]
  : Central (f ⊕ₕ g) := by rw [ChosenFiniteCoproducts.addHom]; infer_instance

@[reassoc]
theorem distl_assoc {X Y Z W : C} :
  (∂L (W ⊗ X) Y Z).hom ≫ (α_ W X (Y ⊕ₒ Z)).hom
  = ((α_ W X Y).hom ⊕ₕ (α_ W X Z).hom) ≫ (∂L W (X ⊗ Y) (X ⊗ Z)).hom ≫ W ◁ (∂L X Y Z).hom
  := by simp [distl, distl_hom, addHom_desc, <-PremonoidalCategory.whiskerLeft_comp]

@[reassoc]
theorem assoc_inv_distl_inv {X Y Z W : C} :
  (α_ W X (Y ⊕ₒ Z)).inv ≫ (∂L (W ⊗ X) Y Z).inv
  = W ◁ (∂L X Y Z).inv ≫ (∂L W (X ⊗ Y) (X ⊗ Z)).inv ≫ ((α_ W X Y).inv ⊕ₕ (α_ W X Z).inv)
  := by
  rw [<-cancel_mono (f := (∂L (W ⊗ X) Y Z).hom ≫ (α_ W X (Y ⊕ₒ Z)).hom)]
  conv =>
    enter [2, 2]
    rw [distl_assoc]
  simp [addHom_comp_addHom_assoc, addHom_id]

@[reassoc]
theorem distl_inv_distl_inv {X Y Z W : C} :
  W ◁ (∂L X Y Z).inv ≫ (∂L W (X ⊗ Y) (X ⊗ Z)).inv
  = (α_ W X (Y ⊕ₒ Z)).inv ≫ (∂L (W ⊗ X) Y Z).inv ≫ ((α_ W X Y).hom ⊕ₕ (α_ W X Z).hom)
  := by rw [assoc_inv_distl_inv_assoc]; simp [addHom_comp_addHom, addHom_id]

@[reassoc]
theorem whiskerLeft_distl_desc {X Y Z W O : C} (f : X ⊗ Y ⟶ O) (g : X ⊗ Z ⟶ O) :
  W ◁ (∂L X Y Z).inv ≫ W ◁ (desc f g)
  = (α_ _ _ _).inv ≫ (∂L _ Y Z).inv ≫ desc ((α_ _ _ _).hom ≫ W ◁ f) ((α_ _ _ _).hom ≫ W ◁ g)
  := by
  rw [assoc_inv_distl_inv_assoc]
  congr 1
  rw [<-cancel_epi (f := (∂L _ _ _).hom), Iso.hom_inv_id_assoc]
  simp [distl, distl_hom, addHom_desc, <-PremonoidalCategory.whiskerLeft_comp]

@[reassoc]
theorem leftUnitor_inv_distl {Y Z : C}
  : (λ_ _).inv ≫ (∂L (𝟙_ C) Y Z).inv = (λ_ _).inv ⊕ₕ (λ_ _).inv := by
  rw [<-cancel_mono (f := (∂L _ _ _).hom)]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  simp [distl, distl_hom, addHom_desc]

theorem inl_tensor_zero_eq_inr_tensor_zero {X : C}
  : inl (X ⊗ 𝟘_ C) (X ⊗ 𝟘_ C) = inr (X ⊗ 𝟘_ C) (X ⊗ 𝟘_ C)
  := by
  rw [<-cancel_mono (f := (∂L _ _ _).hom)]
  simp only [inl_distl, inr_distl]
  congr
  apply fromZero_unique

theorem fromTensorZero_unique {X Y : C} (f g : X ⊗ 𝟘_ C ⟶ Y)
  : f = g := calc
  _ = inl _ _ ≫ desc f g := by simp
  _ = inr _ _ ≫ desc f g := by rw [inl_tensor_zero_eq_inr_tensor_zero]
  _ = _ := by simp

theorem inl_zero_tensor_eq_inr_zero_tensor {X : C}
  : inl (𝟘_ C ⊗ X) (𝟘_ C ⊗ X) = inr (𝟘_ C ⊗ X) (𝟘_ C ⊗ X)
  := by
  rw [<-cancel_mono (f := (∂R _ _ _).hom)]
  simp only [inl_distr, inr_distr]
  congr
  apply fromZero_unique

theorem fromZeroTensor_unique {X Y : C} (f g : 𝟘_ C ⊗ X ⟶ Y)
  : f = g := calc
  _ = inl _ _ ≫ desc f g := by simp
  _ = inr _ _ ≫ desc f g := by rw [inl_zero_tensor_eq_inr_zero_tensor]
  _ = _ := by simp

end DistributiveCategory

end CategoryTheory
