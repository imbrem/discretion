import Discretion.AddMonoidalCategory.ChosenCoproducts
import Discretion.Premonoidal.Category

namespace CategoryTheory

open MonoidalCategory

open Monoidal

variable {C : Type u} [Category C] [MonoidalCategoryStruct C] [CC : ChosenCoproducts C]

namespace Monoidal

def distl (X Y Z : C) : (X ⊗ Y) +ₒ (X ⊗ Z) ⟶ X ⊗ (Y +ₒ Z) := coprod (X ◁ inl) (X ◁ inr)

def distr (X Y Z : C) : (X ⊗ Z) +ₒ (Y ⊗ Z) ⟶ (X +ₒ Y) ⊗ Z := coprod (inl ▷ Z) (inr ▷ Z)

scoped notation "δl_" => distl

scoped notation "δr_" => distr

@[reassoc (attr := simp)]
theorem inl_distl (X Y Z : C) : inl ≫ δl_ X Y Z = X ◁ inl := by
  simp [distl, coprod_comp, map_eq_coprod, left_exchange]

@[reassoc (attr := simp)]
theorem inr_distl (X Y Z : C) : inr ≫ δl_ X Y Z = X ◁ inr := by
  simp [distl, coprod_comp, map_eq_coprod, right_exchange]

@[reassoc (attr := simp)]
theorem inl_distr (X Y Z : C) : inl ≫ δr_ X Y Z = inl ▷ Z := by
  simp [distr, coprod_comp, map_eq_coprod, left_exchange]

@[reassoc (attr := simp)]
theorem inr_distr (X Y Z : C) : inr ≫ δr_ X Y Z = inr ▷ Z := by
  simp [distr, coprod_comp, map_eq_coprod, right_exchange]

noncomputable abbrev distl_inv (X Y Z : C) [IsIso (distl X Y Z)]
  : X ⊗ (Y +ₒ Z) ⟶ (X ⊗ Y) +ₒ (X ⊗ Z) := inv (distl X Y Z)

noncomputable abbrev distr_inv (X Y Z : C) [IsIso (distr X Y Z)]
  : (X +ₒ Y) ⊗ Z ⟶ (X ⊗ Z) +ₒ (Y ⊗ Z) := inv (distr X Y Z)

scoped notation "δl⁻¹" => distl_inv

scoped notation "δr⁻¹" => distr_inv

end Monoidal

class DistributiveCategory (C: Type u) [Category C] [MonoidalCategoryStruct C] [ChosenCoproducts C]
  where
  inl_central : ∀{X Y : C}, Central (inl : X ⟶ X +ₒ Y)
  inr_central : ∀{X Y : C}, Central (inr : Y ⟶ X +ₒ Y)
  distl_iso : ∀X Y Z: C, IsIso (distl X Y Z)
  distr_iso : ∀X Y Z: C, IsIso (distr X Y Z)

instance DistributiveCategory.instDistlIso [DistributiveCategory C] {X Y Z : C}
  : IsIso (distl X Y Z) := DistributiveCategory.distl_iso X Y Z

instance DistributiveCategory.instDistrIso [DistributiveCategory C] {X Y Z : C}
  : IsIso (distr X Y Z) := DistributiveCategory.distr_iso X Y Z

instance DistributiveCategory.instCentralInl [DistributiveCategory C] {X Y : C}
  : Central (inl : X ⟶ X +ₒ Y) := DistributiveCategory.inl_central

instance DistributiveCategory.instCentralInr [DistributiveCategory C] {X Y : C}
  : Central (inr : Y ⟶ X +ₒ Y) := DistributiveCategory.inr_central

namespace Monoidal

section DistributiveCategory

variable [DistributiveCategory C]

@[reassoc]
theorem distl_naturality_left {X Y Z X' : C} (f : X ⟶ X')
  : ((f ▷ Y) +ₕ (f ▷ Z)) ≫ δl_ X' Y Z = δl_ X Y Z ≫ f ▷ (Y +ₒ Z) := by
  simp [distl, coprod_comp, map_eq_coprod, right_exchange]

@[reassoc]
theorem distl_inv_naturality_left {X Y Z X' : C} (f : X ⟶ X')
  : f ▷ (Y +ₒ Z) ≫ δl⁻¹ X' Y Z = δl⁻¹ X Y Z ≫ ((f ▷ Y) +ₕ (f ▷ Z)) := by
  rw [<-cancel_mono (f := δl_ _ _ _)]
  simp [distl_naturality_left]

end DistributiveCategory

variable [IsPremonoidal C]

@[reassoc]
theorem distl_naturality_right {X Y Z Y' Z' : C} (f : Y ⟶ Y') (g : Z ⟶ Z')
  : ((X ◁ f) +ₕ (X ◁ g)) ≫ δl_ X Y' Z' = δl_ X Y Z ≫ X ◁ (f +ₕ g) := by
  simp [distl, coprod_comp, map_eq_coprod, <-whiskerLeft_comp]

variable [DC : DistributiveCategory C]

@[reassoc]
theorem distl_inv_naturality_right {X Y Z Y' Z' : C} (f : Y ⟶ Y') (g : Z ⟶ Z')
  : X ◁ (f +ₕ g) ≫ δl⁻¹ X Y' Z' = δl⁻¹ X Y Z ≫ ((X ◁ f) +ₕ (X ◁ g)) := by
  rw [<-cancel_mono (f := δl_ _ _ _)]
  simp [distl_naturality_right]

instance Central.coprod {X Y Z : C} (f : X ⟶ Z) [Central f] (g : Y ⟶ Z) [Central g]
  : Central (CC.coprod.desc f g) where
  left_sliding h := by
    rw [<-cancel_epi (f := δr_ _ _ _)]
    apply CC.coprod.eq_cases <;> simp [
        ltimes, left_sliding_assoc, ← whiskerRight_comp,
        rtimes, ← whiskerRight_comp_assoc, left_sliding
      ]
  right_sliding h := by
    rw [<-cancel_epi (f := δl_ _ _ _)]
    apply CC.coprod.eq_cases <;> simp [
        ltimes, ← right_sliding_assoc, ← whiskerLeft_comp,
        rtimes, ← whiskerLeft_comp_assoc, right_sliding
      ]

instance Central.distl {X Y Z : C} : Central (δl_ X Y Z) := by unfold Monoidal.distl; infer_instance

instance Central.distr {X Y Z : C} : Central (δr_ X Y Z) := by unfold Monoidal.distr; infer_instance

-- TODO: associators, unitors, etc. are all central

instance Central.addHom {X Y X' Y' : C} (f : X ⟶ Y) [Central f] (g : X' ⟶ Y') [Central g]
  : Central (f +ₕ g) := by rw [map_eq_coprod]; infer_instance

end Monoidal

end CategoryTheory
