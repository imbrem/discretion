import Discretion.AddMonoidalCategory.ChosenCoproducts
import Discretion.Premonoidal.Category

namespace CategoryTheory

open MonoidalCategory

open Monoidal

variable {C : Type u} [Category C] [MonoidalCategoryStruct C] [ChosenCoproducts C]

namespace Monoidal

def distl (X Y Z : C) : (X ⊗ Y) +ₒ (X ⊗ Z) ⟶ X ⊗ (Y +ₒ Z) := coprod (X ◁ inl) (X ◁ inr)

def distr (X Y Z : C) : (X ⊗ Z) +ₒ (Y ⊗ Z) ⟶ (X +ₒ Y) ⊗ Z := coprod (inl ▷ Z) (inr ▷ Z)

scoped notation "δl_" => distl

scoped notation "δr_" => distr

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

instance DistributiveCategory.instDistlIso [DistributiveCategory C] {X Y Z : C}
  : IsIso (distl X Y Z) := DistributiveCategory.distl_iso X Y Z

instance DistributiveCategory.instCentralInl [DistributiveCategory C] {X Y : C}
  : Central (inl : X ⟶ X +ₒ Y) := DistributiveCategory.inl_central

instance DistributiveCategory.instCentralInr [DistributiveCategory C] {X Y : C}
  : Central (inr : Y ⟶ X +ₒ Y) := DistributiveCategory.inr_central

namespace Monoidal

variable [DistributiveCategory C]

theorem distl_naturality_left {X Y Z X' : C} (f : X ⟶ X')
  : ((f ▷ Y) +ₕ (f ▷ Z)) ≫ δl_ X' Y Z = δl_ X Y Z ≫ f ▷ (Y +ₒ Z) := by
  simp [distl, coprod_comp, map_eq_coprod, right_exchange]

end Monoidal

end CategoryTheory
