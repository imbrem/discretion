import Discretion.Premonoidal.Category
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts

namespace CategoryTheory

open MonoidalCategory

open Limits

namespace Monoidal

variable {C : Type u} [Category C] [MonoidalCategoryStruct C] [HasBinaryCoproducts C]

noncomputable def distl (X Y Z : C) : (X ⊗ Y) ⨿ (X ⊗ Z) ⟶ X ⊗ (Y ⨿ Z)
  := coprod.desc (X ◁ coprod.inl) (X ◁ coprod.inr)

noncomputable def distr (X Y Z : C) : (X ⊗ Z) ⨿ (Y ⊗ Z) ⟶ (X ⨿ Y) ⊗ Z
  := coprod.desc (coprod.inl ▷ Z) (coprod.inr ▷ Z)

scoped notation "δl_" => distl

scoped notation "δr_" => distr

end Monoidal

open Monoidal

class HasDistributors (C : Type u) [Category C] [MonoidalCategoryStruct C]
  extends HasBinaryCoproducts C : Prop where
  left_iso : ∀{X Y Z : C}, IsIso (δl_ X Y Z)
  right_iso : ∀{X Y Z : C}, IsIso (δr_ X Y Z)

class CentralInjections (C : Type u) [Category C] [MonoidalCategoryStruct C] : Prop where
  inl_central : ∀{X Y : C} [HasBinaryCoproduct X Y], Monoidal.Central (coprod.inl : X ⟶ X ⨿ Y)
  inr_central : ∀{X Y : C} [HasBinaryCoproduct X Y], Monoidal.Central (coprod.inr : Y ⟶ X ⨿ Y)

class IsDistributive (C : Type u) [Category C] [MonoidalCategoryStruct C]
  extends HasDistributors C, CentralInjections C : Prop where

namespace Monoidal

variable {C : Type u} [Category C] [MonoidalCategoryStruct C]

section HasDistributors

variable [HasDistributors C]

instance IsIso.instDistl {X Y Z : C} : IsIso (δl_ X Y Z) := HasDistributors.left_iso

instance IsIso.instDistr {X Y Z : C} : IsIso (δr_ X Y Z) := HasDistributors.right_iso

end HasDistributors

section CentralInjections

variable [CentralInjections C]

instance inl_central {X Y : C} [HasBinaryCoproduct X Y] : Monoidal.Central (coprod.inl : X ⟶ X ⨿ Y)
  := CentralInjections.inl_central

instance inr_central {X Y : C} [HasBinaryCoproduct X Y] : Monoidal.Central (coprod.inr : Y ⟶ X ⨿ Y)
  := CentralInjections.inr_central

end CentralInjections

section IsPremonoidal

variable [IsPremonoidal C] [HasBinaryCoproducts C]

theorem distl_whiskerLeft_coprod_desc {X Y Z W : C} {f : X ⟶ Z} {g : Y ⟶ Z}
  : δl_ W X Y ≫ W ◁ coprod.desc f g = coprod.desc (W ◁ f) (W ◁ g)
  := by simp [distl, <-whiskerLeft_comp]

theorem distr_whiskerRight_coprod_desc {X Y Z W : C} {f : X ⟶ Z} {g : Y ⟶ Z}
  : δr_ X Y W ≫ coprod.desc f g ▷ W = coprod.desc (f ▷ W) (g ▷ W)
  := by simp [distr, <-whiskerRight_comp]

variable [HasDistributors C]

theorem whiskerRight_coprod_desc {X Y Z W : C} {f : X ⟶ Z} {g : Y ⟶ Z}
  : coprod.desc f g ▷ W = inv (δr_ X Y W) ≫ coprod.desc (f ▷ W) (g ▷ W)
  := (cancel_epi (δr_ X Y W)).mp (by simp [distr_whiskerRight_coprod_desc])

theorem whiskerLeft_coprod_desc {X Y Z W : C} {f : X ⟶ Z} {g : Y ⟶ Z}
  : W ◁ coprod.desc f g = inv (δl_ W X Y) ≫ coprod.desc (W ◁ f) (W ◁ g)
  := (cancel_epi (δl_ W X Y)).mp (by simp [distl_whiskerLeft_coprod_desc])

theorem coprod_desc_ltimes {X Y Z X' Y' : C} {f : X ⟶ Z} {g : Y ⟶ Z} {h : X' ⟶ Y'}
  : coprod.desc f g ⋉ h = inv (δr_ X Y X') ≫ coprod.desc (f ⋉ h) (g ⋉ h)
  := by simp [whiskerRight_coprod_desc, ltimes]

theorem rtimes_coprod_desc {X Y Z X' Y' : C} {f : X ⟶ Z} {g : Y ⟶ Z} {h : X' ⟶ Y'}
  : h ⋊ coprod.desc f g = inv (δl_ X' X Y) ≫ coprod.desc (h ⋊ f) (h ⋊ g)
  := by simp [whiskerLeft_coprod_desc, rtimes]

end IsPremonoidal

section IsDistributive

variable [IsDistributive C]

theorem distl_naturality {X Y Z X' : C} {h : X ⟶ X'}
  : coprod.map (h ▷ Y) (h ▷ Z) ≫ δl_ X' Y Z = δl_ X Y Z ≫ h ▷ (Y ⨿ Z)
  := by simp [distl, right_exchange]

theorem distr_naturality {X Y Z Z' : C} {h : Z ⟶ Z'}
  : coprod.map (X ◁ h) (Y ◁ h) ≫ δr_ X Y Z' = δr_ X Y Z ≫ (X ⨿ Y) ◁ h
  := by simp [distr, left_exchange]

variable [IsPremonoidal C]

instance Central.coprod_desc {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}
  [hf :Central f] [hg : Central g] : Central (coprod.desc f g) where
  left_sliding h := by
    rw [coprod_desc_ltimes]
    apply (cancel_epi (δr_ _ _ _)).mp
    simp only [← Category.assoc, IsIso.hom_inv_id, Category.id_comp, rtimes, ← distr_naturality]
    rw [Category.assoc, distr_whiskerRight_coprod_desc]
    simp [left_sliding]
  right_sliding h := by
    rw [rtimes_coprod_desc]
    apply (cancel_epi (δl_ _ _ _)).mp
    simp only [← Category.assoc, IsIso.hom_inv_id, Category.id_comp, ltimes, ← distl_naturality]
    rw [Category.assoc, distl_whiskerLeft_coprod_desc]
    simp [right_sliding]

instance Central.coprod_map {X Y X' Y' : C} {f : X ⟶ X'} {g : Y ⟶ Y'}
  (hf : Central f) (hg : Central g) : Central (coprod.map f g)
  := by rw [<-coprod.desc_comp_inl_comp_inr]; exact coprod_desc

instance Central.distl {X Y Z : C} : Central (δl_ X Y Z) := coprod_desc

instance Central.distr {X Y Z : C} : Central (δr_ X Y Z) := coprod_desc

end IsDistributive
