import Discretion.Premonoidal.Category
import Discretion.Premonoidal.Property.Basic

namespace CategoryTheory

open MonoidalCategory

open Monoidal

namespace MorphismProperty

variable {C} [Category C] [MonoidalCategoryStruct C]

class Commutes (L R : MorphismProperty C) where
  left_sliding : ∀ {X Y X' Y' : C} (f : X ⟶ Y) (g : X' ⟶ Y'), L f → R g → f ⋉ g = f ⋊ g
  right_sliding : ∀ {X Y X' Y' : C} (f : X ⟶ Y) (g : X' ⟶ Y'), L f → R g → g ⋉ f = g ⋊ f

theorem Commutes.symm {W W' : MorphismProperty C} [h : Commutes W W'] : Commutes W' W where
  left_sliding f g hf hg := right_sliding g f hg hf
  right_sliding f g hf hg := left_sliding g f hg hf

theorem Commutes.mono {L L' R R' : MorphismProperty C}
  (hL : L ≤ L') (hR : R ≤ R') [Commutes L' R'] : Commutes L R where
  left_sliding f g hf hg := left_sliding f g (hL _ hf) (hR _ hg)
  right_sliding f g hf hg := right_sliding f g (hL _ hf) (hR _ hg)

theorem Commutes.inf_ll {L L' R : MorphismProperty C}
  [hW : Commutes L R] : Commutes (L ⊓ L') R where
  left_sliding f g hf hg := left_sliding f g hf.1 hg
  right_sliding f g hf hg := right_sliding f g hf.1 hg

theorem Commutes.inf_lr {L R R' : MorphismProperty C}
  [hW : Commutes L R] : Commutes L (R ⊓ R') where
  left_sliding f g hf hg := left_sliding f g hf hg.1
  right_sliding f g hf hg := right_sliding f g hf hg.1

theorem Commutes.inf_rl {L R R' : MorphismProperty C}
  [hW : Commutes L R'] : Commutes L (R ⊓ R') where
  left_sliding f g hf hg := left_sliding f g hf hg.2
  right_sliding f g hf hg := right_sliding f g hf hg.2

theorem Commutes.inf_rr {L L' R : MorphismProperty C}
  [hW : Commutes L' R] : Commutes (L ⊓ L') R where
  left_sliding f g hf hg := left_sliding f g hf.2 hg
  right_sliding f g hf hg := right_sliding f g hf.2 hg

instance Commutes.sup_left {L L' R : MorphismProperty C}
  [hW : Commutes L R] [hW' : Commutes L' R] : Commutes (L ⊔ L') R where
  left_sliding f g
    | Or.inl hf, hg => left_sliding f g hf hg
    | Or.inr hf, hg => left_sliding f g hf hg
  right_sliding f g
    | Or.inl hf, hg => right_sliding f g hf hg
    | Or.inr hf, hg => right_sliding f g hf hg

instance Commutes.sup_right {L R R' : MorphismProperty C}
  [hW : Commutes L R] [hW' : Commutes L R'] : Commutes L (R ⊔ R') where
  left_sliding f g
    | hf, Or.inl hg => left_sliding f g hf hg
    | hf, Or.inr hg => left_sliding f g hf hg
  right_sliding f g
    | hf, Or.inl hg => right_sliding f g hf hg
    | hf, Or.inr hg => right_sliding f g hf hg

abbrev Commutative (W : MorphismProperty C) := Commutes W W

instance Commutes.central_left {W W' : MorphismProperty C} [Central W] : Commutes W W' where
  left_sliding f g hf _ := Monoidal.left_sliding (hf := Central.central hf) f g
  right_sliding f g hf _ := Monoidal.right_sliding (hg := Central.central hf) g f

instance Commutes.central_right {W W' : MorphismProperty C} [Central W'] : Commutes W W'
  := central_left.symm

theorem Commutative.of_central {W : MorphismProperty C} [h : Central W] : Commutative W
  := inferInstance

-- TODO: fuse these??
theorem Central.of_commutes_top {W : MorphismProperty C} [h : Commutes W ⊤] : Central W where
  central hf := {
    left_sliding := λ _ => Commutes.left_sliding (R := ⊤) _ _ hf True.intro
    right_sliding := λ _ => Commutes.right_sliding (R := ⊤) _ _ hf True.intro
  }

section IsBinoidal

variable [IsBinoidal C]

instance Commutes.cc_left {W W' : MorphismProperty C} [hW : Commutes W W']
  : Commutes (cc W) W' where
  left_sliding f g hf hg := by induction hf with
    | base f hf => exact hW.left_sliding f g hf hg
    | comp f h hf hh If Ih =>
      simp only [
        ltimes, rtimes, Monoidal.whiskerRight_comp, Monoidal.whiskerLeft_comp, Category.assoc
      ] at *
      rw [Ih, <-Category.assoc, If, Category.assoc]
  right_sliding f g hf hg := by induction hf with
    | base f hf => exact hW.right_sliding f g hf hg
    | comp f h hf hh If Ih =>
      simp only [
        ltimes, rtimes, Monoidal.whiskerRight_comp, Monoidal.whiskerLeft_comp, Category.assoc
      ] at *
      rw [<-Ih, <-Category.assoc, If, Category.assoc]

instance Commutes.cc_right {W W' : MorphismProperty C} [hW : Commutes W W']
  : Commutes W (cc W') := have _ : Commutes W' W := symm; cc_left.symm

instance Commutes.mul_left {L L' R : MorphismProperty C} [hL : Commutes L R] [hL' : Commutes L' R]
  : Commutes (L * L') R := cc_left

instance Commutes.mul_right {L R R' : MorphismProperty C} [hR : Commutes L R] [hR' : Commutes L R']
  : Commutes L (R * R') := cc_right

end IsBinoidal

-- TODO: monoidal closure lore...
