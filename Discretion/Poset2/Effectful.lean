import Discretion.Premonoidal.Effectful
import Discretion.Poset2.Premonoidal

namespace CategoryTheory

open MonoidalCategory

open Monoidal

open MorphismProperty

open HasCommRel

class RightMover [Category C] [MonoidalCategoryStruct C] [Refines C]
  (L R : MorphismProperty C) where
  left_fwd : ∀ {X Y X' Y' : C} (f : X ⟶ Y) (g : X' ⟶ Y'), L f → R g → f ⋉ g ↠ f ⋊ g
  right_fwd : ∀ {X Y X' Y' : C} (f : X ⟶ Y) (g : X' ⟶ Y'), L f → R g → g ⋊ f ↠ g ⋉ f

abbrev LeftMover [Category C] [MonoidalCategoryStruct C] [Refines C]
  (L R : MorphismProperty C) := RightMover R L

theorem Commutes.of_left_right
  [Category C] [MonoidalCategoryStruct C] [Poset2 C]
  (L R : MorphismProperty C) [right : RightMover L R] [left : LeftMover L R]
  : Commutes L R where
  left_sliding f g hf hg
    := refines_antisymm (RightMover.left_fwd f g hf hg) (RightMover.right_fwd g f hg hf)
  right_sliding f g hf hg
    := refines_antisymm (RightMover.left_fwd g f hg hf) (RightMover.right_fwd f g hf hg)

theorem Commutes.right
  [Category C] [MonoidalCategoryStruct C] [Poset2 C]
  (L R : MorphismProperty C) [hC : Commutes L R] : RightMover L R where
  left_fwd f g hf hg := refines_of_eq (Commutes.left_sliding f g hf hg)
  right_fwd f g hf hg := refines_of_eq (Commutes.right_sliding f g hf hg).symm

theorem Commutes.left
  [Category C] [MonoidalCategoryStruct C] [Poset2 C]
  (L R : MorphismProperty C) [hC : Commutes L R] : LeftMover L R
  := right R L (hC := hC.symm)

class Effectful2
  (C : Type v) [Category C] [MonoidalCategoryStruct C] [BraidedCategoryStruct C]
  (E : Type u) [EffectSystem E] extends EffectfulCategory C E, MonPoset2 C where
  eff_right_mover : ∀{e e' : E}, e ⇀ e' → RightMover (eff e) (eff e')
  eff_comm h
    := Commutes.of_left_right _ _ (right := eff_right_mover h.1) (left := eff_right_mover h.2)

variable {C : Type v} [Category C] [MonoidalCategoryStruct C] [BraidedCategoryStruct C]
  {E : Type u} [EffectSystem E] [EC : Effectful2 C E]

abbrev Effectful2.pure : MorphismProperty C := EC.eff ⊥

theorem Effectful2.eff_left_mover {e e' : E} (h : e ↽ e') : LeftMover (EC.eff e) (EC.eff e')
  := eff_right_mover h

theorem Effectful2.eff_commutes {e e' : E} (h : e ⇌ e') : Commutes (EC.eff e) (EC.eff e')
  := Commutes.of_left_right (EC.eff e) (EC.eff e')
      (right := eff_right_mover h.1)
      (left := eff_left_mover h.2)

theorem Effectful2.pure_commutes_eff (e : E) : Commutes (EC.pure) (EC.eff e)
  := eff_commutes commutes_bot_left

theorem Effectful2.pure_central : Central (EC.pure)
  := Central.of_commutes_top (h := by convert pure_commutes_eff ⊤; rw [EC.eff_top])

theorem Effectful2.pure_hom_central {f : X ⟶ Y} (h : EC.pure f) : Central f
  := pure_central.central h

namespace Monoidal
