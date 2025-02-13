import Mathlib.Order.BoundedOrder.Basic

import Discretion.Premonoidal.Braided
import Discretion.Premonoidal.Distributive
import Discretion.Premonoidal.Predicate.Basic
import Discretion.Premonoidal.Property.Braided
import Discretion.Premonoidal.Property.Commutative
import Discretion.Premonoidal.Quant
import Discretion.EffectSystem.Basic

import Discretion.Poset2.Premonoidal

namespace CategoryTheory

open MonoidalCategory

open Monoidal

open MorphismProperty

open HasCommRel

class RightMover [Category C] [MonoidalCategoryStruct C] [O : ∀X Y : C, PartialOrder (X ⟶ Y)]
  (L R : MorphismProperty C) where
  left_fwd : ∀ {X Y X' Y' : C} (f : X ⟶ Y) (g : X' ⟶ Y'), L f → R g → f ⋉ g ≤ f ⋊ g
  right_fwd : ∀ {X Y X' Y' : C} (f : X ⟶ Y) (g : X' ⟶ Y'), L f → R g → g ⋊ f ≤ g ⋉ f

abbrev LeftMover [Category C] [MonoidalCategoryStruct C] [O : ∀X Y : C, PartialOrder (X ⟶ Y)]
  (L R : MorphismProperty C) := RightMover R L

theorem Commutes.of_left_right
  [Category C] [MonoidalCategoryStruct C] [O : ∀X Y : C, PartialOrder (X ⟶ Y)]
  (L R : MorphismProperty C) [RightMover L R] [LeftMover L R]
  : Commutes L R where
  left_sliding f g hf hg
    := le_antisymm (RightMover.left_fwd f g hf hg) (RightMover.right_fwd g f hg hf)
  right_sliding f g hf hg
    := le_antisymm (RightMover.left_fwd g f hg hf) (RightMover.right_fwd f g hf hg)

theorem Commutes.right
  [Category C] [MonoidalCategoryStruct C] [O : ∀X Y : C, PartialOrder (X ⟶ Y)]
  (L R : MorphismProperty C) [hC : Commutes L R] : RightMover L R where
  left_fwd f g hf hg := le_of_eq (Commutes.left_sliding f g hf hg)
  right_fwd f g hf hg := le_of_eq (Commutes.right_sliding f g hf hg).symm

theorem Commutes.left
  [Category C] [MonoidalCategoryStruct C] [O : ∀X Y : C, PartialOrder (X ⟶ Y)]
  (L R : MorphismProperty C) [hC : Commutes L R] : LeftMover L R
  := right R L (hC := hC.symm)

class Effectful2
  (C : Type v) [Category C] [MonoidalCategoryStruct C] [BraidedCategoryStruct C]
  [O : ∀X Y : C, LE (X ⟶ Y)] (E : Type u) [EffectSystem E] extends CompMono C, WhiskerMono C where
  eff : E →o MorphismProperty C
  eff_top : eff ⊤ = ⊤
  eff_monoidal : ∀e, (eff e).IsMonoidal
  eff_braided : ∀e, (eff e).IsBraided
  eff_right_mover : ∀{e e' : E}, e ⇀ e' → RightMover (eff e) (eff e')

abbrev Effectful2.pure [Category C] [MonoidalCategoryStruct C] [BraidedCategoryStruct C]
  [O : ∀X Y : C, LE (X ⟶ Y)] (E : Type u) [EffectSystem E] [EC : Effectful2 C E]
  : MorphismProperty C := EC.eff ⊥

namespace Monoidal
