-- TODO: rework to be based off CategoryTheory.MorphismProperty.Limits?

import Mathlib.CategoryTheory.MorphismProperty.Composition
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal

import Discretion.ChosenFiniteCoproducts

namespace CategoryTheory.MorphismProperty

open ChosenFiniteCoproducts

variable {C} [Category C] [ChosenFiniteCoproducts C]

class ContainsInjections (W : MorphismProperty C) : Prop where
  inl_mem : ∀X Y : C, W (inl X Y)
  inr_mem : ∀X Y : C, W (inr X Y)

theorem inl_mem {W : MorphismProperty C} [ContainsInjections W] {X Y : C}
  : W (inl X Y) := ContainsInjections.inl_mem X Y

theorem inr_mem {W : MorphismProperty C} [ContainsInjections W] {X Y : C}
  : W (inr X Y) := ContainsInjections.inr_mem X Y

class ContainsCoprodDesc (W : MorphismProperty C) : Prop where
  coprod_desc_mem : ∀{X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}, W f → W g → W (desc f g)

theorem coprod_desc_mem {W : MorphismProperty C} [ContainsCoprodDesc W] {X Y Z : C}
  {f : X ⟶ Z} {g : Y ⟶ Z} (hf : W f) (hg : W g) : W (desc f g)
  := ContainsCoprodDesc.coprod_desc_mem hf hg

class ContainsBinaryCoproducts (W : MorphismProperty C)
  extends ContainsInjections W, ContainsCoprodDesc W, IsMultiplicative W : Prop

theorem addHom_mem {W : MorphismProperty C} [ContainsBinaryCoproducts W]
  {X Y X' Y' : C} {f : X ⟶ X'} {g : Y ⟶ Y'}
  (hf : W f) (hg : W g) : W (f ⊕ₕ g) := by
  rw [addHom]
  apply coprod_desc_mem <;> apply comp_mem <;> first | assumption | apply inl_mem | apply inr_mem

class ContainsInitial (W : MorphismProperty C) : Prop where
  initial_mem : ∀(X : C), W (fromZero X)

class ContainsCoproducts (W : MorphismProperty C)
  extends ContainsInitial W, ContainsBinaryCoproducts W

instance {W : MorphismProperty C} [ContainsInitial W] [ContainsBinaryCoproducts W]
  : ContainsCoproducts W := ⟨⟩
