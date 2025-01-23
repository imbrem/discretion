import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts

import Discretion.MorphismProperty.BinaryProducts

import Discretion.AddMonoidalCategory.ChosenCoproducts

namespace CategoryTheory

open Limits

open MorphismProperty

class Iterate (C : Type u) [Category C] [HasBinaryCoproducts C] where
  iterate {X Y : C} : (X ⟶ Y ⨿ X) → (X ⟶ Y)
  fixpoint {X Y : C} {f : X ⟶ Y ⨿ X}
    : f ≫ coprod.desc (𝟙 Y) (iterate f) = iterate f

def iterate {C : Type u} [Category C] [HasBinaryCoproducts C] [Iterate C] {X Y : C}
  : (X ⟶ Y ⨿ X) → (X ⟶ Y) := Iterate.iterate

class Iterate.Uniform (C : Type u) [Category C] [HasBinaryCoproducts C] [Iterate C]
  (W : MorphismProperty C) : Prop where
  uniform {X Y : C} {f : Y ⟶ Z ⨿ Y} {g : X ⟶ Z ⨿ X} {h : X ⟶ Y}
    : W h → h ≫ f = g ≫ coprod.map (𝟙 Z) h → h ≫ iterate f = iterate g

-- Part 1 of Lemma 31 of Goncharov and Schröder (2018, Guarded Traced Categories)
theorem Iterate.Uniform.squaring {C : Type u} [Category C] [HasBinaryCoproducts C] [Iterate C]
  {W : MorphismProperty C} [W.ContainsBinaryCoproducts] [U : Iterate.Uniform C W]
  (codiagonal : ∀{X Y : C} {f : X ⟶ (Y ⨿ X) ⨿ X},
    iterate (iterate f) = iterate (f ≫ coprod.desc (𝟙 (Y ⨿ X)) coprod.inr))
  {X Y : C} {f : X ⟶ Y ⨿ X} : iterate (f ≫ coprod.desc coprod.inl f) = iterate f := by
  generalize hw
    : (
      coprod.desc
        (f ≫ coprod.map (𝟙 Y) coprod.inr ≫ coprod.inl)
        (f ≫ coprod.map coprod.inl coprod.inl)
      : X ⨿ X ⟶ (Y ⨿ (X ⨿ X)) ⨿ (X ⨿ X)
    )
    = w
  calc
  _ = coprod.inr ≫ iterate (iterate w) := by
    have u
      : coprod.inr ≫ iterate w = (f ≫ coprod.desc coprod.inl f) ≫ coprod.map (𝟙 Y) coprod.inr :=
      calc
      _ = coprod.inr ≫ w ≫ coprod.desc (𝟙 _) (iterate w) := by rw [fixpoint]
      _ = f ≫ coprod.desc coprod.inl (coprod.inl ≫ iterate w) := by simp [<-hw]
      _ = f ≫ coprod.desc coprod.inl (coprod.inl ≫ w ≫ coprod.desc (𝟙 _) (iterate w))
        := by rw [fixpoint]
      _ = f ≫ coprod.desc coprod.inl f ≫ coprod.map (𝟙 _) coprod.inr := by simp [<-hw]
      _ = _ := by rw [Category.assoc]
      ;
    rw [U.uniform inr_mem u]
  _ = coprod.inr ≫ iterate (w ≫ coprod.desc (𝟙 _) coprod.inr) := by rw [codiagonal]
  _ = coprod.inr
      ≫ iterate (coprod.desc (f ≫ coprod.map (𝟙 Y) coprod.inr) (f ≫ coprod.map (𝟙 Y) coprod.inl))
        := by simp [<-hw, <-coprod.desc_comp_inl_comp_inr]
  _ = coprod.inr ≫ codiag _ ≫ iterate f := by
    have u
      : codiag _ ≫ f
      = coprod.desc
          (f ≫ coprod.map (𝟙 Y) coprod.inr)
          (f ≫ coprod.map (𝟙 Y) coprod.inl)
        ≫ coprod.map (𝟙 _) (codiag _)
      := by simp
    rw [U.uniform codiag_mem u]
  _ = _ := by simp

-- Part 2 of Lemma 32 of Goncharov and Schröder (2018, Guarded Traced Categories)
theorem Iterate.Uniform.dinaturality {C : Type u} [Category C] [HasBinaryCoproducts C] [Iterate C]
  {W : MorphismProperty C} [W.ContainsBinaryCoproducts] [U : Iterate.Uniform C W]
  (squaring : ∀{X Y : C} {f : X ⟶ Y ⨿ X}, iterate (f ≫ coprod.desc coprod.inl f) = iterate f)
  {X Y Z : C} {f : X ⟶ Y ⨿ Z} {g : Z ⟶ Y ⨿ X}
  : f ≫ coprod.desc (𝟙 Y) (iterate (g ≫ coprod.desc coprod.inl f))
      = iterate (f ≫ coprod.desc coprod.inl g)
  := by
  generalize hh
    : coprod.desc (f ≫ coprod.map (𝟙 Y) coprod.inr) (g ≫ coprod.map (𝟙 Y) coprod.inl) = h
  have h1 : coprod.inl ≫ iterate h = iterate (f ≫ coprod.desc coprod.inl g)
    := by
    rw [<-squaring (f := h)]
    apply U.uniform inl_mem
    simp [<-hh]
  have h2 : coprod.inr ≫ iterate h = iterate (g ≫ coprod.desc coprod.inl f)
    := by
    rw [<-squaring (f := h)]
    apply U.uniform inr_mem
    simp [<-hh]
  apply Eq.symm
  calc
    _ = coprod.inl ≫ iterate h := h1.symm
    _ = coprod.inl ≫ h ≫ coprod.desc (𝟙 _) (iterate h) := by rw [fixpoint]
    _ = f ≫ coprod.desc (𝟙 _) (coprod.inr ≫ iterate h) := by simp [<-hh]
    _ = _ := by rw [h2]

class Iterate.Conway (C : Type u) [Category C] [HasBinaryCoproducts C] [Iterate C] : Prop
  where
  naturality {X Y Z : C} {f : X ⟶ Y ⨿ X} {g : Y ⟶ Z}
    : iterate (f ≫ coprod.map g (𝟙 X)) = (iterate f) ≫ g
  dinaturality {X Y Z : C} {f : X ⟶ Y ⨿ Z} {g : Z ⟶ Y ⨿ X}
    : f ≫ coprod.desc (𝟙 Y) (iterate (g ≫ coprod.desc coprod.inl f))
      = iterate (f ≫ coprod.desc coprod.inl g)
  codiagonal {X Y : C} {f : X ⟶ (Y ⨿ X) ⨿ X}
    : iterate (iterate f) = iterate (f ≫ coprod.desc (𝟙 (Y ⨿ X)) coprod.inr)

theorem Iterate.Uniform.conway {C : Type u} [Category C] [HasBinaryCoproducts C] [Iterate C]
  {W : MorphismProperty C} [W.ContainsBinaryCoproducts] [U : Iterate.Uniform C W]
  (naturality : ∀{X Y Z : C} {f : X ⟶ Y ⨿ X} {g : Y ⟶ Z},
    iterate (f ≫ coprod.map g (𝟙 X)) = (iterate f) ≫ g)
  (codiagonal : ∀{X Y : C} {f : X ⟶ (Y ⨿ X) ⨿ X},
    iterate (iterate f) = iterate (f ≫ coprod.desc (𝟙 (Y ⨿ X)) coprod.inr))
  : Iterate.Conway C where
  naturality := naturality
  codiagonal := codiagonal
  dinaturality := U.dinaturality (U.squaring codiagonal)

end CategoryTheory
