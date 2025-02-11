import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts

import Discretion.MorphismProperty.BinaryProducts
import Discretion.ChosenFiniteCoproducts

namespace CategoryTheory

open Limits

open MorphismProperty

open ChosenFiniteCoproducts

-- TODO: port to chosen coproducts...

class Iterate (C : Type u) [Category C] [ChosenFiniteCoproducts C] where
  iterate {X Y : C} : (X ⟶ Y ⊕ₒ X) → (X ⟶ Y)
  fixpoint {X Y : C} {f : X ⟶ Y ⊕ₒ X}
    : f ≫ desc (𝟙 Y) (iterate f) = iterate f

def iterate {C : Type u} [Category C] [ChosenFiniteCoproducts C] [Iterate C] {X Y : C}
  : (X ⟶ Y ⊕ₒ X) → (X ⟶ Y) := Iterate.iterate

class Iterate.Uniform (C : Type u) [Category C] [ChosenFiniteCoproducts C] [Iterate C]
  (W : MorphismProperty C) : Prop where
  uniform {X Y : C} {f : Y ⟶ Z ⊕ₒ Y} {g : X ⟶ Z ⊕ₒ X} {h : X ⟶ Y}
    : W h → h ≫ f = g ≫ ((𝟙 Z) ⊕ₕ h) → h ≫ iterate f = iterate g

-- Part 1 of Lemma 31 of Goncharov and Schröder (2018, Guarded Traced Categories)
theorem Iterate.Uniform.squaring {C : Type u} [Category C] [ChosenFiniteCoproducts C] [Iterate C]
  {W : MorphismProperty C} [W.ContainsBinaryCoproducts] [U : Iterate.Uniform C W]
  (codiagonal : ∀{X Y : C} {f : X ⟶ (Y ⊕ₒ X) ⊕ₒ X},
    iterate (iterate f) = iterate (f ≫ desc (𝟙 (Y ⊕ₒ X)) (inr _ _)))
  {X Y : C} {f : X ⟶ Y ⊕ₒ X} : iterate (f ≫ desc (inl _ _) f) = iterate f := by
  generalize hw
    : (
      desc
        (f ≫ ((𝟙 Y) ⊕ₕ inr _ _) ≫ inl _ _)
        (f ≫ ((inl _ _) ⊕ₕ (inl _ _)))
      : X ⊕ₒ X ⟶ (Y ⊕ₒ (X ⊕ₒ X)) ⊕ₒ (X ⊕ₒ X)
    )
    = w
  calc
  _ = inr _ _ ≫ iterate (iterate w) := by
    have u
      : inr _ _ ≫ iterate w = (f ≫ desc (inl _ _) f) ≫ ((𝟙 Y) ⊕ₕ inr _ _) :=
      calc
      _ = inr _ _ ≫ w ≫ desc (𝟙 _) (iterate w) := by rw [fixpoint]
      _ = f ≫ desc (inl _ _) (inl _ _ ≫ iterate w) := by simp [<-hw]
      _ = f ≫ desc (inl _ _) (inl _ _ ≫ w ≫ desc (𝟙 _) (iterate w))
        := by rw [fixpoint]
      _ = f ≫ desc (inl _ _) f ≫ ((𝟙 _) ⊕ₕ inr _ _) := by simp [<-hw]; congr; simp
      _ = _ := by rw [Category.assoc]
      ;
    rw [U.uniform inr_mem u]
  _ = inr _ _ ≫ iterate (w ≫ desc (𝟙 _) (inr _ _)) := by rw [codiagonal]
  _ = inr _ _ ≫ iterate (desc (f ≫ ((𝟙 Y) ⊕ₕ inr _ _)) (f ≫ ((𝟙 Y) ⊕ₕ inl _ _)))
        := by simp [<-hw]; congr <;> simp
  _ = inr _ _ ≫ desc (𝟙 _) (𝟙 _) ≫ iterate f := by
    have u
      : desc (𝟙 _) (𝟙 _) ≫ f
      = desc
          (f ≫ ((𝟙 Y) ⊕ₕ inr _ _))
          (f ≫ ((𝟙 Y) ⊕ₕ inl _ _))
        ≫ ((𝟙 _) ⊕ₕ (desc (𝟙 _) (𝟙 _)))
      := by simp
    rw [U.uniform ?c u]
    apply coprod_desc_mem <;> apply id_mem
  _ = _ := by simp

-- Part 2 of Lemma 32 of Goncharov and Schröder (2018, Guarded Traced Categories)
theorem Iterate.Uniform.dinaturality {C : Type u} [Category C] [ChosenFiniteCoproducts C] [Iterate C]
  {W : MorphismProperty C} [W.ContainsBinaryCoproducts] [U : Iterate.Uniform C W]
  (squaring : ∀{X Y : C} {f : X ⟶ Y ⊕ₒ X}, iterate (f ≫ desc (inl _ _) f) = iterate f)
  {X Y Z : C} {f : X ⟶ Y ⊕ₒ Z} {g : Z ⟶ Y ⊕ₒ X}
  : f ≫ desc (𝟙 Y) (iterate (g ≫ desc (inl _ _) f))
      = iterate (f ≫ desc (inl _ _) g)
  := by
  generalize hh
    : desc (f ≫ ((𝟙 Y) ⊕ₕ (inr _ _))) (g ≫ ((𝟙 Y) ⊕ₕ inl _ _)) = h
  have h1 : inl _ _ ≫ iterate h = iterate (f ≫ desc (inl _ _) g)
    := by
    rw [<-squaring (f := h)]
    apply U.uniform inl_mem
    simp [<-hh]
  have h2 : inr _ _ ≫ iterate h = iterate (g ≫ desc (inl _ _) f)
    := by
    rw [<-squaring (f := h)]
    apply U.uniform inr_mem
    simp [<-hh]
  apply Eq.symm
  calc
    _ = inl _ _ ≫ iterate h := h1.symm
    _ = inl _ _ ≫ h ≫ desc (𝟙 _) (iterate h) := by rw [fixpoint]
    _ = f ≫ desc (𝟙 _) (inr _ _ ≫ iterate h) := by simp [<-hh]
    _ = _ := by rw [h2]

class Iterate.Conway (C : Type u) [Category C] [ChosenFiniteCoproducts C] [Iterate C] : Prop
  where
  naturality {X Y Z : C} {f : X ⟶ Y ⊕ₒ X} {g : Y ⟶ Z}
    : iterate (f ≫ (g ⊕ₕ (𝟙 X))) = (iterate f) ≫ g
  dinaturality {X Y Z : C} {f : X ⟶ Y ⊕ₒ Z} {g : Z ⟶ Y ⊕ₒ X}
    : f ≫ desc (𝟙 Y) (iterate (g ≫ desc (inl _ _) f))
      = iterate (f ≫ desc (inl _ _) g)
  codiagonal {X Y : C} {f : X ⟶ (Y ⊕ₒ X) ⊕ₒ X}
    : iterate (iterate f) = iterate (f ≫ desc (𝟙 (Y ⊕ₒ X)) (inr _ _))

theorem Iterate.Uniform.conway {C : Type u} [Category C] [ChosenFiniteCoproducts C] [Iterate C]
  {W : MorphismProperty C} [W.ContainsBinaryCoproducts] [U : Iterate.Uniform C W]
  (naturality : ∀{X Y Z : C} {f : X ⟶ Y ⊕ₒ X} {g : Y ⟶ Z},
    iterate (f ≫ (g ⊕ₕ (𝟙 X))) = (iterate f) ≫ g)
  (codiagonal : ∀{X Y : C} {f : X ⟶ (Y ⊕ₒ X) ⊕ₒ X},
    iterate (iterate f) = iterate (f ≫ desc (𝟙 (Y ⊕ₒ X)) (inr _ _)))
  : Iterate.Conway C where
  naturality := naturality
  codiagonal := codiagonal
  dinaturality := U.dinaturality (U.squaring codiagonal)

end CategoryTheory
