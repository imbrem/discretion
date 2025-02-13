import Mathlib.CategoryTheory.Monad.Basic
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Types.Basic

import Discretion.Monad.Commutative

namespace CategoryTheory

variable {C : Type u} [Category C] [MonoidalCategoryStruct C]

open MonoidalCategory

class LeftStrength (T : Monad C) where
  leftStrength : ∀(X Y : C), X ⊗ (T.obj Y) ⟶ T.obj (X ⊗ Y)
  leftStrength_naturality : ∀(X Y X' Y' : C) (f : X ⟶ X') (g : Y ⟶ Y'),
    (f ⊗ (T.map g)) ≫ leftStrength X' Y' = leftStrength X Y ≫ T.map (f ⊗ g)
  leftUnitor_leftStrength : ∀(X : C),
    (λ_ (T.obj X)).inv ≫ leftStrength (𝟙_ C) X = T.map (λ_ X).inv
  leftStrength_associator : ∀(X Y Z : C),
    leftStrength (X ⊗ Y) Z ≫ T.map (α_ X Y Z).hom
      = (α_ X Y (T.obj Z)).hom ≫ X ◁ leftStrength Y Z ≫ leftStrength X (Y ⊗ Z)
  η_leftStrength : ∀(X Y : C), X ◁ T.η.app Y ≫ leftStrength X Y = T.η.app (X ⊗ Y)
  μ_leftStrength : ∀(X Y : C),
    X ◁ T.μ.app Y ≫ leftStrength X Y
      = leftStrength X (T.obj Y) ≫ T.map (leftStrength X Y) ≫ T.μ.app (X ⊗ Y)

attribute [reassoc] LeftStrength.leftStrength_naturality
attribute [reassoc] LeftStrength.leftUnitor_leftStrength
attribute [reassoc] LeftStrength.leftStrength_associator
attribute [reassoc] LeftStrength.η_leftStrength
attribute [reassoc] LeftStrength.μ_leftStrength

class RightStrength (T : Monad C) where
  rightStrength : ∀(X Y : C), T.obj X ⊗ Y ⟶ T.obj (X ⊗ Y)
  rightStrength_naturality : ∀(X Y X' Y' : C) (f : X ⟶ X') (g : Y ⟶ Y'),
    ((T.map f) ⊗ g) ≫ rightStrength X' Y' = rightStrength X Y ≫ T.map (f ⊗ g)
  rightUnitor_rightStrength : ∀(X : C),
    (ρ_ (T.obj X)).inv ≫ rightStrength X (𝟙_ C) = T.map (ρ_ X).inv
  rightStrength_associator : ∀(X Y Z : C),
    rightStrength X (Y ⊗ Z) ≫ T.map (α_ X Y Z).inv
      = (α_ (T.obj X) Y Z).inv ≫ rightStrength X Y ▷ Z ≫ rightStrength (X ⊗ Y) Z
  η_rightStrength : ∀(X Y : C), T.η.app X ▷ Y ≫ rightStrength X Y = T.η.app (X ⊗ Y)
  μ_rightStrength : ∀(X Y : C),
    T.μ.app X ▷ Y ≫ rightStrength X Y
      = rightStrength (T.obj X) Y ≫ T.map (rightStrength X Y) ≫ T.μ.app (X ⊗ Y)

attribute [reassoc] RightStrength.rightStrength_naturality
attribute [reassoc] RightStrength.rightUnitor_rightStrength
attribute [reassoc] RightStrength.rightStrength_associator
attribute [reassoc] RightStrength.η_rightStrength
attribute [reassoc] RightStrength.μ_rightStrength

class Strength (T : Monad C) extends LeftStrength T, RightStrength T where
  leftStrength_rightStrength : ∀(X Y Z : C),
    leftStrength X Y ▷ Z ≫ rightStrength (X ⊗ Y) Z
      = (α_ X (T.obj Y) Z).hom
      ≫ X ◁ rightStrength Y Z
      ≫ leftStrength X (Y ⊗ Z)
      ≫ T.map (α_ X Y Z).inv

attribute [reassoc] Strength.leftStrength_rightStrength

open LeftStrength RightStrength

@[reassoc]
theorem Strength.rightStrength_leftStrength {T : Monad C} [Strength T] (X Y Z : C) :
  X ◁ rightStrength Y Z ≫ leftStrength X (Y ⊗ Z)
    = (α_ X (T.obj Y) Z).inv ≫ leftStrength X Y ▷ Z ≫ rightStrength _ Z ≫ T.map (α_ X Y Z).hom
  := by simp [leftStrength_rightStrength_assoc]

--TODO: strength of left strength for symmetric

--TODO: strength of right strength for symmetric

--TODO: if symmetric, right strength is induced by braiding from left strength

--TODO: if symmetric, left strength is induced by braiding from right strength

instance Strength.ofType.{v} {T : Monad (Type v)} : Strength T where
  leftStrength _ _ | ⟨x, ty⟩ => T.map (λ y => (x, y)) ty
  leftStrength_naturality _ _ _ _ f g := by
    funext ⟨x, ty⟩; simp only [types_comp_apply, tensor_apply]
    rw [
      <-types_comp_apply (g := T.map _), <-types_comp_apply (g := T.map _),
      <-T.map_comp, <-T.map_comp]
    rfl
  leftUnitor_leftStrength _ := rfl
  leftStrength_associator _ _ _ := by
    funext ⟨⟨x, y⟩, tz⟩; simp only [types_comp_apply, associator_hom_apply,
      whiskerLeft_apply]
    rw [
      <-types_comp_apply (g := T.map _), <-types_comp_apply (g := T.map _),
      <-T.map_comp, <-T.map_comp]
    rfl
  η_leftStrength _ _ := by
    funext ⟨x, y⟩; simp only [Functor.id_obj, types_comp_apply, whiskerLeft_apply]
    rw [<-types_comp_apply (g := T.map _), <-T.η.naturality]
    rfl
  μ_leftStrength _ _ := by
    funext ⟨x, tty⟩; simp only [Functor.comp_obj, types_comp_apply, whiskerLeft_apply]
    rw [
      <-types_comp_apply (g := T.map _), <-T.μ.naturality, <-types_comp_apply (g := T.map _),
      <-T.map_comp]
    rfl
  rightStrength _ _ | ⟨tx, y⟩ => T.map (λ x => (x, y)) tx
  rightStrength_naturality _ _ _ _ f g := by
    funext ⟨tx, y⟩; simp only [types_comp_apply, tensor_apply]
    rw [
      <-types_comp_apply (g := T.map _), <-types_comp_apply (g := T.map _),
      <-T.map_comp, <-T.map_comp]
    rfl
  rightUnitor_rightStrength _ := rfl
  rightStrength_associator _ _ _ := by
    funext ⟨tx, ⟨ty, tz⟩⟩; simp only [types_comp_apply, associator_inv_apply,
      whiskerRight_apply]
    rw [
      <-types_comp_apply (g := T.map _), <-types_comp_apply (g := T.map _),
      <-T.map_comp, <-T.map_comp]
    rfl
  η_rightStrength _ _ := by
    funext ⟨tx, y⟩; simp only [Functor.id_obj, types_comp_apply, whiskerRight_apply]
    rw [<-types_comp_apply (g := T.map _), <-T.η.naturality]
    rfl
  μ_rightStrength _ _ := by
    funext ⟨tx, y⟩; simp only [Functor.comp_obj, types_comp_apply, whiskerRight_apply]
    rw [
      <-types_comp_apply (g := T.map _), <-T.μ.naturality, <-types_comp_apply (g := T.map _),
      <-T.map_comp]
    rfl
  leftStrength_rightStrength _ _ _ := by
    funext ⟨⟨x, ty⟩, z⟩; simp only [types_comp_apply, whiskerRight_apply,
      associator_hom_apply, whiskerLeft_apply]
    rw [
      <-types_comp_apply (g := T.map _), <-types_comp_apply (g := T.map _),
      <-T.map_comp, <-T.map_comp, <-types_comp_apply (g := T.map _),
      <-T.map_comp
    ]
    rfl

--GOAL: a strong monad on a monoidal category induces a premonoidal category

class CommutativeMonad (T : Monad C) extends Strength T where
  is_commutative : ∀(X Y : C),
    leftStrength (T.obj X) Y ≫ T.map (rightStrength X Y) ≫ T.μ.app (X ⊗ Y)
      = rightStrength X (T.obj Y) ≫ T.map (leftStrength X Y) ≫ T.μ.app (X ⊗ Y)

attribute [reassoc] CommutativeMonad.is_commutative

--TODO: commutative monads for `Set`

--GOAL: a commutative monad on a monoidal category induces another monoidal category

end CategoryTheory
