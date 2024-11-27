/-
Based on: Mathlib/CategoryTheory/Monoidal/Free/Basic.lean

Copyright (c) 2021 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/

import Discretion.Premonoidal.Property.Basic
import Mathlib.CategoryTheory.Widesubcategory
import Mathlib.CategoryTheory.Monoidal.Free.Coherence

namespace CategoryTheory

open MonoidalCategory

open MorphismProperty

open Monoidal

namespace FreeMonoidalCategory

-- NOTE: the difference between the primed and unprimed functions are that the primed functions
-- only need MonoidalCategoryStruct (and sometimes IsPremonoidal), versus the full MonoidalCategory
section FNotation

local notation "F" => FreeMonoidalCategory

variable {C : Type u} [Category C] {D : Type u} [Category D] [MonoidalCategoryStruct D]

variable (f : C → D)

def projectObj' : F C → D
  | FreeMonoidalCategory.of X => f X
  | FreeMonoidalCategory.unit => 𝟙_ D
  | FreeMonoidalCategory.tensor X Y => projectObj' X ⊗ projectObj' Y

def projectMapAux' : ∀ {X Y : F C}, (Hom X Y) → (projectObj' f X ⟶ projectObj' f Y)
  | _, _, Hom.id _ => 𝟙 _
  | _, _, Hom.α_hom _ _ _ => (α_ _ _ _).hom
  | _, _, Hom.α_inv _ _ _ => (α_ _ _ _).inv
  | _, _, Hom.l_hom _ => (λ_ _).hom
  | _, _, Hom.l_inv _ => (λ_ _).inv
  | _, _, Hom.ρ_hom _ => (ρ_ _).hom
  | _, _, Hom.ρ_inv _ => (ρ_ _).inv
  | _, _, Hom.comp f g => projectMapAux' f ≫ projectMapAux' g
  | _, _, Hom.whiskerLeft X p => projectObj' f X ◁ projectMapAux' p
  | _, _, Hom.whiskerRight p X => projectMapAux' p ▷ projectObj' f X
  | _, _, Hom.tensor f g => projectMapAux' f ⊗ projectMapAux' g

variable [IsPremonoidal D]

instance projectMapAux_monoidal' {X Y : F C} (a : Hom X Y) : MonoidalHom (projectMapAux' f a)
  := by induction a <;> dsimp only [projectMapAux'] <;> infer_instance

def projectMap' (X Y : F C) : (X ⟶ Y) → (projectObj' f X ⟶ projectObj' f Y) :=
  Quotient.lift (projectMapAux' f) <| by
    intro f g h
    induction h with
    | refl => rfl
    | symm _ _ _ hfg' => exact hfg'.symm
    | trans _ _ hfg hgh => exact hfg.trans hgh
    | comp _ _ hf hg => dsimp only [projectMapAux']; rw [hf, hg]
    | whiskerLeft _ _ _ _ hf => dsimp only [projectMapAux']; rw [hf]
    | whiskerRight _ _ _ _ hf => dsimp only [projectMapAux']; rw [hf]
    | tensor _ _ hfg hfg' => dsimp only [projectMapAux']; rw [hfg, hfg']
    | tensorHom_def _ _ =>
        dsimp only [projectMapAux']; rw [Monoidal.tensorHom_def]
    | comp_id => dsimp only [projectMapAux']; rw [Category.comp_id]
    | id_comp => dsimp only [projectMapAux']; rw [Category.id_comp]
    | assoc => dsimp only [projectMapAux']; rw [Category.assoc]
    | tensor_id => dsimp only [projectMapAux']; rw [Monoidal.tensor_id]; rfl
    | tensor_comp => dsimp only [projectMapAux']; rw [Monoidal.tensor_comp_left]
    | whiskerLeft_id =>
        dsimp only [projectMapAux', projectObj']
        rw [Monoidal.whiskerLeft_id]
    | id_whiskerRight =>
        dsimp only [projectMapAux', projectObj']
        rw [Monoidal.id_whiskerRight]
    | α_hom_inv => dsimp only [projectMapAux']; rw [Iso.hom_inv_id]
    | α_inv_hom => dsimp only [projectMapAux']; rw [Iso.inv_hom_id]
    | associator_naturality =>
        dsimp only [projectMapAux']; rw [Monoidal.associator_naturality]
    | ρ_hom_inv => dsimp only [projectMapAux']; rw [Iso.hom_inv_id]
    | ρ_inv_hom => dsimp only [projectMapAux']; rw [Iso.inv_hom_id]
    | ρ_naturality =>
        dsimp only [projectMapAux', projectObj']
        rw [Monoidal.rightUnitor_naturality]
    | l_hom_inv => dsimp only [projectMapAux']; rw [Iso.hom_inv_id]
    | l_inv_hom => dsimp only [projectMapAux']; rw [Iso.inv_hom_id]
    | l_naturality =>
        dsimp only [projectMapAux', projectObj']
        rw [Monoidal.leftUnitor_naturality]
    | pentagon =>
        dsimp only [projectMapAux', projectObj']
        rw [IsPremonoidal.pentagon]
    | triangle =>
        dsimp only [projectMapAux', projectObj']
        rw [IsPremonoidal.triangle]

def project' : F C ⥤ D where
  obj := projectObj' f
  map := projectMap' f _ _
  map_comp := by rintro _ _ _ ⟨_⟩ ⟨_⟩; rfl

end FNotation

end FreeMonoidalCategory

-- Note: for an example of why `Unique (monoidal C)` does not hold in general despite monoidal
-- coherence, see Jose Brox's answer in:
-- https://math.stackexchange.com/questions/3725568/how-does-mac-lanes-coherence-theorem-follow-from-the-fact-that-a-tensor-categor?rq=1

-- TODO: investigate in which cases it _does_ hold
-- For sure: strict monoidal categories
-- Maybe: _non-strict_ monoidal categories a-la
-- https://arxiv.org/abs/2303.16740#:~:text=It%20is%20a%20classical%20result,%2C%20called%20its%20non%2Dstrictification.
