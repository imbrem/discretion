import Mathlib.CategoryTheory.MorphismProperty.Composition

namespace CategoryTheory.MorphismProperty

def identities (C) [Category C] : MorphismProperty C := λ X Y f => ∃p: X = Y, f = p ▸ 𝟙 X

variable {C} [Category C]

instance IsMultiplicative.instIdentities : IsMultiplicative (identities C) where
  id_mem X := ⟨rfl, rfl⟩
  comp_mem _ _
  | ⟨pf, hf⟩, ⟨pg, hg⟩ => by cases pf; cases hf; cases pg; cases hg; exact ⟨rfl, by simp⟩

instance HasTwoOutOfThreeProperty.instIdentities : HasTwoOutOfThreeProperty (identities C) where
  of_postcomp _ _
  | ⟨pg, hg⟩, ⟨pfg, hgf⟩ => by
    cases pg; cases pfg; cases hg; simp only [Category.comp_id] at hgf; cases hgf; exact ⟨rfl, rfl⟩
  of_precomp _ _
  | ⟨pf, hf⟩, ⟨pfg, hgf⟩ => by
    cases pf; cases pfg; cases hf; simp only [Category.id_comp] at hgf; cases hgf; exact ⟨rfl, rfl⟩

theorem StableUnderInverse.identities : StableUnderInverse (identities C)
  := λX Y ⟨f, g, hfg, hgf⟩ ⟨pf, hf⟩
  => by cases pf; simp only at hf; cases hf; simp only [Category.id_comp] at hfg; exact ⟨rfl, hfg⟩

theorem StableUnderInverse.monomorphisms : StableUnderInverse (monomorphisms C)
  := λ_ _ f _ => IsIso.mono_of_iso f.inv

theorem StableUnderInverse.epimorphisms : StableUnderInverse (epimorphisms C)
  := λ_ _ f _ => IsIso.epi_of_iso f.inv

theorem StableUnderInverse.isomorphisms : StableUnderInverse (isomorphisms C)
  := λ_ _ ⟨f, _, hfg, hgf⟩ _ => ⟨f, hgf, hfg⟩

theorem inv_mem_of_stable_under_inverse {W : MorphismProperty C}
  (h : StableUnderInverse W) {X Y : C} {f : X ⟶ Y} [IsIso f] (hf : W f) : W (inv f)
  := h ⟨f, inv f, by simp, by simp⟩ hf

theorem stable_under_inverse_of_inv_mem {W : MorphismProperty C}
  (h : ∀{X Y : C} {f : X ⟶ Y} [IsIso f], W f → W (inv f)) {X Y : C} {f : X ≅ Y} (hf : W f.hom)
  : W f.inv := by convert h hf using 1; simp

theorem stable_under_inverse_iff_inv_mem {W : MorphismProperty C}
  : StableUnderInverse W ↔ ∀{X Y : C} {f : X ⟶ Y} [IsIso f], W f → W (inv f) :=
  ⟨inv_mem_of_stable_under_inverse, stable_under_inverse_of_inv_mem⟩

class IsStableUnderInverse (W : MorphismProperty C) : Prop where
  stable_under_inverse : StableUnderInverse W

set_option linter.unusedVariables false in
theorem IsStableUnderInverse.of_inv_mem {W : MorphismProperty C}
  (h : ∀{X Y : C} {f : X ⟶ Y} [hfi : IsIso f], W f → W (inv f)) : IsStableUnderInverse W
  := ⟨λ_ _ _ hf => stable_under_inverse_of_inv_mem h hf⟩

theorem stable_under_inverse {W : MorphismProperty C} [IsStableUnderInverse W]
  : StableUnderInverse W := IsStableUnderInverse.stable_under_inverse

theorem inv_mem {W : MorphismProperty C} [IsStableUnderInverse W] {X Y : C} {f : X ⟶ Y}
  [IsIso f] (hf : W f) : W (inv f) := inv_mem_of_stable_under_inverse stable_under_inverse hf

theorem IsStableUnderInverse.instIdentities : IsStableUnderInverse (identities C) where
  stable_under_inverse := StableUnderInverse.identities

theorem IsStableUnderInverse.instMonomorphisms : IsStableUnderInverse (monomorphisms C) where
  stable_under_inverse := StableUnderInverse.monomorphisms

theorem IsStableUnderInverse.instEpimorphisms : IsStableUnderInverse (epimorphisms C) where
  stable_under_inverse := StableUnderInverse.epimorphisms

theorem IsStableUnderInverse.instIsomorphisms : IsStableUnderInverse (isomorphisms C) where
  stable_under_inverse := StableUnderInverse.isomorphisms

class IsEndo (W : MorphismProperty C) : Prop where
  is_endo {X Y : C} {f : X ⟶ Y} : W f → X = Y

theorem is_endo {W : MorphismProperty C} [IsEndo W] {X Y : C} {f : X ⟶ Y}
  : W f → X = Y := IsEndo.is_endo

instance IsEndo.instIdentities : IsEndo (identities C) where
  is_endo hf := hf.1

class IsIso (W : MorphismProperty C) : Prop where
  is_iso {X Y : C} {f : X ⟶ Y} : W f → CategoryTheory.IsIso f

theorem is_iso {W : MorphismProperty C} [IsIso W] {X Y : C} {f : X ⟶ Y}
  : W f → CategoryTheory.IsIso f := IsIso.is_iso

instance IsIso.instIdentities : IsIso (identities C) where
  is_iso | ⟨p, hf⟩ => by cases p; cases hf; exact CategoryTheory.IsIso.id _

instance IsIso.instIsomorphisms : IsIso (isomorphisms C) where
  is_iso hf := hf

class IsAuto (W : MorphismProperty C) : Prop where
  is_auto {X : C} {f : X ⟶ X} : W f → CategoryTheory.IsIso f

theorem is_auto {W : MorphismProperty C} [IsAuto W] {X : C} {f : X ⟶ X}
  : W f → CategoryTheory.IsIso f := IsAuto.is_auto

instance IsAuto.ofIsIso {W : MorphismProperty C} [IsIso W] : IsAuto W where
  is_auto hf := is_iso hf

class HasIso (W : MorphismProperty C) : Type _ where
  hasIso {X Y : C} {f : X ⟶ Y} : W f → Iso X Y

def hasIso {W : MorphismProperty C} [HasIso W] {X Y : C} {f : X ⟶ Y} (hf : W f) : Iso X Y :=
  HasIso.hasIso hf

-- TODO: inflore

-- TODO: set as low priority?
noncomputable instance HasIso.ofIsIso {W : MorphismProperty C} [IsIso W] : HasIso W where
  hasIso := λ{_ _ f} hf => have _ := is_iso hf; asIso f

class Unique (W : MorphismProperty C) : Prop where
  unique : ∀{X Y : C} {f g : X ⟶ Y}, W f → W g → f = g

theorem unique {W : MorphismProperty C} [Unique W] {X Y : C} {f g : X ⟶ Y}
  (hf : W f) (hg : W g) : f = g := Unique.unique hf hg

-- TODO: make simp lemma?
theorem eq_id {W : MorphismProperty C} [Unique W] [ContainsIdentities W] {X : C} {f : X ⟶ X}
  (hf : W f) : f = 𝟙 X := unique hf (id_mem W X)

theorem comp_eq_id {W : MorphismProperty C} [Unique W] [IsMultiplicative W] {X Y : C}
  {f : X ⟶ Y} {g : Y ⟶ X} (hf : W f) (hg : W g)
  : f ≫ g = 𝟙 X := eq_id (comp_mem _ _ _ hf hg)

theorem IsAuto.ofUnique {W : MorphismProperty C} [Unique W] [ContainsIdentities W] : IsAuto W where
  is_auto hf := eq_id hf ▸ IsIso.id _

instance Unique.inf_left {W W' : MorphismProperty C} [Unique W] : Unique (W ⊓ W') where
  unique hf hg := unique hf.1 hg.1

instance Unique.inf_right {W W' : MorphismProperty C} [Unique W'] : Unique (W ⊓ W') where
  unique hf hg := unique hf.2 hg.2

instance Unique.instIdentities : Unique (identities C) where
  unique | ⟨pf, hf⟩, ⟨pg, hg⟩ => by cases hf; cases hg; exact rfl
