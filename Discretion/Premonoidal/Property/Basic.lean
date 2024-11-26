import Discretion.Premonoidal.Category
import Discretion.MorphismProperty.Basic

namespace CategoryTheory

open MonoidalCategory

open Monoidal

-- TODO: IsMonoidal, IsBraided classes?

namespace MorphismProperty

inductive monoidalStructure (C) [Category C] [MonoidalCategoryStruct C] : MorphismProperty C
  | associator_hom : monoidalStructure C (α_ X Y Z).hom
  | associator_inv : monoidalStructure C (α_ X Y Z).inv
  | leftUnitor_hom : monoidalStructure C (λ_ X).hom
  | leftUnitor_inv : monoidalStructure C (λ_ X).inv
  | rightUnitor_hom : monoidalStructure C (ρ_ X).hom
  | rightUnitor_inv : monoidalStructure C (ρ_ X).inv

variable {C : Type _} [Category C] [MonoidalCategoryStruct C]

inductive whiskerClosure (W : MorphismProperty C) : MorphismProperty C
  | id : ∀ {X : C}, whiskerClosure W (𝟙 X)
  | comp : whiskerClosure W f → whiskerClosure W g → whiskerClosure W (f ≫ g)
  | whiskerLeft : whiskerClosure W f → whiskerClosure W (Z ◁ f)
  | whiskerRight : whiskerClosure W f → whiskerClosure W (f ▷ Z)
  | base : W f → whiskerClosure W f

def monoidalClosure (W : MorphismProperty C) : MorphismProperty C
  := whiskerClosure (monoidalStructure C ⊔ W)

@[simp]
theorem monoidalClosure.id {X : C} : monoidalClosure W (𝟙 X) := whiskerClosure.id

theorem monoidalClosure.comp {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z}
  (hf : monoidalClosure W f) (hg : monoidalClosure W g)
  : monoidalClosure W (f ≫ g) := whiskerClosure.comp hf hg

theorem monoidalClosure.whiskerLeft {X Y Z : C} {f : X ⟶ Y}
  (hf : monoidalClosure W f)
  : monoidalClosure W (Z ◁ f) := whiskerClosure.whiskerLeft hf

theorem monoidalClosure.whiskerRight {X Y Z : C} {f : X ⟶ Y}
  (hf : monoidalClosure W f)
  : monoidalClosure W (f ▷ Z) := whiskerClosure.whiskerRight hf

theorem monoidalClosure.monoidal {X Y : C} {f : X ⟶ Y}
  (hf : monoidalStructure C f)
  : monoidalClosure W f := whiskerClosure.base (Or.inl hf)

@[simp]
theorem monoidalClosure.associator_hom {X Y Z : C}
  : monoidalClosure W (α_ X Y Z).hom := monoidal monoidalStructure.associator_hom

@[simp]
theorem monoidalClosure.associator_inv {X Y Z : C}
  : monoidalClosure W (α_ X Y Z).inv := monoidal monoidalStructure.associator_inv

@[simp]
theorem monoidalClosure.leftUnitor_hom {X : C}
  : monoidalClosure W (λ_ X).hom := monoidal monoidalStructure.leftUnitor_hom

@[simp]
theorem monoidalClosure.leftUnitor_inv {X : C}
  : monoidalClosure W (λ_ X).inv := monoidal monoidalStructure.leftUnitor_inv

@[simp]
theorem monoidalClosure.rightUnitor_hom {X : C}
  : monoidalClosure W (ρ_ X).hom := monoidal monoidalStructure.rightUnitor_hom

@[simp]
theorem monoidalClosure.rightUnitor_inv {X : C}
  : monoidalClosure W (ρ_ X).inv := monoidal monoidalStructure.rightUnitor_inv

theorem monoidalClosure.base {X Y : C} {f : X ⟶ Y}
  (hf : W f)
  : monoidalClosure W f := whiskerClosure.base (Or.inr hf)

theorem monoidalClosure.induction
  {motive : ∀ {X Y : C} (f : X ⟶ Y), monoidalClosure W f → Prop}
  (id : ∀ {X : C}, motive (𝟙 X) id)
  (comp : ∀ {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z}
    (hf : monoidalClosure W f) (hg : monoidalClosure W g)
    (_ : motive f hf) (_ : motive g hg),
    motive (f ≫ g) (comp hf hg))
  (whiskerLeft : ∀ {X Y Z : C} {f : X ⟶ Y}
    (hf : monoidalClosure W f)
    (_ : motive f hf),
    motive (Z ◁ f) (whiskerLeft hf))
  (whiskerRight : ∀ {X Y Z : C} {f : X ⟶ Y}
    (hf : monoidalClosure W f)
    (_ : motive f hf),
    motive (f ▷ Z) (whiskerRight hf))
  (monoidal : ∀ {X Y : C} {f : X ⟶ Y}
    (hf : monoidalStructure C f),
    motive f (monoidal hf))
  (base : ∀ {X Y : C} {f : X ⟶ Y}
    (hf : W f),
    motive f (base hf))
  {f : X ⟶ Y} (hf : monoidalClosure W f)
  : motive f hf
  := by induction hf with
  | base hf => cases hf with
    | inl h => exact monoidal h
    | inr h => exact base h
  | _ => apply_assumption <;> assumption

theorem monoidalClosure.induction'
  {motive : ∀ {X Y : C} (f : X ⟶ Y), monoidalClosure W f → Prop}
  (id : ∀ {X : C}, motive (𝟙 X) id)
  (comp : ∀ {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z}
    (hf : monoidalClosure W f) (hg : monoidalClosure W g)
    (_ : motive f hf) (_ : motive g hg),
    motive (f ≫ g) (comp hf hg))
  (whiskerLeft : ∀ {X Y Z : C} {f : X ⟶ Y}
    (hf : monoidalClosure W f)
    (_ : motive f hf),
    motive (Z ◁ f) (whiskerLeft hf))
  (whiskerRight : ∀ {X Y Z : C} {f : X ⟶ Y}
    (hf : monoidalClosure W f)
    (_ : motive f hf),
    motive (f ▷ Z) (whiskerRight hf))
  (associator_hom : ∀{X Y Z : C}, motive (α_ X Y Z).hom associator_hom)
  (associator_inv : ∀{X Y Z : C}, motive (α_ X Y Z).inv associator_inv)
  (leftUnitor_hom : ∀{X : C}, motive (λ_ X).hom leftUnitor_hom)
  (leftUnitor_inv : ∀{X : C}, motive (λ_ X).inv leftUnitor_inv)
  (rightUnitor_hom : ∀{X : C}, motive (ρ_ X).hom rightUnitor_hom)
  (rightUnitor_inv : ∀{X : C}, motive (ρ_ X).inv rightUnitor_inv)
  (base : ∀ {X Y : C} {f : X ⟶ Y}
    (hf : W f),
    motive f (base hf))
  {f : X ⟶ Y} (hf : monoidalClosure W f)
  : motive f hf
  := by induction hf using monoidalClosure.induction with
  | monoidal h => cases h <;> apply_assumption
  | _ => apply_assumption <;> assumption

def monoidal (C) [Category C] [MonoidalCategoryStruct C] : MorphismProperty C
  := monoidalClosure ⊥

@[simp]
theorem monoidal.id {X : C} : monoidal C (𝟙 X) := monoidalClosure.id

theorem monoidal.comp {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z}
  (hf : monoidal C f) (hg : monoidal C g)
  : monoidal C (f ≫ g) := monoidalClosure.comp hf hg

theorem monoidal.whiskerLeft {X Y Z : C} {f : X ⟶ Y}
  (hf : monoidal C f)
  : monoidal C (Z ◁ f) := monoidalClosure.whiskerLeft hf

theorem monoidal.whiskerRight {X Y Z : C} {f : X ⟶ Y}
  (hf : monoidal C f)
  : monoidal C (f ▷ Z) := monoidalClosure.whiskerRight hf

theorem monoidal.s {X Y : C} {f : X ⟶ Y}
  (hf : monoidalStructure C f)
  : monoidal C f := monoidalClosure.monoidal hf

@[simp]
theorem monoidal.associator_hom {X Y Z : C}
  : monoidal C (α_ X Y Z).hom := monoidalClosure.associator_hom

@[simp]
theorem monoidal.associator_inv {X Y Z : C}
  : monoidal C (α_ X Y Z).inv := monoidalClosure.associator_inv

@[simp]
theorem monoidal.leftUnitor_hom {X : C}
  : monoidal C (λ_ X).hom := monoidalClosure.leftUnitor_hom

@[simp]
theorem monoidal.leftUnitor_inv {X : C}
  : monoidal C (λ_ X).inv := monoidalClosure.leftUnitor_inv

@[simp]
theorem monoidal.rightUnitor_hom {X : C}
  : monoidal C (ρ_ X).hom := monoidalClosure.rightUnitor_hom

@[simp]
theorem monoidal.rightUnitor_inv {X : C}
  : monoidal C (ρ_ X).inv := monoidalClosure.rightUnitor_inv

theorem monoidal.induction
  {motive : ∀ {X Y : C} (f : X ⟶ Y), monoidal C f → Prop}
  (id : ∀ {X : C}, motive (𝟙 X) monoidal.id)
  (comp : ∀ {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z}
    (hf : monoidal C f) (hg : monoidal C g)
    (_ : motive f hf) (_ : motive g hg),
    motive (f ≫ g) (monoidal.comp hf hg))
  (whiskerLeft : ∀ {X Y Z : C} {f : X ⟶ Y}
    (hf : monoidal C f)
    (_ : motive f hf),
    motive (Z ◁ f) (monoidal.whiskerLeft hf))
  (whiskerRight : ∀ {X Y Z : C} {f : X ⟶ Y}
    (hf : monoidal C f)
    (_ : motive f hf),
    motive (f ▷ Z) (monoidal.whiskerRight hf))
  (s : ∀ {X Y : C} {f : X ⟶ Y}
    (hf : monoidalStructure C f),
    motive f (monoidal.s hf))
  {f : X ⟶ Y} (hf : monoidal C f)
  : motive f hf
  := by induction hf using monoidalClosure.induction with
  | base h => cases h
  | _ => apply_assumption <;> assumption

theorem monoidal.induction'
  {motive : ∀ {X Y : C} (f : X ⟶ Y), monoidal C f → Prop}
  (id : ∀ {X : C}, motive (𝟙 X) monoidal.id)
  (comp : ∀ {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z}
    (hf : monoidal C f) (hg : monoidal C g)
    (_ : motive f hf) (_ : motive g hg),
    motive (f ≫ g) (monoidal.comp hf hg))
  (whiskerLeft : ∀ {X Y Z : C} {f : X ⟶ Y}
    (hf : monoidal C f)
    (_ : motive f hf),
    motive (Z ◁ f) (monoidal.whiskerLeft hf))
  (whiskerRight : ∀ {X Y Z : C} {f : X ⟶ Y}
    (hf : monoidal C f)
    (_ : motive f hf),
    motive (f ▷ Z) (monoidal.whiskerRight hf))
  (associator_hom : ∀{X Y Z : C}, motive (α_ X Y Z).hom monoidal.associator_hom)
  (associator_inv : ∀{X Y Z : C}, motive (α_ X Y Z).inv monoidal.associator_inv)
  (leftUnitor_hom : ∀{X : C}, motive (λ_ X).hom monoidal.leftUnitor_hom)
  (leftUnitor_inv : ∀{X : C}, motive (λ_ X).inv monoidal.leftUnitor_inv)
  (rightUnitor_hom : ∀{X : C}, motive (ρ_ X).hom monoidal.rightUnitor_hom)
  (rightUnitor_inv : ∀{X : C}, motive (ρ_ X).inv monoidal.rightUnitor_inv)
  {f : X ⟶ Y} (hf : monoidal C f)
  : motive f hf
  := by induction hf using monoidalClosure.induction' with
  | base h => cases h
  | _ => apply_assumption <;> assumption

class IsStableUnderWhisker (W : MorphismProperty C) : Prop where
  whiskerLeft_mem : ∀ {X Y Z : C} (f : X ⟶ Y), W f → W (Z ◁ f)
  whiskerRight_mem : ∀ {X Y Z : C} (f : X ⟶ Y), W f → W (f ▷ Z)

instance IsStableUnderWhisker.instTop : IsStableUnderWhisker (⊤ : MorphismProperty C) where
  whiskerLeft_mem _ _ := True.intro
  whiskerRight_mem _ _ := True.intro

instance IsStableUnderWhisker.instBot : IsStableUnderWhisker (⊥ : MorphismProperty C) where
  whiskerLeft_mem _ := False.elim
  whiskerRight_mem _ := False.elim

theorem whiskerLeft_mem {W : MorphismProperty C} [IsStableUnderWhisker W] {X Y Z : C}
  {f : X ⟶ Y} (hf : W f) : W (Z ◁ f) := IsStableUnderWhisker.whiskerLeft_mem f hf

theorem whiskerRight_mem {W : MorphismProperty C} [IsStableUnderWhisker W] {X Y Z : C}
  {f : X ⟶ Y} (hf : W f) : W (f ▷ Z) := IsStableUnderWhisker.whiskerRight_mem f hf

instance IsStableUnderWhisker.inf {W W' : MorphismProperty C}
  [IsStableUnderWhisker W] [IsStableUnderWhisker W']
  : IsStableUnderWhisker (W ⊓ W') where
  whiskerLeft_mem f hf := ⟨whiskerLeft_mem f hf.1, whiskerLeft_mem f hf.2⟩
  whiskerRight_mem f hf := ⟨whiskerRight_mem f hf.1, whiskerRight_mem f hf.2⟩

instance IsStableUnderWhisker.sup {W W' : MorphismProperty C}
  [IsStableUnderWhisker W] [IsStableUnderWhisker W']
  : IsStableUnderWhisker (W ⊔ W') where
  whiskerLeft_mem f hf := Or.elim hf (Or.inl ∘ whiskerLeft_mem f) (Or.inr ∘ whiskerLeft_mem f)
  whiskerRight_mem f hf := Or.elim hf (Or.inl ∘ whiskerRight_mem f) (Or.inr ∘ whiskerRight_mem f)

class ContainsMonoidalStructure (W : MorphismProperty C) : Prop where
  associator_hom_mem : ∀ {X Y Z : C}, W (α_ X Y Z).hom
  associator_inv_mem : ∀ {X Y Z : C}, W (α_ X Y Z).inv
  leftUnitor_hom_mem : ∀ {X : C}, W (λ_ X).hom
  leftUnitor_inv_mem : ∀ {X : C}, W (λ_ X).inv
  rightUnitor_hom_mem : ∀ {X : C}, W (ρ_ X).hom
  rightUnitor_inv_mem : ∀ {X : C}, W (ρ_ X).inv

theorem associator_hom_mem {W : MorphismProperty C} [ContainsMonoidalStructure W] {X Y Z : C}
  : W (α_ X Y Z).hom := ContainsMonoidalStructure.associator_hom_mem

theorem associator_inv_mem {W : MorphismProperty C} [ContainsMonoidalStructure W] {X Y Z : C}
  : W (α_ X Y Z).inv := ContainsMonoidalStructure.associator_inv_mem

theorem leftUnitor_hom_mem {W : MorphismProperty C} [ContainsMonoidalStructure W] {X : C}
  : W (λ_ X).hom := ContainsMonoidalStructure.leftUnitor_hom_mem

theorem leftUnitor_inv_mem {W : MorphismProperty C} [ContainsMonoidalStructure W] {X : C}
  : W (λ_ X).inv := ContainsMonoidalStructure.leftUnitor_inv_mem

theorem rightUnitor_hom_mem {W : MorphismProperty C} [ContainsMonoidalStructure W] {X : C}
  : W (ρ_ X).hom := ContainsMonoidalStructure.rightUnitor_hom_mem

theorem rightUnitor_inv_mem {W : MorphismProperty C} [ContainsMonoidalStructure W] {X : C}
  : W (ρ_ X).inv := ContainsMonoidalStructure.rightUnitor_inv_mem

instance ContainsMonoidalStructure.instTop : ContainsMonoidalStructure (⊤ : MorphismProperty C)
  where
  associator_hom_mem := True.intro
  associator_inv_mem := True.intro
  leftUnitor_hom_mem := True.intro
  leftUnitor_inv_mem := True.intro
  rightUnitor_hom_mem := True.intro
  rightUnitor_inv_mem := True.intro

instance ContainsMonoidalStructure.sup_left {W W' : MorphismProperty C}
  [ContainsMonoidalStructure W]
  : ContainsMonoidalStructure (W ⊔ W') where
  associator_hom_mem := Or.inl associator_hom_mem
  associator_inv_mem := Or.inl associator_inv_mem
  leftUnitor_hom_mem := Or.inl leftUnitor_hom_mem
  leftUnitor_inv_mem := Or.inl leftUnitor_inv_mem
  rightUnitor_hom_mem := Or.inl rightUnitor_hom_mem
  rightUnitor_inv_mem := Or.inl rightUnitor_inv_mem

instance ContainsMonoidalStructure.sup_right {W W' : MorphismProperty C}
  [ContainsMonoidalStructure W']
  : ContainsMonoidalStructure (W ⊔ W') where
  associator_hom_mem := Or.inr associator_hom_mem
  associator_inv_mem := Or.inr associator_inv_mem
  leftUnitor_hom_mem := Or.inr leftUnitor_hom_mem
  leftUnitor_inv_mem := Or.inr leftUnitor_inv_mem
  rightUnitor_hom_mem := Or.inr rightUnitor_hom_mem
  rightUnitor_inv_mem := Or.inr rightUnitor_inv_mem

instance ContainsMonoidalStructure.inf {W W' : MorphismProperty C}
  [ContainsMonoidalStructure W] [ContainsMonoidalStructure W']
  : ContainsMonoidalStructure (W ⊓ W') where
  associator_hom_mem := ⟨associator_hom_mem, associator_hom_mem⟩
  associator_inv_mem := ⟨associator_inv_mem, associator_inv_mem⟩
  leftUnitor_hom_mem := ⟨leftUnitor_hom_mem, leftUnitor_hom_mem⟩
  leftUnitor_inv_mem := ⟨leftUnitor_inv_mem, leftUnitor_inv_mem⟩
  rightUnitor_hom_mem := ⟨rightUnitor_hom_mem, rightUnitor_hom_mem⟩
  rightUnitor_inv_mem := ⟨rightUnitor_inv_mem, rightUnitor_inv_mem⟩

instance ContainsMonoidalStructure.instMonoidalStructure
  : ContainsMonoidalStructure (monoidalStructure C) where
  associator_hom_mem := monoidalStructure.associator_hom
  associator_inv_mem := monoidalStructure.associator_inv
  leftUnitor_hom_mem := monoidalStructure.leftUnitor_hom
  leftUnitor_inv_mem := monoidalStructure.leftUnitor_inv
  rightUnitor_hom_mem := monoidalStructure.rightUnitor_hom
  rightUnitor_inv_mem := monoidalStructure.rightUnitor_inv

class ContainsMonoidal (W : MorphismProperty C) extends
  ContainsMonoidalStructure W,
  ContainsIdentities W,
  IsStableUnderComposition W,
  IsStableUnderWhisker W : Prop where

instance {W : MorphismProperty C}
  [ContainsMonoidalStructure W] [ContainsIdentities W]
  [IsStableUnderComposition W] [IsStableUnderWhisker W]
  : ContainsMonoidal W := ⟨⟩

instance ContainsMonoidal.instWhiskerClosure {W : MorphismProperty C} [ContainsMonoidalStructure W]
  : ContainsMonoidal (whiskerClosure W) where
  id_mem _ := whiskerClosure.id
  comp_mem _ _ := whiskerClosure.comp
  whiskerLeft_mem _ := whiskerClosure.whiskerLeft
  whiskerRight_mem _ := whiskerClosure.whiskerRight
  associator_hom_mem := whiskerClosure.base associator_hom_mem
  associator_inv_mem := whiskerClosure.base associator_inv_mem
  leftUnitor_hom_mem := whiskerClosure.base leftUnitor_hom_mem
  leftUnitor_inv_mem := whiskerClosure.base leftUnitor_inv_mem
  rightUnitor_hom_mem := whiskerClosure.base rightUnitor_hom_mem
  rightUnitor_inv_mem := whiskerClosure.base rightUnitor_inv_mem

instance ContainsMonoidal.instMonoidalClosure {W : MorphismProperty C}
  : ContainsMonoidal (monoidalClosure W) := instWhiskerClosure

instance ContainsMonoidal.instMonoidal {C : Type _} [Category C] [MonoidalCategoryStruct C]
  : ContainsMonoidal (monoidal C) := instMonoidalClosure

-- TODO: inf lore; monoidal is the smallest ContainsMonoidal

section IsPremonoidal

variable [IsPremonoidal C]

instance IsIso.instWhiskerClosure {W : MorphismProperty C} [IsIso W] : IsIso (whiskerClosure W)
  where is_iso hf := by induction hf with
  | base h => exact is_iso h
  | _ => infer_instance

instance IsIso.instMonoidalStructure : IsIso (monoidalStructure C) where
  is_iso hf := by induction hf <;> infer_instance

instance IsIso.instMonoidalClosure {W : MorphismProperty C} [IsIso W] : IsIso (monoidalClosure W)
  := instWhiskerClosure

instance IsIso.instMonoidal : IsIso (monoidal C) := instMonoidalClosure

instance IsStableUnderInverse.instWhiskerClosure {W : MorphismProperty C}
  [IsIso W] [IsStableUnderInverse W]
  : IsStableUnderInverse (whiskerClosure W)
  := of_inv_mem (λ{X Y} f {hfi} hf => by
  induction hf with
  | id => convert whiskerClosure.id; simp
  | comp hf hg =>
    have hf' := is_iso hf
    have hg' := is_iso hg
    rw [IsIso.inv_comp]
    apply whiskerClosure.comp <;> apply_assumption
  | whiskerLeft hf =>
    have hf' := is_iso hf
    rw [Monoidal.inv_whiskerLeft]
    apply whiskerClosure.whiskerLeft ; apply_assumption
  | whiskerRight hf =>
    have hf' := is_iso hf
    rw [Monoidal.inv_whiskerRight]
    apply whiskerClosure.whiskerRight ; apply_assumption
  | base h => exact whiskerClosure.base (inv_mem h)
  )

instance IsStableUnderInverse.instMonoidalStructure : IsStableUnderInverse (monoidalStructure C)
  := of_inv_mem (λ{X Y} f {hfi} hf => by cases hf <;> simp <;> constructor)

instance IsStableUnderInverse.instMonoidalClosure {W : MorphismProperty C}
  [IsIso W] [IsStableUnderInverse W]
  : IsStableUnderInverse (monoidalClosure W)
  := instWhiskerClosure

instance IsStableUnderInverse.instMonoidal
  : IsStableUnderInverse (monoidal C)
  := instMonoidalClosure

-- TODO: this is premonoidal coherence

-- instance Unique.instMonoidal : Unique (monoidal C) where
--   unique hf hg := sorry

def center (C) [Category C] [MonoidalCategoryStruct C] : MorphismProperty C
  := λ _ _  f => Monoidal.Central f

class Central (W : MorphismProperty C) : Prop where
  central {X Y : C} {f : X ⟶ Y} : W f → Monoidal.Central f

instance Central.instCenter : Central (center C) where
  central hf := hf

theorem StableUnderInverse.center : StableUnderInverse (center C)
  := λ _ _ _ hf => Monoidal.Central.inv_hom (hf := hf)

theorem IsStableUnderInverse.instCenter : IsStableUnderInverse (center C) where
  stable_under_inverse := StableUnderInverse.center

instance ContainsMonoidal.instCenter : ContainsMonoidal (center C) where
  id_mem _ := Monoidal.Central.id
  comp_mem _ _ hf hg := Monoidal.Central.comp (hf := hf) (hg := hg)
  whiskerLeft_mem _ hf := Monoidal.Central.whiskerLeft (hf := hf)
  whiskerRight_mem _ hf := Monoidal.Central.whiskerRight (hf := hf)
  associator_hom_mem := associator_central
  associator_inv_mem := associator_inv_central
  leftUnitor_hom_mem := leftUnitor_central
  leftUnitor_inv_mem := leftUnitor_inv_central
  rightUnitor_hom_mem := rightUnitor_central
  rightUnitor_inv_mem := rightUnitor_inv_central

end IsPremonoidal

end MorphismProperty

open MorphismProperty
