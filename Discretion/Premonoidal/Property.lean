import Discretion.Premonoidal.Category
import Discretion.Premonoidal.Braided
import Discretion.MorphismProperty.Basic

namespace CategoryTheory.MorphismProperty

open MonoidalCategory

open Monoidal

inductive monoidalStructure (C) [Category C] [MonoidalCategoryStruct C] : MorphismProperty C
  | associator_hom : monoidalStructure C (α_ X Y Z).hom
  | associator_inv : monoidalStructure C (α_ X Y Z).inv
  | leftUnitor_hom : monoidalStructure C (λ_ X).hom
  | leftUnitor_inv : monoidalStructure C (λ_ X).inv
  | rightUnitor_hom : monoidalStructure C (ρ_ X).hom
  | rightUnitor_inv : monoidalStructure C (ρ_ X).inv

inductive braidedStructure (C) [Category C] [MonoidalCategoryStruct C] [BraidedCategoryStruct C]
  : MorphismProperty C
  | monoidal : monoidalStructure C f → braidedStructure C f
  | braiding_hom : braidedStructure C (σ_ X Y)
  | braiding_inv : braidedStructure C (BraidedCategoryStruct.braiding X Y).inv

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

section BraidedCategoryStruct

variable [BraidedCategoryStruct C]

def braidedClosure (W : MorphismProperty C) : MorphismProperty C
  := whiskerClosure (braidedStructure C ⊔ W)

theorem braidedClosure.id {X : C} : braidedClosure W (𝟙 X) := whiskerClosure.id

theorem braidedClosure.comp {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z}
  (hf : braidedClosure W f) (hg : braidedClosure W g)
  : braidedClosure W (f ≫ g) := whiskerClosure.comp hf hg

theorem braidedClosure.whiskerLeft {X Y Z : C} {f : X ⟶ Y}
  (hf : braidedClosure W f)
  : braidedClosure W (Z ◁ f) := whiskerClosure.whiskerLeft hf

theorem braidedClosure.whiskerRight {X Y Z : C} {f : X ⟶ Y}
  (hf : braidedClosure W f)
  : braidedClosure W (f ▷ Z) := whiskerClosure.whiskerRight hf

theorem braidedClosure.monoidalS {X Y : C} {f : X ⟶ Y}
  (hf : monoidalStructure C f)
  : braidedClosure W f := whiskerClosure.base (Or.inl (braidedStructure.monoidal hf))

theorem braidedClosure.braided {X Y : C} {f : X ⟶ Y}
  (hf : braidedStructure C f)
  : braidedClosure W f := whiskerClosure.base (Or.inl hf)

theorem braidedClosure.associator_hom {X Y Z : C}
  : braidedClosure W (α_ X Y Z).hom := monoidalS monoidalStructure.associator_hom

theorem braidedClosure.associator_inv {X Y Z : C}
  : braidedClosure W (α_ X Y Z).inv := monoidalS monoidalStructure.associator_inv

theorem braidedClosure.leftUnitor_hom {X : C}
  : braidedClosure W (λ_ X).hom := monoidalS monoidalStructure.leftUnitor_hom

theorem braidedClosure.leftUnitor_inv {X : C}
  : braidedClosure W (λ_ X).inv := monoidalS monoidalStructure.leftUnitor_inv

theorem braidedClosure.rightUnitor_hom {X : C}
  : braidedClosure W (ρ_ X).hom := monoidalS monoidalStructure.rightUnitor_hom

theorem braidedClosure.rightUnitor_inv {X : C}
  : braidedClosure W (ρ_ X).inv := monoidalS monoidalStructure.rightUnitor_inv

theorem braidedClosure.braiding_hom {X Y : C}
  : braidedClosure W (σ_ X Y) := braided braidedStructure.braiding_hom

theorem braidedClosure.braiding_inv {X Y : C}
  : braidedClosure W (BraidedCategoryStruct.braiding X Y).inv
    := braided braidedStructure.braiding_inv

theorem braidedClosure.base {X Y : C} (f : X ⟶ Y)
  (hf : W f)
  : braidedClosure W f := whiskerClosure.base (Or.inr hf)

theorem braidedClosure.induction {motive : ∀ {X Y : C} (f : X ⟶ Y), braidedClosure W f → Prop}
  (id : ∀ {X : C}, motive (𝟙 X) braidedClosure.id)
  (comp : ∀ {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z}
    (hf : braidedClosure W f) (hg : braidedClosure W g)
    (_ : motive f hf) (_ : motive g hg),
    motive (f ≫ g) (braidedClosure.comp hf hg))
  (whiskerLeft : ∀ {X Y Z : C} {f : X ⟶ Y}
    (hf : braidedClosure W f)
    (_ : motive f hf),
    motive (Z ◁ f) (braidedClosure.whiskerLeft hf))
  (whiskerRight : ∀ {X Y Z : C} {f : X ⟶ Y}
    (hf : braidedClosure W f)
    (_ : motive f hf),
    motive (f ▷ Z) (braidedClosure.whiskerRight hf))
  (braided : ∀ {X Y : C} {f : X ⟶ Y}
    (hf : braidedStructure C f),
    motive f (braidedClosure.braided hf))
  (base : ∀ {X Y : C} {f : X ⟶ Y}
    (hf : W f),
    motive f (braidedClosure.base f hf))
  {f : X ⟶ Y} (hf : braidedClosure W f)
  : motive f hf
  := by induction hf with
  | base h => cases h with | inl h => exact braided h | inr h => exact base h
  | _ => apply_assumption <;> assumption

@[simp]
theorem braidedStructure.associator_hom {X Y Z : C}
  : braidedStructure C (α_ X Y Z).hom := braidedStructure.monoidal monoidalStructure.associator_hom

@[simp]
theorem braidedStructure.associator_inv {X Y Z : C}
  : braidedStructure C (α_ X Y Z).inv := braidedStructure.monoidal monoidalStructure.associator_inv

@[simp]
theorem braidedStructure.leftUnitor_hom {X : C}
  : braidedStructure C (λ_ X).hom := braidedStructure.monoidal monoidalStructure.leftUnitor_hom

@[simp]
theorem braidedStructure.leftUnitor_inv {X : C}
  : braidedStructure C (λ_ X).inv := braidedStructure.monoidal monoidalStructure.leftUnitor_inv

@[simp]
theorem braidedStructure.rightUnitor_hom {X : C}
  : braidedStructure C (ρ_ X).hom := braidedStructure.monoidal monoidalStructure.rightUnitor_hom

@[simp]
theorem braidedStructure.rightUnitor_inv {X : C}
  : braidedStructure C (ρ_ X).inv := braidedStructure.monoidal monoidalStructure.rightUnitor_inv

attribute [simp] braidedStructure.braiding_hom braidedStructure.braiding_inv

theorem braidedStructure.cases' {motive : ∀ {X Y : C} (f : X ⟶ Y), braidedStructure C f → Prop}
  (associator_hom : ∀ {X Y Z : C}, motive (α_ X Y Z).hom braidedStructure.associator_hom)
  (associator_inv : ∀ {X Y Z : C}, motive (α_ X Y Z).inv braidedStructure.associator_inv)
  (leftUnitor_hom : ∀ {X : C}, motive (λ_ X).hom braidedStructure.leftUnitor_hom)
  (leftUnitor_inv : ∀ {X : C}, motive (λ_ X).inv braidedStructure.leftUnitor_inv)
  (rightUnitor_hom : ∀ {X : C}, motive (ρ_ X).hom braidedStructure.rightUnitor_hom)
  (rightUnitor_inv : ∀ {X : C}, motive (ρ_ X).inv braidedStructure.rightUnitor_inv)
  (braiding_hom : ∀ {X Y : C}, motive (σ_ X Y) braidedStructure.braiding_hom)
  (braiding_inv : ∀ {X Y : C},
    motive (BraidedCategoryStruct.braiding X Y).inv braidedStructure.braiding_inv)
  {f : X ⟶ Y} (hf : braidedStructure C f)
  : motive f hf
  := by induction hf with
  | monoidal h => cases h <;> apply_assumption
  | braiding_hom => exact braiding_hom
  | braiding_inv => exact braiding_inv

theorem braidedClosure.induction' {motive : ∀ {X Y : C} (f : X ⟶ Y), braidedClosure W f → Prop}
  (id : ∀ {X : C}, motive (𝟙 X) braidedClosure.id)
  (comp : ∀ {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z}
    (hf : braidedClosure W f) (hg : braidedClosure W g)
    (_ : motive f hf) (_ : motive g hg),
    motive (f ≫ g) (braidedClosure.comp hf hg))
  (whiskerLeft : ∀ {X Y Z : C} {f : X ⟶ Y}
    (hf : braidedClosure W f)
    (_ : motive f hf),
    motive (Z ◁ f) (braidedClosure.whiskerLeft hf))
  (whiskerRight : ∀ {X Y Z : C} {f : X ⟶ Y}
    (hf : braidedClosure W f)
    (_ : motive f hf),
    motive (f ▷ Z) (braidedClosure.whiskerRight hf))
  (associator_hom : ∀{X Y Z : C}, motive
    (α_ X Y Z).hom braidedClosure.associator_hom)
  (associator_inv : ∀{X Y Z : C}, motive
    (α_ X Y Z).inv braidedClosure.associator_inv)
  (leftUnitor_hom : ∀{X : C}, motive
    (λ_ X).hom braidedClosure.leftUnitor_hom)
  (leftUnitor_inv : ∀{X : C}, motive
    (λ_ X).inv braidedClosure.leftUnitor_inv)
  (rightUnitor_hom : ∀{X : C}, motive
    (ρ_ X).hom braidedClosure.rightUnitor_hom)
  (rightUnitor_inv : ∀{X : C}, motive
    (ρ_ X).inv braidedClosure.rightUnitor_inv)
  (braiding_hom : ∀{X Y : C}, motive
    (σ_ X Y) braidedClosure.braiding_hom)
  (braiding_inv : ∀{X Y : C}, motive
    (BraidedCategoryStruct.braiding X Y).inv braidedClosure.braiding_inv)
  (base : ∀ {X Y : C} {f : X ⟶ Y}
    (hf : W f),
    motive f (braidedClosure.base f hf))
  {f : X ⟶ Y} (hf : braidedClosure W f)
  : motive f hf
  := by induction hf using braidedClosure.induction with
  | braided h => cases h using braidedStructure.cases' <;> apply_assumption
  | _ => apply_assumption <;> assumption

def braided (C) [Category C] [MonoidalCategoryStruct C] [BraidedCategoryStruct C]
  : MorphismProperty C
  := braidedClosure ⊥

theorem braided.id {X : C} : braided C (𝟙 X) := braidedClosure.id

theorem braided.comp {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z}
  (hf : braided C f) (hg : braided C g)
  : braided C (f ≫ g) := braidedClosure.comp hf hg

theorem braided.whiskerLeft {X Y Z : C} {f : X ⟶ Y}
  (hf : braided C f)
  : braided C (Z ◁ f) := braidedClosure.whiskerLeft hf

theorem braided.whiskerRight {X Y Z : C} {f : X ⟶ Y}
  (hf : braided C f)
  : braided C (f ▷ Z) := braidedClosure.whiskerRight hf

theorem braided.monoidalS {X Y : C} {f : X ⟶ Y}
  (hf : monoidalStructure C f)
  : braided C f := braidedClosure.monoidalS hf

theorem braided.s {X Y : C} {f : X ⟶ Y}
  (hf : braidedStructure C f)
  : braided C f := braidedClosure.braided hf

theorem braided.associator_hom {X Y Z : C}
  : braided C (α_ X Y Z).hom := braidedClosure.associator_hom

theorem braided.associator_inv {X Y Z : C}
  : braided C (α_ X Y Z).inv := braidedClosure.associator_inv

theorem braided.leftUnitor_hom {X : C}
  : braided C (λ_ X).hom := braidedClosure.leftUnitor_hom

theorem braided.leftUnitor_inv {X : C}
  : braided C (λ_ X).inv := braidedClosure.leftUnitor_inv

theorem braided.rightUnitor_hom {X : C}
  : braided C (ρ_ X).hom := braidedClosure.rightUnitor_hom

theorem braided.rightUnitor_inv {X : C}
  : braided C (ρ_ X).inv := braidedClosure.rightUnitor_inv

theorem braided.braiding_hom {X Y : C}
  : braided C (σ_ X Y) := braidedClosure.braiding_hom

theorem braided.braiding_inv {X Y : C}
  : braided C (BraidedCategoryStruct.braiding X Y).inv
    := braidedClosure.braiding_inv

theorem braided.induction {motive : ∀ {X Y : C} (f : X ⟶ Y), braided C f → Prop}
  (id : ∀ {X : C}, motive (𝟙 X) braided.id)
  (comp : ∀ {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z}
    (hf : braided C f) (hg : braided C g)
    (_ : motive f hf) (_ : motive g hg),
    motive (f ≫ g) (braided.comp hf hg))
  (whiskerLeft : ∀ {X Y Z : C} {f : X ⟶ Y}
    (hf : braided C f)
    (_ : motive f hf),
    motive (Z ◁ f) (braided.whiskerLeft hf))
  (whiskerRight : ∀ {X Y Z : C} {f : X ⟶ Y}
    (hf : braided C f)
    (_ : motive f hf),
    motive (f ▷ Z) (braided.whiskerRight hf))
  (s : ∀ {X Y : C} {f : X ⟶ Y}
    (hf : braidedStructure C f),
    motive f (braided.s hf))
  {f : X ⟶ Y} (hf : braided C f)
  : motive f hf
  := by induction hf using braidedClosure.induction with
  | base h => cases h
  | braided h => exact s h
  | _ => apply_assumption <;> assumption

theorem braided.induction' {motive : ∀ {X Y : C} (f : X ⟶ Y), braided C f → Prop}
  (id : ∀ {X : C}, motive (𝟙 X) braided.id)
  (comp : ∀ {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z}
    (hf : braided C f) (hg : braided C g)
    (_ : motive f hf) (_ : motive g hg),
    motive (f ≫ g) (braided.comp hf hg))
  (whiskerLeft : ∀ {X Y Z : C} {f : X ⟶ Y}
    (hf : braided C f)
    (_ : motive f hf),
    motive (Z ◁ f) (braided.whiskerLeft hf))
  (whiskerRight : ∀ {X Y Z : C} {f : X ⟶ Y}
    (hf : braided C f)
    (_ : motive f hf),
    motive (f ▷ Z) (braided.whiskerRight hf))
  (associator_hom : ∀{X Y Z : C}, motive
    (α_ X Y Z).hom braided.associator_hom)
  (associator_inv : ∀{X Y Z : C}, motive
    (α_ X Y Z).inv braided.associator_inv)
  (leftUnitor_hom : ∀{X : C}, motive
    (λ_ X).hom braided.leftUnitor_hom)
  (leftUnitor_inv : ∀{X : C}, motive
    (λ_ X).inv braided.leftUnitor_inv)
  (rightUnitor_hom : ∀{X : C}, motive
    (ρ_ X).hom braided.rightUnitor_hom)
  (rightUnitor_inv : ∀{X : C}, motive
    (ρ_ X).inv braided.rightUnitor_inv)
  (braiding_hom : ∀{X Y : C}, motive
    (σ_ X Y) braided.braiding_hom)
  (braiding_inv : ∀{X Y : C}, motive
    (BraidedCategoryStruct.braiding X Y).inv braided.braiding_inv)
  {f : X ⟶ Y} (hf : braided C f)
  : motive f hf
  := by induction hf using braidedClosure.induction' with
  | base h => cases h
  | _ => apply_assumption <;> assumption

end BraidedCategoryStruct

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

variable [BraidedCategoryStruct C]

instance IsIso.instBraidedStructure : IsIso (braidedStructure C) where
  is_iso hf := by cases hf using braidedStructure.cases' <;> infer_instance

instance IsIso.instBraidedClosure {W : MorphismProperty C} [IsIso W] : IsIso (braidedClosure W)
  := instWhiskerClosure

instance IsIso.instBraided : IsIso (braided C) := instBraidedClosure

instance IsStableUnderInverse.instBraidedStructure : IsStableUnderInverse (braidedStructure C)
  := of_inv_mem (λ{X Y} f {hfi} hf => by cases hf using braidedStructure.cases' <;> simp)

instance IsStableUnderInverse.instBraidedClosure {W : MorphismProperty C}
  [IsIso W] [IsStableUnderInverse W]
  : IsStableUnderInverse (braidedClosure W)
  := instWhiskerClosure

instance IsStableUnderInverse.instBraided
  : IsStableUnderInverse (braided C)
  := instBraidedClosure

variable [IsBraided C]

end IsPremonoidal
