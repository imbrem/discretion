import Discretion.Premonoidal.Braided
import Discretion.Premonoidal.Property.Basic

namespace CategoryTheory.MorphismProperty

open MonoidalCategory

open Monoidal

inductive braidedStructure (C) [Category C] [MonoidalCategoryStruct C] [BraidedCategoryStruct C]
  : MorphismProperty C
  | monoidal : monoidalStructure C f → braidedStructure C f
  | braiding_hom : braidedStructure C (σ_ X Y)
  | braiding_inv : braidedStructure C (BraidedCategoryStruct.braiding X Y).inv

variable {C : Type _} [Category C] [MonoidalCategoryStruct C] [BraidedCategoryStruct C]

class ContainsBraidings (W : MorphismProperty C) : Prop where
  braiding_hom_mem : ∀ {X Y : C}, W (σ_ X Y)
  braiding_inv_mem : ∀ {X Y : C}, W (BraidedCategoryStruct.braiding X Y).inv

theorem braiding_hom_mem {W : MorphismProperty C} [ContainsBraidings W] {X Y : C}
  : W (σ_ X Y) := ContainsBraidings.braiding_hom_mem

theorem braiding_inv_mem {W : MorphismProperty C} [ContainsBraidings W] {X Y : C}
  : W (BraidedCategoryStruct.braiding X Y).inv := ContainsBraidings.braiding_inv_mem

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

@[simp]
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

@[simp]
theorem braided.associator_hom {X Y Z : C}
  : braided C (α_ X Y Z).hom := braidedClosure.associator_hom

@[simp]
theorem braided.associator_inv {X Y Z : C}
  : braided C (α_ X Y Z).inv := braidedClosure.associator_inv

@[simp]
theorem braided.leftUnitor_hom {X : C}
  : braided C (λ_ X).hom := braidedClosure.leftUnitor_hom

@[simp]
theorem braided.leftUnitor_inv {X : C}
  : braided C (λ_ X).inv := braidedClosure.leftUnitor_inv

@[simp]
theorem braided.rightUnitor_hom {X : C}
  : braided C (ρ_ X).hom := braidedClosure.rightUnitor_hom

@[simp]
theorem braided.rightUnitor_inv {X : C}
  : braided C (ρ_ X).inv := braidedClosure.rightUnitor_inv

@[simp]
theorem braided.braiding_hom {X Y : C}
  : braided C (σ_ X Y) := braidedClosure.braiding_hom

@[simp]
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

variable [IsPremonoidal C]

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

instance ContainsBraidings.instCenter
  [BraidedCategoryStruct C] [IsBraided C] : ContainsBraidings (center C) where
  braiding_hom_mem := braiding_central
  braiding_inv_mem := braiding_inv_central
