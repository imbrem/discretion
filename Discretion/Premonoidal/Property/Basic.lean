import Discretion.Premonoidal.Category
import Discretion.MorphismProperty.Basic
import Discretion.MorphismProperty.Mul

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

@[simp]
theorem associator_hom_mem {W : MorphismProperty C} [ContainsMonoidalStructure W] {X Y Z : C}
  : W (α_ X Y Z).hom := ContainsMonoidalStructure.associator_hom_mem

@[simp]
theorem associator_inv_mem {W : MorphismProperty C} [ContainsMonoidalStructure W] {X Y Z : C}
  : W (α_ X Y Z).inv := ContainsMonoidalStructure.associator_inv_mem

@[simp]
theorem leftUnitor_hom_mem {W : MorphismProperty C} [ContainsMonoidalStructure W] {X : C}
  : W (λ_ X).hom := ContainsMonoidalStructure.leftUnitor_hom_mem

@[simp]
theorem leftUnitor_inv_mem {W : MorphismProperty C} [ContainsMonoidalStructure W] {X : C}
  : W (λ_ X).inv := ContainsMonoidalStructure.leftUnitor_inv_mem

@[simp]
theorem rightUnitor_hom_mem {W : MorphismProperty C} [ContainsMonoidalStructure W] {X : C}
  : W (ρ_ X).hom := ContainsMonoidalStructure.rightUnitor_hom_mem

@[simp]
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

theorem ContainsMonoidalStructure.of_le {W W' : MorphismProperty C}
  (h : W ≤ W') [ContainsMonoidalStructure W] : ContainsMonoidalStructure W' where
  associator_hom_mem := h _ associator_hom_mem
  associator_inv_mem := h _ associator_inv_mem
  leftUnitor_hom_mem := h _ leftUnitor_hom_mem
  leftUnitor_inv_mem := h _ leftUnitor_inv_mem
  rightUnitor_hom_mem := h _ rightUnitor_hom_mem
  rightUnitor_inv_mem := h _ rightUnitor_inv_mem

-- TODO: should these be instances?
instance ContainsMonoidalStructure.sup_left {W W' : MorphismProperty C}
  [ContainsMonoidalStructure W] : ContainsMonoidalStructure (W ⊔ W') := of_le le_sup_left

instance ContainsMonoidalStructure.sup_right {W W' : MorphismProperty C}
  [ContainsMonoidalStructure W'] : ContainsMonoidalStructure (W ⊔ W') := of_le le_sup_right

instance ContainsMonoidalStructure.cc {W : MorphismProperty C} [ContainsMonoidalStructure W]
  : ContainsMonoidalStructure (cc W) := of_le (cc_increasing W)

instance ContainsMonoidalStructure.mul_left {W W' : MorphismProperty C}
  [ContainsMonoidalStructure W] : ContainsMonoidalStructure (W * W') := of_le le_mul_left

instance ContainsMonoidalStructure.mul_right {W W' : MorphismProperty C}
  [ContainsMonoidalStructure W'] : ContainsMonoidalStructure (W * W') := of_le le_mul_right

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

class IsMonoidal (W : MorphismProperty C) extends
  ContainsMonoidalStructure W,
  IsMultiplicative W,
  IsStableUnderWhisker W : Prop where

instance {W : MorphismProperty C}
  [ContainsMonoidalStructure W] [IsMultiplicative W] [IsStableUnderWhisker W]
  : IsMonoidal W := ⟨⟩

@[simp]
theorem monoidal_le {W : MorphismProperty C} [IsMonoidal W] : monoidal C ≤ W :=
  by intro X Y f hf; induction hf using monoidal.induction' with
  | comp _ _ hf hg => exact comp_mem _ _ _ hf hg
  | whiskerLeft _ hf => exact whiskerLeft_mem hf
  | whiskerRight _ hf => exact whiskerRight_mem hf
  | _ => simp [id_mem, *]

theorem sup_monoidal {W : MorphismProperty C} [IsMonoidal W] : W ⊔ monoidal C = W := by simp

theorem monoidal_sup {W : MorphismProperty C} [IsMonoidal W] : monoidal C ⊔ W = W := by simp

@[simp]
theorem mul_monoidal {W : MorphismProperty C} [IsMonoidal W] : W * monoidal C = W
  := by simp [mul_def, cc_of_stable]

@[simp]
theorem monoidal_mul {W : MorphismProperty C} [IsMonoidal W] : monoidal C * W = W
  := by simp [mul_def, cc_of_stable]

instance IsMonoidal.instWhiskerClosure {W : MorphismProperty C} [ContainsMonoidalStructure W]
  : IsMonoidal (whiskerClosure W) where
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

instance IsMonoidal.instMonoidalClosure {W : MorphismProperty C}
  : IsMonoidal (monoidalClosure W) := instWhiskerClosure

instance IsMonoidal.instMonoidal {C : Type _} [Category C] [MonoidalCategoryStruct C]
  : IsMonoidal (monoidal C) := instMonoidalClosure

theorem IsMonoidal.inf {W W' : MorphismProperty C}
  [IsMonoidal W] [IsMonoidal W'] : IsMonoidal (W ⊓ W') := inferInstance

-- TODO: inf lore; monoidal is the smallest ContainsMonoidal

def center (C) [Category C] [MonoidalCategoryStruct C] : MorphismProperty C
  := λ _ _  f => Monoidal.Central f

class Central (W : MorphismProperty C) : Prop where
  central {X Y : C} {f : X ⟶ Y} : W f → Monoidal.Central f

instance Central.instCenter : Central (center C) where
  central hf := hf

instance Central.instBot : Central (⊥ : MorphismProperty C) where
  central hf := False.elim hf

instance Central.sup {W W' : MorphismProperty C} [Central W] [Central W']
  : Central (W ⊔ W') where
  central hf := by cases hf with
    | inl hf => exact central hf
    | inr hf => exact central hf

-- TODO: should these be instances?
instance Central.inf_left {W W' : MorphismProperty C} [Central W] : Central (W ⊓ W') where
  central hf := central hf.1

instance Central.inf_right {W W' : MorphismProperty C} [Central W'] : Central (W ⊓ W') where
  central hf := central hf.2

theorem mem_central {W : MorphismProperty C} [Central W] {X Y : C} {f : X ⟶ Y}
  (hf : W f) : Monoidal.Central f := Central.central hf

class MonoidalHom {X Y : C} (f : X ⟶ Y) where
  prop : monoidal C f

instance MonoidalHom.id {X : C} : MonoidalHom (𝟙 X) where
  prop := monoidal.id

instance MonoidalHom.whiskerLeft {X Y Z : C} (f : X ⟶ Y)
  [MonoidalHom f] : MonoidalHom (Z ◁ f) where
  prop := monoidal.whiskerLeft MonoidalHom.prop

instance MonoidalHom.whiskerRight {X Y Z : C} (f : X ⟶ Y)
  [MonoidalHom f] : MonoidalHom (f ▷ Z) where
  prop := monoidal.whiskerRight MonoidalHom.prop

instance MonoidalHom.comp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)
  [MonoidalHom f] [MonoidalHom g] : MonoidalHom (f ≫ g) where
  prop := monoidal.comp MonoidalHom.prop MonoidalHom.prop

instance MonoidalHom.associator_hom {X Y Z : C}
  : MonoidalHom (α_ X Y Z).hom where
  prop := monoidal.associator_hom

instance MonoidalHom.associator_inv {X Y Z : C}
  : MonoidalHom (α_ X Y Z).inv where
  prop := monoidal.associator_inv

instance MonoidalHom.leftUnitor_hom {X : C}
  : MonoidalHom (λ_ X).hom where
  prop := monoidal.leftUnitor_hom

instance MonoidalHom.leftUnitor_inv {X : C}
  : MonoidalHom (λ_ X).inv where
  prop := monoidal.leftUnitor_inv

instance MonoidalHom.rightUnitor_hom {X : C}
  : MonoidalHom (ρ_ X).hom where
  prop := monoidal.rightUnitor_hom

instance MonoidalHom.rightUnitor_inv {X : C}
  : MonoidalHom (ρ_ X).inv where
  prop := monoidal.rightUnitor_inv

section IsBinoidal

variable [IsBinoidal C]

instance IsStableUnderWhisker.cc {W : MorphismProperty C} [IsStableUnderWhisker W]
  : IsStableUnderWhisker (cc W) where
  whiskerLeft_mem f hf := by induction hf with
    | base f hf => exact cc.base _  (whiskerLeft_mem f hf)
    | comp f g hf hg If Ig => convert cc.comp _ _ If Ig; simp
  whiskerRight_mem f hf := by induction hf with
    | base f hf => exact cc.base _  (whiskerRight_mem f hf)
    | comp f g hf hg If Ig => convert cc.comp _ _ If Ig; simp

theorem IsMonoidal.cc {W : MorphismProperty C} [IsMonoidal W] : IsMonoidal (cc W) := inferInstance

instance Central.cc {W : MorphismProperty C} [Central W] : Central (cc W) where
  central hf := by induction hf with
    | base f hf => exact central hf
    | comp f g hf hg If Ig => exact Central.comp

instance IsStableUnderWhisker.mul {W W' : MorphismProperty C}
  [IsStableUnderWhisker W] [IsStableUnderWhisker W'] : IsStableUnderWhisker (W * W') := cc

theorem IsMonoidal.mul {W W' : MorphismProperty C}
  [IsMonoidal W] [IsMonoidal W'] : IsMonoidal (W * W') := inferInstance

instance Central.mul {W W' : MorphismProperty C} [Central W] [Central W'] : Central (W * W') := cc

theorem tensorHom_mem {W : MorphismProperty C}
  [IsStableUnderWhisker W] [IsStableUnderComposition W] {X Y X' Y' : C}
  {f : X ⟶ Y} {g : X' ⟶ Y'} (hf : W f) (hg : W g) : W (f ⊗ g)
  := by rw [Monoidal.tensorHom_def];
        apply comp_mem; exact whiskerRight_mem hf; exact whiskerLeft_mem hg

instance MonoidalHom.tensorHom {X Y X' Y' : C} {f : X ⟶ Y} {g : X' ⟶ Y'}
  [MonoidalHom f] [MonoidalHom g] : MonoidalHom (f ⊗ g) where
  prop := tensorHom_mem MonoidalHom.prop MonoidalHom.prop

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
  := of_inv_mem (λ{X Y} f {hfi} hf => by cases hf <;> simp)

instance IsStableUnderInverse.instMonoidalClosure {W : MorphismProperty C}
  [IsIso W] [IsStableUnderInverse W]
  : IsStableUnderInverse (monoidalClosure W)
  := instWhiskerClosure

instance IsStableUnderInverse.instMonoidal
  : IsStableUnderInverse (monoidal C)
  := instMonoidalClosure

theorem StableUnderInverse.center : StableUnderInverse (center C)
  := λ _ _ _ hf => Monoidal.Central.inv_hom (hf := hf)

theorem IsStableUnderInverse.instCenter : IsStableUnderInverse (center C) where
  stable_under_inverse := StableUnderInverse.center

end IsBinoidal

section IsPremonoidal

variable [IsPremonoidal C]

instance Central.instMonoidal
  : Central (monoidal C) where
  central hf := by induction hf using monoidal.induction' <;> infer_instance

instance IsMonoidal.instCenter : IsMonoidal (center C) where
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

instance MonoidalHom.instCentral {X Y : C} {f : X ⟶ Y} [MonoidalHom f] : Monoidal.Central f
  := mem_central MonoidalHom.prop

end IsPremonoidal

end MorphismProperty

open MorphismProperty
