import Discretion.Premonoidal.Category
import Discretion.MorphismProperty.Basic

namespace CategoryTheory.MorphismProperty

open MonoidalCategory

open Monoidal

inductive monoidal (C) [Category C] [MonoidalCategoryStruct C] : MorphismProperty C
  | id : ∀ {X : C}, monoidal C (𝟙 X)
  | comp : monoidal C f → monoidal C g → monoidal C (f ≫ g)
  | whiskerLeft : monoidal C f → monoidal C (X ◁ f)
  | whiskerRight : monoidal C f → monoidal C (f ▷ Y)
  | associator_hom : monoidal C (α_ X Y Z).hom
  | associator_inv : monoidal C (α_ X Y Z).inv
  | left_unitor_hom : monoidal C (λ_ X).hom
  | left_unitor_inv : monoidal C (λ_ X).inv
  | right_unitor_hom : monoidal C (ρ_ X).hom
  | right_unitor_inv : monoidal C (ρ_ X).inv

variable {C : Type _} [Category C]

section MonoidalCategoryStruct

variable  [MonoidalCategoryStruct C]

class IsStableUnderWhisker (W : MorphismProperty C) : Prop where
  whiskerLeft_mem : ∀ {X Y Z : C} (f : X ⟶ Y), W f → W (Z ◁ f)
  whiskerRight_mem : ∀ {X Y Z : C} (f : X ⟶ Y), W f → W (f ▷ Z)

theorem whiskerLeft_mem {W : MorphismProperty C} [IsStableUnderWhisker W] {X Y Z : C}
  {f : X ⟶ Y} (hf : W f) : W (Z ◁ f) := IsStableUnderWhisker.whiskerLeft_mem f hf

theorem whiskerRight_mem {W : MorphismProperty C} [IsStableUnderWhisker W] {X Y Z : C}
  {f : X ⟶ Y} (hf : W f) : W (f ▷ Z) := IsStableUnderWhisker.whiskerRight_mem f hf

class ContainsMonoidal (W : MorphismProperty C) extends
  ContainsIdentities W, IsStableUnderComposition W, IsStableUnderWhisker W : Prop where
  associator_hom_mem : ∀ {X Y Z : C}, W (α_ X Y Z).hom
  associator_inv_mem : ∀ {X Y Z : C}, W (α_ X Y Z).inv
  left_unitor_hom_mem : ∀ {X : C}, W (λ_ X).hom
  left_unitor_inv_mem : ∀ {X : C}, W (λ_ X).inv
  right_unitor_hom_mem : ∀ {X : C}, W (ρ_ X).hom
  right_unitor_inv_mem : ∀ {X : C}, W (ρ_ X).inv

instance ContainsMonoidal.instMonoidal : ContainsMonoidal (monoidal C) where
  id_mem _ := monoidal.id
  comp_mem _ _ := monoidal.comp
  whiskerLeft_mem _ := monoidal.whiskerLeft
  whiskerRight_mem _ := monoidal.whiskerRight
  associator_hom_mem := monoidal.associator_hom
  associator_inv_mem := monoidal.associator_inv
  left_unitor_hom_mem := monoidal.left_unitor_hom
  left_unitor_inv_mem := monoidal.left_unitor_inv
  right_unitor_hom_mem := monoidal.right_unitor_hom
  right_unitor_inv_mem := monoidal.right_unitor_inv

-- TODO: inf lore; monoidal is the smallest ContainsMonoidal

section IsPremonoidal

variable [IsPremonoidal C]

instance IsIso.instMonoidal : IsIso (monoidal C) where
  is_iso hf := by induction hf <;> infer_instance

instance IsStableUnderInverse.instMonoidal
  : IsStableUnderInverse (monoidal C)
  := of_inv_mem (λ{X Y} f {hfi} hf => by
  induction hf with
  | id => convert monoidal.id; simp
  | comp hf hg =>
    have hf' := is_iso hf
    have hg' := is_iso hg
    rw [IsIso.inv_comp]
    apply monoidal.comp <;> apply_assumption
  | whiskerLeft hf =>
    have hf' := is_iso hf
    rw [Monoidal.inv_whiskerLeft]
    apply monoidal.whiskerLeft ; apply_assumption
  | whiskerRight hf =>
    have hf' := is_iso hf
    rw [Monoidal.inv_whiskerRight]
    apply monoidal.whiskerRight ; apply_assumption
  | _ => simp; constructor
  )

-- TODO: this is premonoidal coherence

-- instance Unique.instMonoidal : Unique (monoidal C) where
--   unique hf hg := sorry

end IsPremonoidal
