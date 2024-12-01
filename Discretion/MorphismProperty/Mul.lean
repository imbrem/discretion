import Discretion.MorphismProperty.Basic
import Mathlib.Algebra.Group.Defs

namespace CategoryTheory.MorphismProperty

variable {C} [Category C]

inductive cc (W : MorphismProperty C) : MorphismProperty C
  | base : ∀ {X Y : C} (f : X ⟶ Y), W f → cc W f
  | comp : ∀ {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z),
    cc W f → cc W g → cc W (f ≫ g)

theorem cc_mono {W W' : MorphismProperty C}
  (h : W ≤ W') : cc W ≤ cc W' := by intro X Y f hf; induction hf with
  | base f hf => exact cc.base _ (h _ hf)
  | comp f g hf hg ihf ihg => exact cc.comp _ _ ihf ihg

theorem cc_increasing (W : MorphismProperty C) : W ≤ cc W := by
  intro X Y f hf; exact cc.base _ hf

theorem cc_of_stable {W : MorphismProperty C} [IsStableUnderComposition W] : cc W = W := by
  ext X Y f; constructor
  · intro h; induction h with
    | base f hf => exact hf
    | comp f g hf hg If Ig => exact IsStableUnderComposition.comp_mem _ _ If Ig
  · intro h; exact cc.base _ h

instance cc_is_stable_under_composition {W : MorphismProperty C}
  : IsStableUnderComposition (cc W) where
  comp_mem _ _ hf hg := cc.comp _ _ hf hg

theorem cc_idem {W : MorphismProperty C} : cc (cc W) = cc W := by simp [cc_of_stable]

instance cc_contains_identities {W : MorphismProperty C} [ContainsIdentities W]
  : ContainsIdentities (cc W) where
  id_mem X := cc.base _ (id_mem W X)

instance cc_is_multiplicative {W : MorphismProperty C} [ContainsIdentities W]
  : IsMultiplicative (cc W) := ⟨⟩

theorem cc_minimal {W W' : MorphismProperty C} [IsStableUnderComposition W']
  (h : W ≤ W') : cc W ≤ W' := by convert cc_mono h; rw [cc_of_stable]

def mul (W W' : MorphismProperty C) : MorphismProperty C := cc (W ⊔ W')

instance instMul : Mul (MorphismProperty C) := ⟨mul⟩

theorem mul_def {W W' : MorphismProperty C} : W * W' = cc (W ⊔ W') := rfl

theorem mul_minimal {W₁ W₂ W₃ : MorphismProperty C}
  (h₁ : W₁ ≤ W₃) (h₂ : W₂ ≤ W₃) [IsStableUnderComposition W₃] : W₁ * W₂ ≤ W₃
  := cc_minimal (sup_le h₁ h₂)

theorem mul_mono {W W' W₁ W₂ : MorphismProperty C}
  (h₁ : W ≤ W₁) (h₂ : W' ≤ W₂) : W * W' ≤ W₁ * W₂ := cc_mono (sup_le_sup h₁ h₂)

theorem le_mul_left {W W' : MorphismProperty C} : W ≤ W * W'
  := le_sup_left.trans (cc_increasing _)

theorem le_mul_right {W W' : MorphismProperty C} : W' ≤ W * W'
  := le_sup_right.trans (cc_increasing _)

theorem mul_self {W : MorphismProperty C} : W * W = cc W := by simp [mul_def]

theorem mul_assoc {W₁ W₂ W₃ : MorphismProperty C} : (W₁ * W₂) * W₃ = W₁ * (W₂ * W₃) := by
    ext X Y f; constructor
    · intro h; induction h with
      | base f h => cases h with
        | inl h =>
          apply mul_mono
          rfl
          apply le_mul_left
          exact h
        | inr h =>
          apply le_mul_right
          apply le_mul_right
          exact h
      | comp f g hf hg If Ig => exact cc.comp _ _ If Ig
    · intro h; induction h with
      | base f h => cases h with
        | inl h =>
          apply le_mul_left
          apply le_mul_left
          exact h
        | inr h =>
          apply mul_mono
          apply le_mul_right
          rfl
          exact h
      | comp f g hf hg If Ig => exact cc.comp _ _ If Ig

theorem mul_comm {W W' : MorphismProperty C} : W * W' = W' * W := by simp [mul_def, sup_comm]

instance instCommSemigroup : CommSemigroup (MorphismProperty C) where
  mul_assoc _ _ _ := mul_assoc
  mul_comm _ _ := mul_comm

instance mul_is_stable_under_composition {W W' : MorphismProperty C}
  : IsStableUnderComposition (W * W') := cc_is_stable_under_composition

instance mul_contains_identities_left {W W' : MorphismProperty C}
  [ContainsIdentities W] : ContainsIdentities (W * W') where
  id_mem X := cc.base _ (Or.inl (id_mem W X))

instance mul_contains_identities_right {W W' : MorphismProperty C}
  [ContainsIdentities W'] : ContainsIdentities (W * W') where
  id_mem X := cc.base _ (Or.inr (id_mem W' X))

instance mul_is_multiplicative_left {W W' : MorphismProperty C}
  [ContainsIdentities W] : IsMultiplicative (W * W') := ⟨⟩

instance mul_is_multiplicative_right {W W' : MorphismProperty C}
  [ContainsIdentities W'] : IsMultiplicative (W * W') := ⟨⟩

@[simp]
theorem mul_identities {W : MorphismProperty C} [IsMultiplicative W] : W * (identities C) = W
  := calc
  _ = cc W := by simp [mul_def]
  _ = W := cc_of_stable

@[simp]
theorem identities_mul {W : MorphismProperty C} [IsMultiplicative W] : (identities C) * W = W
  := by rw [CommSemigroup.mul_comm, mul_identities]
