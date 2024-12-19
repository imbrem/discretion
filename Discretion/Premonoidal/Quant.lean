import Mathlib.CategoryTheory.Monoidal.Free.Basic
import Discretion.Wk.Quant

namespace CategoryTheory

open MonoidalCategory

class HasQuant (τ : Type u) where
  quant : τ → Quant

class MonoidalQuant (C : Type u) [Category C] [MonoidalCategoryStruct C] extends HasQuant C where
  le_quant_tensor : ∀{X Y : C}, quant X ⊓ quant Y ≤ quant (X ⊗ Y)
  quant_unit : quant (𝟙_ C) = ⊤

class StrictQuant (C : Type u) [Category C] [MonoidalCategoryStruct C] extends MonoidalQuant C where
  quant_tensor : ∀{X Y : C}, quant (X ⊗ Y) = quant X ⊓ quant Y
  le_quant_tensor := quant_tensor ▸ le_refl _

-- TODO: coherent quant : X ≃_{SymMon} Y => quant X = quant Y

-- TODO: strict quant ==> coherent quant

open HasQuant

variable {C}

section HasQuant

variable [HasQuant C]

class IsRelevant (X : C) : Prop where
  copy_le_quant : .copy ≤ quant X

class IsAffine (X : C) : Prop where
  del_le_quant : .del ≤ quant X

class IsNonlinear (X : C) : Prop where
  quant_eq_top : quant X = ⊤

theorem IsNonlinear.copy_le_quant {X : C} [IsNonlinear X] : .copy ≤ quant X
  := by rw [IsNonlinear.quant_eq_top]; decide

theorem IsNonlinear.del_le_quant {X : C} [IsNonlinear X] : .del ≤ quant X
  := by rw [IsNonlinear.quant_eq_top]; decide

instance IsNonlinear.of_relevant_affine {X : C} [IsRelevant X] [IsAffine X] : IsNonlinear X where
  quant_eq_top := by
    convert sup_le IsRelevant.copy_le_quant (IsAffine.del_le_quant (X := X)) using 0
    generalize quant X = q
    cases q <;> decide

instance IsNonlinear.relevant {X : C} [IsNonlinear X] : IsRelevant X where
  copy_le_quant := IsNonlinear.copy_le_quant

instance IsNonlinear.affine {X : C} [IsNonlinear X] : IsAffine X where
  del_le_quant := IsNonlinear.del_le_quant

end HasQuant

section MonoidalQuant

open MonoidalQuant

variable [Category C] [MonoidalCategoryStruct C] [MonoidalQuant C]

instance IsNonlinear.unit : IsNonlinear (𝟙_ C) where
  quant_eq_top := quant_unit

instance IsRelevant.unit : IsRelevant (𝟙_ C) := inferInstance

instance IsAffine.unit : IsAffine (𝟙_ C) := inferInstance

instance IsRelevant.tensor {X Y : C} [IsRelevant X] [IsRelevant Y] : IsRelevant (X ⊗ Y) where
  copy_le_quant := le_trans (le_inf copy_le_quant copy_le_quant) le_quant_tensor

instance IsAffine.tensor {X Y : C} [IsAffine X] [IsAffine Y] : IsAffine (X ⊗ Y) where
  del_le_quant := le_trans (le_inf del_le_quant del_le_quant) le_quant_tensor

instance IsNonlinear.tensor {X Y : C} [IsNonlinear X] [IsNonlinear Y] : IsNonlinear (X ⊗ Y)
  := inferInstance

end MonoidalQuant

class HasPQuant (τ : Type u) [LE τ] [Bot τ] where
  pquant : τ → PQuant
  pquant_bot : pquant (⊥ : τ) = ⊤
  pquant_anti : ∀lo hi : τ, lo ≤ hi → pquant hi ≤ pquant lo

class EffectSystem (ε : Type u) [PartialOrder ε] [BoundedOrder ε] : Sort _ where
  commutes : ε → ε → Prop
  commutes_symm : ∀e₁ e₂, commutes e₁ e₂ → commutes e₂ e₁
  commutes_anti_right : ∀e₁ e₂ e₂', e₂ ≤ e₂' → commutes e₁ e₂' → commutes e₁ e₂
  central_bot : commutes ⊥ ⊤

namespace EffectSystem

scoped infixr:50 " ‖ " => commutes

end EffectSystem

open EffectSystem

variable {ε} [PartialOrder ε] [BoundedOrder ε] [EffectSystem ε]

theorem commutes_symm  {l r : ε} : l ‖ r → r ‖ l := EffectSystem.commutes_symm l r

theorem commutes_anti_right {l r r' : ε} (hr : r ≤ r') : l ‖ r' → l ‖ r
  := EffectSystem.commutes_anti_right l r r' hr

theorem commutes_anti_left {l l' r : ε} (hl : l ≤ l') (hlr : l' ‖ r) : l ‖ r
  := commutes_symm <| commutes_anti_right hl (commutes_symm hlr)

theorem commutes_anti {l l' r r' : ε} (hl : l ≤ l') (hr : r ≤ r') (hlr : l' ‖ r') : l ‖ r
  := commutes_anti_right hr (commutes_anti_left hl hlr)

theorem central_bot : (⊥ : ε) ‖ ⊤ := EffectSystem.central_bot

theorem commutes_bot_left {r : ε} : (⊥ : ε) ‖ r := commutes_anti_right le_top central_bot

theorem commutes_bot_right {l : ε} : l ‖ (⊥ : ε) := commutes_symm commutes_bot_left
