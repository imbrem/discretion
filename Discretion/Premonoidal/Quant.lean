import Mathlib.CategoryTheory.Monoidal.Free.Basic
import Discretion.Wk.Quant

open CategoryTheory

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
