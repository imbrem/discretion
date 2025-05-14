import Discretion.MorphismProperty.BinaryProducts

import Mathlib.CategoryTheory.MorphismProperty.Composition
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.CategoryTheory.MorphismProperty.Limits

namespace CategoryTheory.MorphismProperty

open Limits

variable {C} [Category C]

-- theorem IsStableUnderProductsOfShape.pi_map_mem
--   {J : Type*}
--   {W : MorphismProperty C}
--   (hW : IsStableUnderProductsOfShape W J)
--   (X₁ X₂ : J → C)
--   [HasProduct X₁] [HasProduct X₂]
--   (f : ∀j, X₁ j ⟶ X₂ j) (hf : ∀j, W (f j)) : W (Limits.Pi.map f)
--   := hW.condition _ _ _ _ (getLimitCone (Discrete.functor X₁)).isLimit _ _ (λ⟨j⟩ => hf j)

-- ?? is this true ??
-- theorem IsStableUnderProductsOfShape.pi_lift_mem
--   {J : Type*}
--   {W : MorphismProperty C}
--   (hW : IsStableUnderProductsOfShape W J)
--   (X : C) (Y : J → C)
--   [HasProduct Y]
--   (f : ∀j, X ⟶ Y j) (hf : ∀j, W (f j)) : W (Limits.Pi.lift f)
--   := by
--   simp [Pi.lift, Fan.mk]
--   unfold limit.lift
--   convert hW _ _ _ _ _ _ _ _ using 1
