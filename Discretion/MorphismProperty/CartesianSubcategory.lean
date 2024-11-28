
import Mathlib.CategoryTheory.MorphismProperty.Composition
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts
import Mathlib.CategoryTheory.Widesubcategory

import Discretion.MorphismProperty.BinaryProducts

namespace CategoryTheory.MorphismProperty

open Limits

variable {C} [Category C]

class IsCartesian (W : MorphismProperty C) extends IsMultiplicative W : Prop where
  subcategory_has_binary_products : HasFiniteProducts (WideSubcategory W)

class IsCocartesian (W : MorphismProperty C) extends IsMultiplicative W : Prop where
  subcategory_has_binary_coproducts : HasFiniteCoproducts (WideSubcategory W)

-- instance ContainsCoproducts.instIsCoCartesian {W : MorphismProperty C} [ContainsCoproducts W]
--   : IsCocartesian W where
--   subcategory_has_binary_coproducts := {
--     has_colimit := sorry
--   }
