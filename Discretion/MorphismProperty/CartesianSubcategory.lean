
import Mathlib.CategoryTheory.MorphismProperty.Composition
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Widesubcategory

namespace CategoryTheory.MorphismProperty

open Limits

variable {C} [Category C]

class IsCartesian (W : MorphismProperty C) extends IsMultiplicative W : Prop where
  subcategory_has_binary_products : HasBinaryProducts (WideSubcategory W)

class IsCocartesian (W : MorphismProperty C) extends IsMultiplicative W : Prop where
  subcategory_has_binary_coproducts : HasBinaryCoproducts (WideSubcategory W)
