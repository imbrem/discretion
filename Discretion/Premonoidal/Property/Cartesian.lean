import Discretion.Premonoidal.Braided
import Discretion.Premonoidal.Property.Basic
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Widesubcategory
import Discretion.MorphismProperty.CartesianSubcategory

namespace CategoryTheory.MorphismProperty

open Limits

open MonoidalCategory

open Monoidal

variable {C} [Category C] [MonoidalCategoryStruct C]

class CartesianMonoidal (W : MorphismProperty C) extends IsMultiplicative W : Type _ where
  fst : ∀(X Y : C), (X ⊗ Y) ⟶ X
  snd : ∀(X Y : C), (X ⊗ Y) ⟶ Y
  fst_prop : ∀(X Y : C), W (fst X Y)
  snd_prop : ∀(X Y : C), W (snd X Y)
  monoidal_product_is_cartesian : ∀(X Y : C), IsLimit (BinaryFan.mk (fst X Y) (snd X Y))
  monoidal_unit_is_terminal : IsTerminal (𝟙_ C)
