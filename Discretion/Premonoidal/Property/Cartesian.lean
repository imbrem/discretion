import Discretion.Monoidal.Braided.Basic
import Discretion.Premonoidal.Property.Basic
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Widesubcategory
import Discretion.MorphismProperty.CartesianSubcategory
import Discretion.Premonoidal.Property.WideSubcategory

namespace CategoryTheory.MorphismProperty

open Limits

open MonoidalCategory'

open scoped MonoidalCategory

variable {C} [Category C] [PremonoidalCategory C]

class CartesianMonoidal (W : MorphismProperty C) : Type _ extends IsMonoidal W where
  fst : ∀(X Y : WideSubcategory W), (X ⊗ Y) ⟶ X
  snd : ∀(X Y : WideSubcategory W), (X ⊗ Y) ⟶ Y
  monoidal_product_is_cartesian
    : ∀(X Y : WideSubcategory W), IsLimit (BinaryFan.mk (fst X Y) (snd X Y))
  monoidal_unit_is_terminal
    : IsTerminal (𝟙_ (WideSubcategory W))

-- TODO: if a morphism property is CartesianMonoidal, then its WideSubcategory has
-- ChosenFiniteProducts
