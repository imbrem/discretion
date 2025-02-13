import Discretion.Distributive.Category
import Discretion.MorphismProperty.BinaryProducts

namespace CategoryTheory.MorphismProperty

open Monoidal

variable {C : Type u} [Category C] [MonoidalCategoryStruct C] [CC : ChosenFiniteCoproducts C]
                      [DistributiveCategory C]

class Distributive (W : MorphismProperty C) extends Cocartesian W : Prop where
  distl_inv_mem : ∀{X Y Z : C}, W (δl⁻¹ X Y Z : _ ⟶ _)
  distr_inv_mem : ∀{X Y Z : C}, W (δr⁻¹ X Y Z : _ ⟶ _)

end CategoryTheory.MorphismProperty
