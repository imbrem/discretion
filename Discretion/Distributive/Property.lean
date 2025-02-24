import Discretion.Distributive.Category
import Discretion.MorphismProperty.BinaryProducts
import Discretion.Premonoidal.Property.Basic

namespace CategoryTheory.MorphismProperty

open MonoidalCategory' DistributiveCategory

variable {C : Type u} [Category C] [MonoidalCategoryStruct C] [CC : ChosenFiniteCoproducts C]
                      [DistributiveCategory C]

-- Note: IsMonoidal W and Cocartesian W ==> contains distl, distr

-- If closed under inverses, we get `Distributive` for free

class Distributive (W : MorphismProperty C) extends IsMonoidal W, ContainsCoproducts W : Prop where
  distl_inv_mem : ∀{X Y Z : C}, W ((∂L X Y Z).inv : _ ⟶ _)
  distr_inv_mem : ∀{X Y Z : C}, W ((∂R X Y Z).inv : _ ⟶ _)

end CategoryTheory.MorphismProperty
