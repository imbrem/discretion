import Discretion.Distributive.Property
import Discretion.Poset2.ChosenFiniteProducts
import Discretion.Poset2.Effectful

namespace CategoryTheory

class Distributive2 (C : Type u)
  [Category C] [MonoidalCategoryStruct C] [BraidedCategoryStruct C] [ChosenFiniteCoproducts C]
  (E : Type v) [EffectSystem E] extends Effectful2 C E, DistributiveCategory C, DescMono C where
  eff_distributive: ∀e, (eff e).Distributive
