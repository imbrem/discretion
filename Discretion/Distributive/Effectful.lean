import Discretion.Premonoidal.Effectful
import Discretion.Distributive.Property

namespace CategoryTheory

class DistributiveEffectful (C : Type u)
  [Category C] [MonoidalCategoryStruct C] [BraidedCategoryStruct C] [ChosenFiniteCoproducts C]
  (E : Type v) [EffectSystem E] extends EffectfulCategory C E, DistributiveCategory C where
  eff_distributive: ∀e, (eff e).Distributive
