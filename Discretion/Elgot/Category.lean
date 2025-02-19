import Discretion.Distributive.Effectful
import Discretion.Elgot.Strong
import Discretion.Elgot.Property
import Mathlib.Order.Defs.Unbundled

namespace CategoryTheory

open ChosenFiniteCoproducts

open HasCommRel

class ElgotCategory (C : Type u)
  [Category C] [PremonoidalCategory C] [BraidedCategory' C] [ChosenFiniteCoproducts C]
  [Iterate C] (E : Type v) [ES : IterEffectSystem E]
  extends DistributiveEffectful C E where
  contains_iterates : ∀e ∈ ES.iterative, (eff e).ContainsIterates
  commutative_uniform : ∀{e e' : E}, e ⇌ e' → (eff e).Uniform (eff e')
