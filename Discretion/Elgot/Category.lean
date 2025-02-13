import Discretion.Distributive.Effectful
import Discretion.Elgot.Strong
import Discretion.Elgot.Property
import Mathlib.Order.Defs.Unbundled

namespace CategoryTheory

open ChosenFiniteCoproducts

open HasCommRel

class ElgotCategory (C : Type u)
  [Category C] [MonoidalCategoryStruct C] [BraidedCategoryStruct C] [ChosenFiniteCoproducts C]
  [Iterate C] [O : ∀X Y : C, PartialOrder (X ⟶ Y)]
  (E : Type v) [EffectSystem E]
  extends DistributiveEffectful C E where
  iterative : Set E
  iterative_is_upper : IsUpperSet iterative
  top_iterative : ⊤ ∈ iterative
  contains_iterates : ∀e ∈ iterative, (eff e).ContainsIterates
  right_mover_right_uniform : ∀{e e' : E}, e ⇀ e' → (eff e).RightUniform (eff e')
  left_mover_left_uniform : ∀{e e' : E}, e ↽ e' → (eff e).LeftUniform (eff e')
