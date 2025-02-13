import Discretion.Premonoidal.Effectful
import Discretion.Elgot.Category
import Discretion.Poset2.Distributive

namespace CategoryTheory

open ChosenFiniteCoproducts

namespace MorphismProperty

variable {C : Type u} [Category C] [ChosenFiniteCoproducts C] [Iterate C]

class RightUniform
  [O : ∀X Y : C, LE (X ⟶ Y)] (L R : MorphismProperty C) : Prop where
  left_uniform {X Y : C} {f : Y ⟶ Z ⊕ₒ Y} {g : X ⟶ Z ⊕ₒ X} {h : X ⟶ Y}
    : L h → R f → R g → h ≫ f ≤ g ≫ ((𝟙 Z) ⊕ₕ h) → h ≫ iterate f ≤ iterate g

class LeftUniform
  [O : ∀X Y : C, LE (X ⟶ Y)] (L R : MorphismProperty C) : Prop where
  right_uniform {X Y : C} {f : Y ⟶ Z ⊕ₒ Y} {g : X ⟶ Z ⊕ₒ X} {h : X ⟶ Y}
    : L h → R f → R g → h ≫ f ≥ g ≫ ((𝟙 Z) ⊕ₕ h) → h ≫ iterate f ≥ iterate g

end MorphismProperty

open HasCommRel

class Elgot2 (C : Type u)
  [Category C] [MonoidalCategoryStruct C] [BraidedCategoryStruct C] [ChosenFiniteCoproducts C]
  [Iterate C] (E : Type v) [EffectSystem E]
  extends Distributive2 C E where
  iterative : Set E
  iterative_is_upper : IsUpperSet iterative
  top_iterative : ⊤ ∈ iterative
  contains_iterates : ∀e ∈ iterative, (eff e).ContainsIterates
  right_mover_right_uniform : ∀{e e' : E}, e ⇀ e' → (eff e).RightUniform (eff e')
  left_mover_left_uniform : ∀{e e' : E}, e ↽ e' → (eff e).LeftUniform (eff e')

end CategoryTheory
