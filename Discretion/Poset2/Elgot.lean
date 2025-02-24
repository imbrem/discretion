import Discretion.Premonoidal.Effectful
import Discretion.Elgot.Category
import Discretion.Poset2.Distributive

namespace CategoryTheory

open ChosenFiniteCoproducts

namespace MorphismProperty

variable {C : Type u} [Category C] [ChosenFiniteCoproducts C] [Iterate C]

class RightUniform
  [Refines C] (L R : MorphismProperty C) : Prop where
  right_uniform {X Y : C} {f : Y ⟶ Z ⊕ₒ Y} {g : X ⟶ Z ⊕ₒ X} {h : X ⟶ Y}
    : L h → R f → R g → h ≫ f ↠ g ≫ ((𝟙 Z) ⊕ₕ h) → h ≫ iterate f ↠ iterate g

class LeftUniform
  [Refines C] (L R : MorphismProperty C) : Prop where
  left_uniform {X Y : C} {f : Y ⟶ Z ⊕ₒ Y} {g : X ⟶ Z ⊕ₒ X} {h : X ⟶ Y}
    : L h → R f → R g → h ≫ f ↞ g ≫ ((𝟙 Z) ⊕ₕ h) → h ≫ iterate f ↞ iterate g

end MorphismProperty

open HasCommRel

class Elgot2 (C : Type u)
  [Category C] [PremonoidalCategory C] [BraidedCategory' C] [ChosenFiniteCoproducts C]
  [Iterate C] (E : Type v) [ES : IterEffectSystem E]
  extends Distributive2 C E where
  contains_iterates : ∀e ∈ ES.iterative, (eff e).ContainsIterates
  right_mover_right_uniform : ∀{e e' : E}, e ⇀ e' → (eff e).RightUniform (eff e')
  left_mover_left_uniform : ∀{e e' : E}, e ↽ e' → (eff e).LeftUniform (eff e')

variable {C : Type u}
          [Category C] [PremonoidalCategory C] [BraidedCategory' C]
          [ChosenFiniteCoproducts C] [IC : Iterate C]
          {E : Type v} [ES : IterEffectSystem E] [EC : Elgot2 C E]

theorem EffectfulCategory.HasEff.iterate {e : E} {X Y : C} (f : X ⟶ Y ⊕ₒ X) (he : e ∈ ES.iterative)
  [HasEff e f] : EC.HasEff e (iterate f) where
  has_eff := (EC.contains_iterates e he).iterate_mem f has_eff


end CategoryTheory
