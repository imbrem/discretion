import Discretion.Elgot.Iterate

namespace CategoryTheory.MorphismProperty

open ChosenFiniteCoproducts

variable {C : Type u} [Category C] [ChosenFiniteCoproducts C] [Iterate C]

class ContainsIterates (W : MorphismProperty C) where
  iterate_mem : ∀ {X Y : C} (f : X ⟶ (Y ⊕ₒ X)), W f → W (iterate f)

class Uniform
  (L R : MorphismProperty C) : Prop where
  uniform {X Y : C} {f : Y ⟶ Z ⊕ₒ Y} {g : X ⟶ Z ⊕ₒ X} {h : X ⟶ Y}
    : L h → R f → h ≫ f = g ≫ ((𝟙 Z) ⊕ₕ h) → h ≫ iterate f = iterate g

end CategoryTheory.MorphismProperty
