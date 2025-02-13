import Discretion.Elgot.Iterate

namespace CategoryTheory.MorphismProperty

open ChosenFiniteCoproducts

variable {C : Type u} [Category C] [ChosenFiniteCoproducts C] [Iterate C]

class ContainsIterates (W : MorphismProperty C) where
  iterate_mem : ∀ {X Y : C} (f : X ⟶ (Y ⊕ₒ X)), W f → W (iterate f)

class IsoUniform
  (L R : MorphismProperty C) : Prop where
  uniform {X Y : C} {f : Y ⟶ Z ⊕ₒ Y} {g : X ⟶ Z ⊕ₒ X} {h : X ⟶ Y}
    : L h → R f → R g → h ≫ f = g ≫ ((𝟙 Z) ⊕ₕ h) → h ≫ iterate f = iterate g

class RightUniform
  [O : ∀X Y : C, PartialOrder (X ⟶ Y)] (L R : MorphismProperty C) : Prop where
  left_uniform {X Y : C} {f : Y ⟶ Z ⊕ₒ Y} {g : X ⟶ Z ⊕ₒ X} {h : X ⟶ Y}
    : L h → R f → R g → h ≫ f ≤ g ≫ ((𝟙 Z) ⊕ₕ h) → h ≫ iterate f ≤ iterate g

class LeftUniform
  [O : ∀X Y : C, PartialOrder (X ⟶ Y)] (L R : MorphismProperty C) : Prop where
  right_uniform {X Y : C} {f : Y ⟶ Z ⊕ₒ Y} {g : X ⟶ Z ⊕ₒ X} {h : X ⟶ Y}
    : L h → R f → R g → h ≫ f ≥ g ≫ ((𝟙 Z) ⊕ₕ h) → h ≫ iterate f ≥ iterate g

end CategoryTheory.MorphismProperty
