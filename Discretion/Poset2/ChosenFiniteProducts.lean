import Discretion.Poset2.Basic
import Discretion.ChosenFiniteCoproducts

namespace CategoryTheory

open ChosenFiniteProducts

open ChosenFiniteCoproducts

class LiftMono (C : Type u) [Category C] [ChosenFiniteProducts C] [∀X Y : C, LE (X ⟶ Y)]
  : Prop where
  lift_mono : ∀{X Y Z : C} (f f' : Z ⟶ X) (g g' : Z ⟶ Y), f ≤ f' → g ≤ g' → lift f g ≤ lift f' g'

class DescMono (C : Type u) [Category C] [ChosenFiniteCoproducts C] [∀X Y : C, LE (X ⟶ Y)]
  : Prop where
  desc_mono : ∀{X Y Z : C} (f f' : X ⟶ Z) (g g' : Y ⟶ Z), f ≤ f' → g ≤ g' → desc f g ≤ desc f' g'

instance Disc2.instChosenFiniteProducts {C : Type u} [Category C] [ℳ : ChosenFiniteProducts C]
  : ChosenFiniteProducts (Disc2 C) := ℳ

instance Disc2.instLiftMono {C : Type u} [Category C] [ChosenFiniteProducts C]
  : LiftMono (Disc2 C) where
  lift_mono f f' g g' ff' gg' := by cases ff'; cases gg'; rfl

instance Disc2.instChosenFiniteCoproducts {C : Type u} [Category C] [ℳ : ChosenFiniteCoproducts C]
  : ChosenFiniteCoproducts (Disc2 C) := ℳ

instance Disc2.instDescMono {C : Type u} [Category C] [ChosenFiniteCoproducts C]
  : DescMono (Disc2 C) where
  desc_mono f f' g g' ff' gg' := by cases ff'; cases gg'; rfl

end CategoryTheory
