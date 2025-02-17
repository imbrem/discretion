import Discretion.Poset2.Basic
import Discretion.ChosenFiniteCoproducts

namespace CategoryTheory

open ChosenFiniteProducts

open ChosenFiniteCoproducts

class LiftMono (C : Type u) [Category C] [ChosenFiniteProducts C] [Refines C]
  : Prop where
  lift_mono : ∀{X Y Z : C} (f f' : Z ⟶ X) (g g' : Z ⟶ Y), f ↠ f' → g ↠ g' → lift f g ↠ lift f' g'

class DescMono (C : Type u) [Category C] [ChosenFiniteCoproducts C] [Refines C]
  : Prop where
  desc_mono : ∀{X Y Z : C} (f f' : X ⟶ Z) (g g' : Y ⟶ Z), f ↠ f' → g ↠ g' → desc f g ↠ desc f' g'

instance LiftMono.ofDiscrete {C : Type u}
  [Category C] [ChosenFiniteProducts C] [Poset2 C] [RefinesIsDiscrete C]
  : LiftMono C where
  lift_mono f f' g g' ff' gg' := by cases (eq_of_refines ff'); cases (eq_of_refines gg'); rfl

instance DescMono.ofDiscrete {C : Type u}
  [Category C] [ChosenFiniteCoproducts C] [Poset2 C] [RefinesIsDiscrete C]
  : DescMono C where
  desc_mono f f' g g' ff' gg' := by cases (eq_of_refines ff'); cases (eq_of_refines gg'); rfl

instance Disc2.instChosenFiniteProducts {C : Type u} [Category C] [ℳ : ChosenFiniteProducts C]
  : ChosenFiniteProducts (Disc2 C) := ℳ

instance Disc2.instChosenFiniteCoproducts {C : Type u} [Category C] [ℳ : ChosenFiniteCoproducts C]
  : ChosenFiniteCoproducts (Disc2 C) := ℳ

end CategoryTheory
