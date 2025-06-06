import Discretion.Poset2.Basic
import Discretion.ChosenFiniteCoproducts

namespace CategoryTheory

open ChosenFiniteCoproducts

class DescMono (C : Type u) [Category C] [ChosenFiniteCoproducts C] [Refines C]
  : Prop where
  refines_desc : ∀{X Y Z : C} {f f' : X ⟶ Z} {g g' : Y ⟶ Z},
    f ↠ f' → g ↠ g' → desc f g ↠ desc f' g'

export DescMono (refines_desc)

instance DescMono.ofDiscrete {C : Type u}
  [Category C] [ChosenFiniteCoproducts C] [Poset2 C] [RefinesIsDiscrete C]
  : DescMono C where
  refines_desc ff' gg' := by cases (eq_of_refines ff'); cases (eq_of_refines gg'); rfl

instance Disc2.instChosenFiniteCoproducts {C : Type u} [Category C] [ℳ : ChosenFiniteCoproducts C]
  : ChosenFiniteCoproducts (Disc2 C) := ℳ

theorem refines_addHom {C : Type u} [Category C] [ChosenFiniteCoproducts C]
  [Poset2 C] [DescMono C]
  {X Y X' Y' : C} {f f' : X ⟶ X'} {g g' : Y ⟶ Y'} (ff' : f ↠ f') (gg' : g ↠ g')
  : addHom f g ↠ addHom f' g' := by
  unfold addHom
  apply refines_desc
  apply refines_comp ff'
  rfl
  apply refines_comp gg'
  rfl

end CategoryTheory
