import Discretion.Premonoidal.Category

namespace CategoryTheory

open MonoidalCategory

class BraidedCategoryStruct (C : Type u) [Category C] [MonoidalCategoryStruct C] where
  braiding (X Y : C) : X ⊗ Y ≅ Y ⊗ X

namespace Monoidal

scoped notation "σ_" => λX Y => Iso.hom (BraidedCategoryStruct.braiding X Y)

end Monoidal

open Monoidal

class IsBraided (C : Type u)
  [Category C] [MonoidalCategoryStruct C] [BraidedCategoryStruct C] : Prop where
  braiding_central : ∀ X Y : C, Monoidal.Central (σ_ X Y) := by aesop_cat
  braiding_naturality_right :
    ∀ (X : C) {Y Z : C} (f : Y ⟶ Z),
      X ◁ f ≫ σ_ X Z = σ_ X Y ≫ f ▷ X := by
    aesop_cat
  braiding_naturality_left :
    ∀ {X Y : C} (f : X ⟶ Y) (Z : C),
      f ▷ Z ≫ σ_ Y Z = σ_ X Z ≫ Z ◁ f := by
    aesop_cat
  /-- The first hexagon identity. -/
  hexagon_forward :
    ∀ X Y Z : C,
      (α_ X Y Z).hom ≫ σ_ X (Y ⊗ Z) ≫ (α_ Y Z X).hom =
        (σ_ X Y ▷ Z) ≫ (α_ Y X Z).hom ≫ (Y ◁ σ_ X Z) := by
    aesop_cat
  /-- The second hexagon identity. -/
  hexagon_reverse :
    ∀ X Y Z : C,
      (α_ X Y Z).inv ≫ σ_ (X ⊗ Y) Z ≫ (α_ Z X Y).inv =
        (X ◁ σ_ Y Z) ≫ (α_ X Z Y).inv ≫ (σ_ X Z ▷ Y) := by
    aesop_cat

class IsSymmetric (C : Type u)
  [Category C] [MonoidalCategoryStruct C] [BraidedCategoryStruct C]
  extends IsBraided C : Prop where
  braiding_braiding : ∀ X Y : C, σ_ X Y ≫ σ_ Y X = 𝟙 (X ⊗ Y)

namespace Monoidal

variable {C : Type u} [Category C] [MonoidalCategoryStruct C] [BraidedCategoryStruct C]

section IsBraided

variable [IsBraided C]

@[simp]
instance braiding_central {X Y : C} : Monoidal.Central (σ_ X Y)
  := IsBraided.braiding_central X Y

theorem braiding_naturality_right (X : C) {Y Z : C} (f : Y ⟶ Z) :
  X ◁ f ≫ σ_ X Z = σ_ X Y ≫ f ▷ X := IsBraided.braiding_naturality_right X f

theorem braiding_naturality_left {X Y : C} (f : X ⟶ Y) (Z : C) :
  f ▷ Z ≫ σ_ Y Z = σ_ X Z ≫ Z ◁ f := IsBraided.braiding_naturality_left f Z

theorem ltimes_braiding {X Y X' Y' : C} (f : X ⟶ Y) (g : X' ⟶ Y')
  : f ⋉ g ≫ σ_ Y Y' = σ_ X X' ≫ g ⋊ f := by rw [
    ltimes, Category.assoc, braiding_naturality_right, <-Category.assoc, braiding_naturality_left,
    Category.assoc
  ]

theorem rtimes_braiding {X Y X' Y' : C} (f : X ⟶ Y) (g : X' ⟶ Y')
  : f ⋊ g ≫ σ_ Y Y' = σ_ X X' ≫ g ⋉ f := by rw [
    rtimes, Category.assoc, braiding_naturality_left, <-Category.assoc, braiding_naturality_right,
    Category.assoc
  ]

theorem hexagon_forward (X Y Z : C) :
  (α_ X Y Z).hom ≫ σ_ X (Y ⊗ Z) ≫ (α_ Y Z X).hom =
    (σ_ X Y ▷ Z) ≫ (α_ Y X Z).hom ≫ (Y ◁ σ_ X Z) := IsBraided.hexagon_forward X Y Z

theorem hexagon_reverse (X Y Z : C) :
  (α_ X Y Z).inv ≫ σ_ (X ⊗ Y) Z ≫ (α_ Z X Y).inv =
    (X ◁ σ_ Y Z) ≫ (α_ X Z Y).inv ≫ (σ_ X Z ▷ Y) := IsBraided.hexagon_reverse X Y Z

end IsBraided

section IsSymmetric

variable [IsSymmetric C]

@[simp]
theorem braiding_braiding (X Y : C) : σ_ X Y ≫ σ_ Y X = 𝟙 (X ⊗ Y)
  := IsSymmetric.braiding_braiding X Y

end IsSymmetric

end Monoidal

end CategoryTheory
