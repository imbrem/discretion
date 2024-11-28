import Mathlib.CategoryTheory.Monoidal.Category
import Discretion.Utils.Category

namespace CategoryTheory

open MonoidalCategory

class AddMonoidalCategoryStruct (C : Type _) [Category C] where
  addObj : C → C → C
  addHom : ∀ {X Y X' Y' : C}, (X ⟶ Y) → (X' ⟶ Y') → (addObj X X' ⟶ addObj Y Y')
  addLeft (X : C) {Y₁ Y₂ : C} (f : Y₁ ⟶ Y₂) : addObj X Y₁ ⟶ addObj X Y₂ := addHom (𝟙 X) f
  addRight {X₁ X₂ : C} (f : X₁ ⟶ X₂) (Y : C) : addObj X₁ Y ⟶ addObj X₂ Y := addHom f (𝟙 Y)
  zeroObj : C
  addAssoc : ∀ (X Y Z : C), addObj (addObj X Y) Z ≅ addObj X (addObj Y Z)
  leftZero : ∀ (X : C), addObj zeroObj X ≅ X
  rightZero : ∀ (X : C), addObj X zeroObj ≅ X

namespace Monoidal

scoped infixr:70 " +ₒ " => AddMonoidalCategoryStruct.addObj

scoped infixr:81 " ◁⁺ " => AddMonoidalCategoryStruct.addLeft

scoped infixl:81 " ▷⁺ " => AddMonoidalCategoryStruct.addRight

scoped infixr:70 " +ₕ " => AddMonoidalCategoryStruct.addHom

scoped notation "𝟘_ " C:max => (AddMonoidalCategoryStruct.zeroObj : C)

open Lean PrettyPrinter.Delaborator SubExpr in
@[delab app.CategoryTheory.AddMonoidalCategoryStruct.zeroObj]
def delabZeroObj : Delab := whenPPOption getPPNotation <| withOverApp 3 do
  let e ← getExpr
  guard <| e.isAppOfArity ``AddMonoidalCategoryStruct.zeroObj 3
  let C ← withNaryArg 0 delab
  `(𝟘_ $C)

scoped notation "α⁺" => AddMonoidalCategoryStruct.addAssoc

scoped notation "λ⁺" => AddMonoidalCategoryStruct.leftZero

scoped notation "ρ⁺" => AddMonoidalCategoryStruct.rightZero

end Monoidal

open Monoidal

class AddMonoidalCategory (C : Type _) [Category C]
  extends AddMonoidalCategoryStruct C where
  addHom_def {X₁ Y₁ X₂ Y₂ : C} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) :
    f +ₕ g = (f ▷⁺ X₂) ≫ (Y₁ ◁⁺ g) := by
      aesop_cat
  add_id : ∀ {X Y : C}, (𝟙 X) +ₕ (𝟙 Y) = 𝟙 (X +ₒ Y) := by
    aesop_cat
  add_comp :
    ∀ {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : C} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (g₁ : Y₁ ⟶ Z₁) (g₂ : Y₂ ⟶ Z₂),
      (f₁ ≫ g₁) +ₕ (f₂ ≫ g₂) = (f₁ +ₕ f₂) ≫ (g₁ +ₕ g₂) := by
    aesop_cat
  addLeft_id : ∀ (X Y : C), X ◁⁺ 𝟙 Y = 𝟙 (X +ₒ Y) := by
    aesop_cat
  id_addRight : ∀ (X Y : C), 𝟙 X ▷⁺ Y = 𝟙 (X +ₒ Y) := by
    aesop_cat
  addAssoc_naturality : ∀ {X₁ X₂ X₃ Y₁ Y₂ Y₃ : C}
    (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (f₃ : X₃ ⟶ Y₃),
    ((f₁ +ₕ f₂) +ₕ f₃) ≫ (α⁺ Y₁ Y₂ Y₃).hom = (α⁺ X₁ X₂ X₃).hom ≫ (f₁ +ₕ (f₂ +ₕ f₃))
  leftZero_naturality :
    ∀ {X Y : C} (f : X ⟶ Y), (_ ◁⁺ f) ≫ (λ⁺ Y).hom = (λ⁺ X).hom ≫ f := by
    aesop_cat
  rightZero_naturality :
    ∀ {X Y : C} (f : X ⟶ Y), (f ▷⁺ _) ≫ (ρ⁺ Y).hom = (ρ⁺ X).hom ≫ f := by
    aesop_cat
  pentagon :
    ∀ W X Y Z : C,
      (α⁺ W X Y).hom ▷⁺ Z ≫ (α⁺ W (X +ₒ Y) Z).hom ≫ W ◁⁺ (α⁺ X Y Z).hom =
        (α⁺ (W +ₒ X) Y Z).hom ≫ (α⁺ W X (Y +ₒ Z)).hom := by
    aesop_cat
  triangle :
    ∀ X Y : C, (α⁺ X (𝟘_ _) Y).hom ≫ X ◁⁺ (λ⁺ Y).hom = (ρ⁺ X).hom ▷⁺ Y := by
    aesop_cat

attribute [reassoc] AddMonoidalCategory.addHom_def
attribute [reassoc, simp] AddMonoidalCategory.addLeft_id
attribute [reassoc, simp] AddMonoidalCategory.id_addRight
attribute [reassoc] AddMonoidalCategory.add_comp
attribute [simp] AddMonoidalCategory.add_comp
attribute [reassoc] AddMonoidalCategory.addAssoc_naturality
attribute [reassoc] AddMonoidalCategory.leftZero_naturality
attribute [reassoc] AddMonoidalCategory.rightZero_naturality
attribute [reassoc (attr := simp)] AddMonoidalCategory.pentagon
attribute [reassoc (attr := simp)] AddMonoidalCategory.triangle

namespace Monoidal

variable {C : Type _} [Category C] [AddMonoidalCategory C]

export AddMonoidalCategoryStruct
  (addObj addHom addLeft addRight zeroObj addAssoc leftZero rightZero)

export AddMonoidalCategory
  (
    add_id add_comp addLeft_id id_addRight leftZero_naturality
    rightZero_naturality pentagon triangle
  )

end Monoidal

class ChosenCoproducts (C : Type _) [Category C]
  extends AddMonoidalCategory C where
  codiag (X : C) : X +ₒ X ⟶ X
  initial (X : C) : 𝟘_ C ⟶ X
  -- TODO: coproduct lore goes here...
  inl (X Y : C) : X ⟶ X +ₒ Y := (ρ⁺ X).inv ≫ X ◁⁺ initial Y
  inr (X Y : C) : Y ⟶ X +ₒ Y := (λ⁺ Y).inv ≫ initial X ▷⁺ Y
  coprod {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) : X +ₒ Y ⟶ Z := (f +ₕ g) ≫ codiag Z
