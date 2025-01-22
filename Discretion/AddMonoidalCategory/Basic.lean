import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import Discretion.Utils.Category

namespace CategoryTheory

open MonoidalCategory

-- class AddMonoidalCategoryStruct (C : Type _) [Category C] where
--   addObj : C → C → C
--   addHom : ∀ {X Y X' Y' : C}, (X ⟶ Y) → (X' ⟶ Y') → (addObj X X' ⟶ addObj Y Y')
--   addLeft (X : C) {Y₁ Y₂ : C} (f : Y₁ ⟶ Y₂) : addObj X Y₁ ⟶ addObj X Y₂ := addHom (𝟙 X) f
--   addRight {X₁ X₂ : C} (f : X₁ ⟶ X₂) (Y : C) : addObj X₁ Y ⟶ addObj X₂ Y := addHom f (𝟙 Y)
--   zeroObj : C
--   addAssoc : ∀ (X Y Z : C), addObj (addObj X Y) Z ≅ addObj X (addObj Y Z)
--   addComm : ∀ (X Y : C), addObj X Y ≅ addObj Y X
--   leftZero : ∀ (X : C), addObj zeroObj X ≅ X
--   rightZero : ∀ (X : C), addObj X zeroObj ≅ X

-- namespace Monoidal

-- scoped infixr:70 " +ₒ " => AddMonoidalCategoryStruct.addObj

-- scoped infixr:81 " ◁⁺ " => AddMonoidalCategoryStruct.addLeft

-- scoped infixl:81 " ▷⁺ " => AddMonoidalCategoryStruct.addRight

-- scoped infixr:70 " +ₕ " => AddMonoidalCategoryStruct.addHom

-- scoped notation "𝟘_ " C:max => (AddMonoidalCategoryStruct.zeroObj : C)

-- open Lean PrettyPrinter.Delaborator SubExpr in
-- @[delab app.CategoryTheory.AddMonoidalCategoryStruct.zeroObj]
-- def delabZeroObj : Delab := whenPPOption getPPNotation <| withOverApp 3 do
--   let e ← getExpr
--   guard <| e.isAppOfArity ``AddMonoidalCategoryStruct.zeroObj 3
--   let C ← withNaryArg 0 delab
--   `(𝟘_ $C)

-- scoped notation "α⁺" => AddMonoidalCategoryStruct.addAssoc

-- scoped notation "λ⁺" => AddMonoidalCategoryStruct.leftZero

-- scoped notation "ρ⁺" => AddMonoidalCategoryStruct.rightZero

-- end Monoidal

-- open Monoidal

class AddMonoidalCategory (C : Type _) [Category C] where
  addMonoidal : MonoidalCategory C
  addSymmetric : SymmetricCategory C

namespace Monoidal

open AddMonoidalCategory

variable {C : Type _} [Category C] [AddMonoidalCategory C]

def addObj : C → C → C := addMonoidal.tensorObj

def addUnit : C := addMonoidal.tensorUnit

scoped infixr:70 " +ₒ " => addObj

scoped notation "𝟘_ " C:max => (addUnit : C)

open Lean PrettyPrinter.Delaborator SubExpr in
@[delab app.CategoryTheory.Monoidal.addUnit]
def delabZeroObj : Delab := whenPPOption getPPNotation <| withOverApp 3 do
  let e ← getExpr
  guard <| e.isAppOfArity ``Monoidal.addUnit 3
  let C ← withNaryArg 0 delab
  `(𝟘_ $C)

def addLeft (X) {Y₁ Y₂ : C} (f : Y₁ ⟶ Y₂) : X +ₒ Y₁ ⟶ X +ₒ Y₂ := addMonoidal.whiskerLeft X f

def addRight {X₁ X₂ : C} (f : X₁ ⟶ X₂) (Y) : X₁ +ₒ Y ⟶ X₂ +ₒ Y := addMonoidal.whiskerRight f Y

def addHom : ∀ {X Y X' Y' : C}, (X ⟶ Y) → (X' ⟶ Y') → (X +ₒ X' ⟶ Y +ₒ Y') := addMonoidal.tensorHom

scoped infixr:81 " ◁⁺ " => addLeft

scoped infixl:81 " ▷⁺ " => addRight

scoped infixr:70 " +ₕ " => addHom

def addAssoc : ∀ (X Y Z : C), (X +ₒ Y) +ₒ Z ≅ X +ₒ (Y +ₒ Z) := addMonoidal.associator

def leftZero : ∀ (X : C), 𝟘_ C +ₒ X ≅ X := addMonoidal.leftUnitor

def rightZero : ∀ (X : C), X +ₒ 𝟘_ C ≅ X := addMonoidal.rightUnitor

def addSymm : ∀ (X Y : C), X +ₒ Y ≅ Y +ₒ X := addSymmetric.braiding

scoped notation "α⁺" => addAssoc

scoped notation "λ⁺" => leftZero

scoped notation "ρ⁺" => rightZero

scoped notation "σ⁺" => addSymm

@[reassoc]
theorem addHom_def {X₁ Y₁ X₂ Y₂ : C} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) :
    f +ₕ g = (f ▷⁺ X₂) ≫ (Y₁ ◁⁺ g) := addMonoidal.tensorHom_def f g

theorem add_id (X Y : C) : 𝟙 X +ₕ 𝟙 Y = 𝟙 (X +ₒ Y) := addMonoidal.tensor_id X Y

@[reassoc]
theorem add_comp
  : ∀ {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : C} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (g₁ : Y₁ ⟶ Z₁) (g₂ : Y₂ ⟶ Z₂),
    (f₁ ≫ g₁) +ₕ (f₂ ≫ g₂) = (f₁ +ₕ f₂) ≫ (g₁ +ₕ g₂) := addMonoidal.tensor_comp

@[reassoc, simp]
theorem addLeft_id : ∀ (X Y : C), X ◁⁺ 𝟙 Y = 𝟙 (X +ₒ Y) := addMonoidal.whiskerLeft_id

@[reassoc, simp]
theorem id_addRight : ∀ (X Y : C), 𝟙 X ▷⁺ Y = 𝟙 (X +ₒ Y) := addMonoidal.id_whiskerRight

@[reassoc]
theorem addAssoc_naturality :
  ∀ {X₁ X₂ X₃ Y₁ Y₂ Y₃ : C} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (f₃ : X₃ ⟶ Y₃),
    ((f₁ +ₕ f₂) +ₕ f₃) ≫ (α⁺ Y₁ Y₂ Y₃).hom = (α⁺ X₁ X₂ X₃).hom ≫ (f₁ +ₕ (f₂ +ₕ f₃))
  := addMonoidal.associator_naturality

@[reassoc]
theorem leftZero_naturality : ∀ {X Y : C} (f : X ⟶ Y), 𝟘_ _ ◁⁺ f ≫ (λ⁺ Y).hom = (λ⁺ X).hom ≫ f
  := addMonoidal.leftUnitor_naturality

@[reassoc]
theorem rightZero_naturality : ∀ {X Y : C} (f : X ⟶ Y), f ▷⁺ 𝟘_ _ ≫ (ρ⁺ Y).hom = (ρ⁺ X).hom ≫ f
  := addMonoidal.rightUnitor_naturality

@[reassoc (attr := simp)]
theorem add_pentagon :
  ∀ W X Y Z : C,
      (α⁺ W X Y).hom ▷⁺ Z ≫ (α⁺ W (X +ₒ Y) Z).hom ≫ W ◁⁺ (α⁺ X Y Z).hom =
        (α⁺ (W +ₒ X) Y Z).hom ≫ (α⁺ W X (Y +ₒ Z)).hom
  := addMonoidal.pentagon

@[reassoc (attr := simp)]
theorem add_triangle :
  ∀ X Y : C, (α⁺ X (𝟘_ _) Y).hom ≫ X ◁⁺ (λ⁺ Y).hom = (ρ⁺ X).hom ▷⁺ Y := addMonoidal.triangle

end Monoidal

-- TODO: factor this into its own file?
