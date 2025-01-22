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

open Monoidal

open Limits

-- TODO: factor this into its own file?

variable {C : Type _} [Category C]

abbrev IsBinaryCoproduct {X Y P : C} (inl : X ⟶ P) (inr : Y ⟶ P)
  := IsColimit (BinaryCofan.mk (X := X) (Y := Y) inl inr)

abbrev IsBinaryCoproduct.desc {W X Y P : C} {inl : X ⟶ P} {inr : Y ⟶ P}
  (coprod : IsBinaryCoproduct inl inr) (f : X ⟶ W) (g : Y ⟶ W) : P ⟶ W
  := IsColimit.desc coprod (BinaryCofan.mk f g)

@[simp, reassoc (attr := simp)]
theorem IsBinaryCoproduct.inl_desc {W X Y P : C} {inl : X ⟶ P} {inr : Y ⟶ P}
  (coprod : IsBinaryCoproduct inl inr) (f : X ⟶ W) (g : Y ⟶ W)
  : inl ≫ coprod.desc f g = f
  := coprod.fac (BinaryCofan.mk f g) ⟨WalkingPair.left⟩

@[simp, reassoc (attr := simp)]
theorem IsBinaryCoproduct.inr_desc {X Y P : C} {inl : X ⟶ P} {inr : Y ⟶ P}
  (coprod : IsBinaryCoproduct inl inr) (f : X ⟶ W) (g : Y ⟶ W)
  : inr ≫ coprod.desc f g = g
  := coprod.fac (BinaryCofan.mk f g) ⟨WalkingPair.right⟩

@[simp, reassoc (attr := simp)]
theorem IsBinaryCoproduct.desc_inl_inr {X Y P : C} {inl : X ⟶ P} {inr : Y ⟶ P}
  (coprod : IsBinaryCoproduct inl inr)
  : coprod.desc inl inr = 𝟙 P
  := coprod.desc_self

theorem IsBinaryCoproduct.desc_comp {X Y P : C} {inl : X ⟶ P} {inr : Y ⟶ P}
  (coprod : IsBinaryCoproduct inl inr) (f : X ⟶ W) (g : Y ⟶ W) (h : W ⟶ Z)
  : coprod.desc f g ≫ h = coprod.desc (f ≫ h) (g ≫ h)
  := by
  convert coprod.uniq (BinaryCofan.mk (f ≫ h) (g ≫ h)) (coprod.desc f g ≫ h) _
  simp
  intro ⟨j⟩; cases j <;> simp

@[simp, reassoc (attr := simp)]
theorem IsBinaryCoproduct.desc_inl_inr_comp {X Y P : C} {inl : X ⟶ P} {inr : Y ⟶ P}
  (coprod : IsBinaryCoproduct inl inr) (f : P ⟶ Z)
  : coprod.desc (inl ≫ f) (inr ≫ f) = f := by simp [<-desc_comp]

theorem IsBinaryCoproduct.eq_cases
  {X Y P : C} {inl : X ⟶ P} {inr : Y ⟶ P}
  (coprod : IsBinaryCoproduct inl inr)
  (f g : P ⟶ Z)
  (hl : inl ≫ f = inl ≫ g)
  (hr : inr ≫ f = inr ≫ g)
  : f = g
  := by rw [<-coprod.desc_inl_inr_comp f, <-coprod.desc_inl_inr_comp g, hl, hr]

def IsBinaryCoproduct.map
  {X Y P : C} {inl : X ⟶ P} {inr : Y ⟶ P}
  {X' Y' P' : C}
  (coprod : IsBinaryCoproduct inl inr)
  (inl' : X' ⟶ P') (inr' : Y' ⟶ P')
  (f : X ⟶ X') (g : Y ⟶ Y') : P ⟶ P'
  := IsColimit.map coprod (BinaryCofan.mk inl' inr') (mapPair f g)

theorem IsBinaryCoproduct.map_eq_desc
  {X Y P : C} {inl : X ⟶ P} {inr : Y ⟶ P}
  {X' Y' P' : C}
  (coprod : IsBinaryCoproduct inl inr)
  (inl' : X' ⟶ P') (inr' : Y' ⟶ P')
  (f : X ⟶ X') (g : Y ⟶ Y')
  : coprod.map inl' inr' f g = coprod.desc (f ≫ inl') (g ≫ inr') := by
  simp only [
    map, IsColimit.map, desc, Cocones.precompose, BinaryCofan.mk, mapPair, CategoryStruct.comp,
    NatTrans.vcomp
  ]
  congr
  funext x; cases x with | mk x => cases x <;> rfl

@[simp, reassoc (attr := simp)]
theorem IsBinaryCoproduct.inl_map
  {X Y P : C} {inl : X ⟶ P} {inr : Y ⟶ P}
  {X' Y' P' : C}
  (coprod : IsBinaryCoproduct inl inr)
  (inl' : X' ⟶ P') (inr' : Y' ⟶ P')
  (f : X ⟶ X') (g : Y ⟶ Y')
  : inl ≫ coprod.map inl' inr' f g = f ≫ inl'
  := by rw [IsBinaryCoproduct.map_eq_desc]; simp

@[simp, reassoc (attr := simp)]
theorem IsBinaryCoproduct.inr_map
  {X Y P : C} {inl : X ⟶ P} {inr : Y ⟶ P}
  {X' Y' P' : C}
  (coprod : IsBinaryCoproduct inl inr)
  (inl' : X' ⟶ P') (inr' : Y' ⟶ P')
  (f : X ⟶ X') (g : Y ⟶ Y')
  : inr ≫ coprod.map inl' inr' f g = g ≫ inr'
  := by rw [IsBinaryCoproduct.map_eq_desc]; simp

abbrev IsBinaryCoproduct.codiag {X : C} (inl : X ⟶ P) (inr : X ⟶ P)
  (coprod : IsBinaryCoproduct inl inr)
  := coprod.desc (𝟙 X) (𝟙 X)

def IsBinaryCoproduct.associator
  {X Y PXY : C} {inl_xy : X ⟶ PXY} {inr_xy : Y ⟶ PXY}
  {Z PYZ : C} {inl_yz : Y ⟶ PYZ} {inr_yz : Z ⟶ PYZ}
  {PXY_Z : C} {inl_xy_z : PXY ⟶ PXY_Z} {inr_xy_z : Z ⟶ PXY_Z}
  {PX_YZ : C} {inl_x_yz : X ⟶ PX_YZ} {inr_x_yz : PYZ ⟶ PX_YZ}
  (coprod_xy : IsBinaryCoproduct inl_xy inr_xy)
  (coprod_yz : IsBinaryCoproduct inl_yz inr_yz)
  (coprod_xy_z : IsBinaryCoproduct inl_xy_z inr_xy_z)
  (coprod_x_yz : IsBinaryCoproduct inl_x_yz inr_x_yz)
  : PXY_Z ≅ PX_YZ
  := ⟨
    coprod_xy_z.desc (coprod_xy.desc inl_x_yz (inl_yz ≫ inr_x_yz)) (inr_yz ≫ inr_x_yz),
    coprod_x_yz.desc (inl_xy ≫ inl_xy_z) (coprod_yz.desc (inr_xy ≫ inl_xy_z) inr_xy_z),
    by simp [desc_comp],
    by simp [desc_comp]
  ⟩

def IsBinaryCoproduct.leftUnitor
  {I X P : C} {inl : I ⟶ P} {inr : X ⟶ P}
  (initial : IsInitial I)
  (coprod : IsBinaryCoproduct inl inr)
  : P ≅ X
  := ⟨
    coprod.desc (initial.to X) (𝟙 X),
    inr,
    by apply coprod.eq_cases <;> simp; apply initial.hom_ext,
    by simp
  ⟩

def IsBinaryCoproduct.rightUnitor
  {X I P : C} {inl : X ⟶ P} {inr : I ⟶ P}
  (coprod : IsBinaryCoproduct inl inr)
  (initial : IsInitial I)
  : P ≅ X
  := ⟨
    coprod.desc (𝟙 X) (initial.to X),
    inl,
    by apply coprod.eq_cases <;> simp; apply initial.hom_ext,
    by simp
  ⟩

def IsBinaryCoproduct.braiding
  {X Y P : C}
  {inl : X ⟶ P} {inr : Y ⟶ P}
  {inl' : Y ⟶ Q} {inr' : X ⟶ Q}
  (coprod : IsBinaryCoproduct inl inr)
  (coprod' : IsBinaryCoproduct inl' inr')
  : P ≅ Q
  := ⟨
    coprod.desc inr' inl',
    coprod'.desc inr inl,
    by simp [desc_comp],
    by simp [desc_comp]
  ⟩

class ChosenCoproducts (C : Type _) [Category C] extends AddMonoidalCategory C where
  inl : ∀ {X Y : C}, X ⟶ X +ₒ Y
  inr : ∀ {X Y : C}, Y ⟶ X +ₒ Y
  coprod : ∀{X Y : C}, IsBinaryCoproduct (X := X) (Y := Y) inl inr
  initial : IsInitial (𝟘_ C)
  assoc_canonical {X Y Z : C} : α⁺ X Y Z = coprod.associator coprod coprod coprod
  leftUnitor_canonical {X : C} : λ⁺ X = coprod.leftUnitor initial
  rightUnitor_canonical {X : C} : ρ⁺ X = coprod.rightUnitor initial
  braiding_canonical {X Y : C} : σ⁺ X Y = coprod.braiding coprod

-- def monoidalOfBinaryCoproducts
--   (addObj : C → C → C)
--   (initialObj : C)
--   (inl : ∀ {X Y : C}, X ⟶ addObj X Y)
--   (inr : ∀ {X Y : C}, Y ⟶ addObj X Y)
--   (coprod : ∀{X Y : C}, IsBinaryCoproduct (X := X) (Y := Y) inl inr)
--   (initial : IsInitial initialObj)
--   : MonoidalCategory C where
--   tensorObj := addObj
--   tensorUnit := initialObj
--   tensorHom := coprod.map inl inr
--   whiskerLeft Z X Y f := coprod.map inl inr (𝟙 Z) f
--   whiskerRight f Z := coprod.map inl inr f (𝟙 Z)
--   associator _ _ _ := coprod.associator coprod coprod coprod
--   leftUnitor _ := coprod.leftUnitor initial
--   rightUnitor _ := coprod.rightUnitor initial
--   tensorHom_def _ _ := sorry
--   tensor_id := sorry
--   tensor_comp := sorry
--   whiskerLeft_id := sorry
--   id_whiskerRight := sorry
--   associator_naturality := sorry
--   leftUnitor_naturality := sorry
--   rightUnitor_naturality := sorry
--   pentagon := sorry
--   triangle := sorry

-- def symmetricOfBinaryCoproducts
--   (addObj : C → C → C)
--   (initialObj : C)
--   (inl : ∀ {X Y : C}, X ⟶ addObj X Y)
--   (inr : ∀ {X Y : C}, Y ⟶ addObj X Y)
--   (coprod : ∀{X Y : C}, IsBinaryCoproduct (X := X) (Y := Y) inl inr)
--   (initial : IsInitial initialObj) :
--     let _ := monoidalOfBinaryCoproducts addObj initialObj inl inr coprod initial;
--     SymmetricCategory C
--   := let _ := monoidalOfBinaryCoproducts addObj initialObj inl inr coprod initial; {
--     braiding := λ _ _ => coprod.braiding coprod
--     braiding_naturality_right := sorry
--     braiding_naturality_left := sorry
--     hexagon_forward := sorry
--     hexagon_reverse := sorry
--     symmetry := sorry
--   }

-- def ChosenCoproducts.mk'
--   (addObj : C → C → C)
--   (initialObj : C)
--   (inl : ∀ {X Y : C}, X ⟶ addObj X Y)
--   (inr : ∀ {X Y : C}, Y ⟶ addObj X Y)
--   (coprod : ∀{X Y : C}, IsBinaryCoproduct (X := X) (Y := Y) inl inr)
--   (initial : IsInitial initialObj) : ChosenCoproducts C where
--   addMonoidal := monoidalOfBinaryCoproducts addObj initialObj inl inr coprod initial
--   addSymmetric := symmetricOfBinaryCoproducts addObj initialObj inl inr coprod initial
--   inl := inl
--   inr := inr
--   coprod := coprod
--   initial := initial
