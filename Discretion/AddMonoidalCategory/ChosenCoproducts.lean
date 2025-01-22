import Discretion.AddMonoidalCategory.Basic

namespace CategoryTheory

open MonoidalCategory

open Monoidal

open Limits

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

theorem IsBinaryCoproduct.map_comp
  {X Y P : C} {inl : X ⟶ P} {inr : Y ⟶ P}
  (coprod : IsBinaryCoproduct inl inr)
  {X' Y' P' : C} {inl' : X' ⟶ P'} {inr' : Y' ⟶ P'}
  (coprod' : IsBinaryCoproduct inl' inr')
  {X'' Y'' P'' : C}
  (inl'' : X'' ⟶ P'') (inr'' : Y'' ⟶ P'')
  (f : X ⟶ X') (g : Y ⟶ Y')
  (f' : X' ⟶ X'') (g' : Y' ⟶ Y'')
  : coprod.map inl' inr' f g ≫ coprod'.map inl'' inr'' f' g'
  = coprod.map inl'' inr'' (f ≫ f') (g ≫ g')
  := by simp [map_eq_desc, desc_comp]

theorem IsBinaryCoproduct.map_comp_desc
  {X Y P : C} {inl : X ⟶ P} {inr : Y ⟶ P}
  (coprod : IsBinaryCoproduct inl inr)
  {X' Y' P' : C} {inl' : X' ⟶ P'} {inr' : Y' ⟶ P'}
  (coprod' : IsBinaryCoproduct inl' inr')
  (f : X ⟶ X') (g : Y ⟶ Y')
  (f' : X' ⟶ Z) (g' : Y' ⟶ Z)
  : coprod.map inl' inr' f g ≫ coprod'.desc f' g' = coprod.desc (f ≫ f') (g ≫ g')
  := by simp [map_eq_desc, desc_comp]

@[simp]
theorem IsBinaryCoproduct.map_id'
  {X Y P : C} {inl : X ⟶ P} {inr : Y ⟶ P}
  (coprod : IsBinaryCoproduct inl inr)
  (inl' : X ⟶ P') (inr' : Y ⟶ P')
  : coprod.map inl' inr' (𝟙 X) (𝟙 Y) = coprod.desc inl' inr'
  := by simp [map_eq_desc]

theorem IsBinaryCoproduct.map_id
  {X Y P : C} {inl : X ⟶ P} {inr : Y ⟶ P}
  (coprod : IsBinaryCoproduct inl inr)
  : coprod.map inl inr (𝟙 X) (𝟙 Y) = 𝟙 P
  := by simp

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

theorem IsBinaryCoproduct.associator_hom_def
  {X Y PXY : C} {inl_xy : X ⟶ PXY} {inr_xy : Y ⟶ PXY}
  {Z PYZ : C} {inl_yz : Y ⟶ PYZ} {inr_yz : Z ⟶ PYZ}
  {PXY_Z : C} {inl_xy_z : PXY ⟶ PXY_Z} {inr_xy_z : Z ⟶ PXY_Z}
  {PX_YZ : C} {inl_x_yz : X ⟶ PX_YZ} {inr_x_yz : PYZ ⟶ PX_YZ}
  (coprod_xy : IsBinaryCoproduct inl_xy inr_xy)
  (coprod_yz : IsBinaryCoproduct inl_yz inr_yz)
  (coprod_xy_z : IsBinaryCoproduct inl_xy_z inr_xy_z)
  (coprod_x_yz : IsBinaryCoproduct inl_x_yz inr_x_yz)
  : (coprod_xy.associator coprod_yz coprod_xy_z coprod_x_yz).hom
  = coprod_xy_z.desc (coprod_xy.desc inl_x_yz (inl_yz ≫ inr_x_yz)) (inr_yz ≫ inr_x_yz)
  := rfl

theorem IsBinaryCoproduct.associator_inv_def
  {X Y PXY : C} {inl_xy : X ⟶ PXY} {inr_xy : Y ⟶ PXY}
  {Z PYZ : C} {inl_yz : Y ⟶ PYZ} {inr_yz : Z ⟶ PYZ}
  {PXY_Z : C} {inl_xy_z : PXY ⟶ PXY_Z} {inr_xy_z : Z ⟶ PXY_Z}
  {PX_YZ : C} {inl_x_yz : X ⟶ PX_YZ} {inr_x_yz : PYZ ⟶ PX_YZ}
  (coprod_xy : IsBinaryCoproduct inl_xy inr_xy)
  (coprod_yz : IsBinaryCoproduct inl_yz inr_yz)
  (coprod_xy_z : IsBinaryCoproduct inl_xy_z inr_xy_z)
  (coprod_x_yz : IsBinaryCoproduct inl_x_yz inr_x_yz)
  : (coprod_xy.associator coprod_yz coprod_xy_z coprod_x_yz).inv
  = coprod_x_yz.desc (inl_xy ≫ inl_xy_z) (coprod_yz.desc (inr_xy ≫ inl_xy_z) inr_xy_z)
  := rfl

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

theorem IsBinaryCoproduct.leftUnitor_hom_def
  {I X P : C} {inl : I ⟶ P} {inr : X ⟶ P}
  (initial : IsInitial I)
  (coprod : IsBinaryCoproduct inl inr)
  : (coprod.leftUnitor initial).hom = coprod.desc (initial.to X) (𝟙 X)
  := rfl

theorem IsBinaryCoproduct.leftUnitor_inv_def
  {I X P : C} {inl : I ⟶ P} {inr : X ⟶ P}
  (initial : IsInitial I)
  (coprod : IsBinaryCoproduct inl inr)
  : (coprod.leftUnitor initial).inv = inr
  := rfl

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

theorem IsBinaryCoproduct.rightUnitor_hom_def
  {X I P : C} {inl : X ⟶ P} {inr : I ⟶ P}
  (coprod : IsBinaryCoproduct inl inr)
  (initial : IsInitial I)
  : (coprod.rightUnitor initial).hom = coprod.desc (𝟙 X) (initial.to X)
  := rfl

theorem IsBinaryCoproduct.rightUnitor_inv_def
  {X I P : C} {inl : X ⟶ P} {inr : I ⟶ P}
  (coprod : IsBinaryCoproduct inl inr)
  (initial : IsInitial I)
  : (coprod.rightUnitor initial).inv = inl
  := rfl

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

theorem IsBinaryCoproduct.braiding_hom_def
  {X Y P : C}
  {inl : X ⟶ P} {inr : Y ⟶ P}
  {inl' : Y ⟶ Q} {inr' : X ⟶ Q}
  (coprod : IsBinaryCoproduct inl inr)
  (coprod' : IsBinaryCoproduct inl' inr')
  : (coprod.braiding coprod').hom = coprod.desc inr' inl'
  := rfl

theorem IsBinaryCoproduct.braiding_inv_def
  {X Y P : C}
  {inl : X ⟶ P} {inr : Y ⟶ P}
  {inl' : Y ⟶ Q} {inr' : X ⟶ Q}
  (coprod : IsBinaryCoproduct inl inr)
  (coprod' : IsBinaryCoproduct inl' inr')
  : (coprod.braiding coprod').inv = coprod'.desc inr inl
  := rfl

class ChosenCoproducts (C : Type _) [Category C] extends AddMonoidalCategory C where
  inl : ∀ {X Y : C}, X ⟶ X +ₒ Y
  inr : ∀ {X Y : C}, Y ⟶ X +ₒ Y
  coprod : ∀{X Y : C}, IsBinaryCoproduct (X := X) (Y := Y) inl inr
  initial : IsInitial (𝟘_ C)
  assoc_canonical {X Y Z : C} : α⁺ X Y Z = coprod.associator coprod coprod coprod
  leftUnitor_canonical {X : C} : λ⁺ X = coprod.leftUnitor initial
  rightUnitor_canonical {X : C} : ρ⁺ X = coprod.rightUnitor initial
  braiding_canonical {X Y : C} : σ⁺ X Y = coprod.braiding coprod

def monoidalOfBinaryCoproducts
  (addObj : C → C → C)
  (initialObj : C)
  (inl : ∀ {X Y : C}, X ⟶ addObj X Y)
  (inr : ∀ {X Y : C}, Y ⟶ addObj X Y)
  (coprod : ∀{X Y : C}, IsBinaryCoproduct (X := X) (Y := Y) inl inr)
  (initial : IsInitial initialObj)
  : MonoidalCategory C where
  tensorObj := addObj
  tensorUnit := initialObj
  tensorHom := coprod.map inl inr
  whiskerLeft Z X Y f := coprod.map inl inr (𝟙 Z) f
  whiskerRight f Z := coprod.map inl inr f (𝟙 Z)
  associator _ _ _ := coprod.associator coprod coprod coprod
  leftUnitor _ := coprod.leftUnitor initial
  rightUnitor _ := coprod.rightUnitor initial
  tensorHom_def _ _ := by simp [IsBinaryCoproduct.map_comp]
  tensor_id _ _ := by simp
  tensor_comp _ _ _ _ := by simp [IsBinaryCoproduct.map_comp]
  whiskerLeft_id _ _ := by simp
  id_whiskerRight _ _ := by simp
  associator_naturality _ _ _ := by simp [
    IsBinaryCoproduct.associator_hom_def,
    IsBinaryCoproduct.map_eq_desc,
    IsBinaryCoproduct.desc_comp]
  leftUnitor_naturality := by simp [
    IsBinaryCoproduct.leftUnitor_hom_def,
    IsBinaryCoproduct.map_eq_desc,
    IsBinaryCoproduct.desc_comp]
  rightUnitor_naturality := by simp [
    IsBinaryCoproduct.rightUnitor_hom_def,
    IsBinaryCoproduct.map_eq_desc,
    IsBinaryCoproduct.desc_comp]
  pentagon := by simp [
    IsBinaryCoproduct.associator_hom_def,
    IsBinaryCoproduct.map_eq_desc,
    IsBinaryCoproduct.desc_comp]
  triangle := by simp [
    IsBinaryCoproduct.associator_hom_def,
    IsBinaryCoproduct.leftUnitor_hom_def,
    IsBinaryCoproduct.rightUnitor_hom_def,
    IsBinaryCoproduct.map_eq_desc,
    IsBinaryCoproduct.desc_comp]

def symmetricOfBinaryCoproducts
  (addObj : C → C → C)
  (initialObj : C)
  (inl : ∀ {X Y : C}, X ⟶ addObj X Y)
  (inr : ∀ {X Y : C}, Y ⟶ addObj X Y)
  (coprod : ∀{X Y : C}, IsBinaryCoproduct (X := X) (Y := Y) inl inr)
  (initial : IsInitial initialObj) :
    let _ := monoidalOfBinaryCoproducts addObj initialObj inl inr coprod initial;
    SymmetricCategory C
  := let _ := monoidalOfBinaryCoproducts addObj initialObj inl inr coprod initial; {
    braiding := λ _ _ => coprod.braiding coprod
    braiding_naturality_right := by simp [
      monoidalOfBinaryCoproducts,
      IsBinaryCoproduct.braiding_hom_def,
      IsBinaryCoproduct.map_eq_desc,
      IsBinaryCoproduct.desc_comp]
    braiding_naturality_left := by simp [
      monoidalOfBinaryCoproducts,
      IsBinaryCoproduct.braiding_hom_def,
      IsBinaryCoproduct.map_eq_desc,
      IsBinaryCoproduct.desc_comp]
    hexagon_forward := by simp [
      monoidalOfBinaryCoproducts,
      IsBinaryCoproduct.associator_hom_def,
      IsBinaryCoproduct.braiding_hom_def,
      IsBinaryCoproduct.map_eq_desc,
      IsBinaryCoproduct.desc_comp]
    hexagon_reverse := by simp [
      monoidalOfBinaryCoproducts,
      IsBinaryCoproduct.associator_inv_def,
      IsBinaryCoproduct.braiding_hom_def,
      IsBinaryCoproduct.map_eq_desc,
      IsBinaryCoproduct.desc_comp]
    symmetry := by simp [
      monoidalOfBinaryCoproducts,
      IsBinaryCoproduct.braiding_hom_def,
      IsBinaryCoproduct.map_eq_desc,
      IsBinaryCoproduct.desc_comp]
  }

def ChosenCoproducts.mk'
  (addObj : C → C → C)
  (initialObj : C)
  (inl : ∀ {X Y : C}, X ⟶ addObj X Y)
  (inr : ∀ {X Y : C}, Y ⟶ addObj X Y)
  (coprod : ∀{X Y : C}, IsBinaryCoproduct (X := X) (Y := Y) inl inr)
  (initial : IsInitial initialObj) : ChosenCoproducts C where
  addMonoidal := monoidalOfBinaryCoproducts addObj initialObj inl inr coprod initial
  addSymmetric := symmetricOfBinaryCoproducts addObj initialObj inl inr coprod initial
  inl := inl
  inr := inr
  coprod := coprod
  initial := initial
  assoc_canonical := rfl
  leftUnitor_canonical := rfl
  rightUnitor_canonical := rfl
  braiding_canonical := rfl

-- TODO: now define things for chosen coproducts!
