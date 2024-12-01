import Mathlib.CategoryTheory.Monoidal.Category
import Discretion.Utils.Category

namespace CategoryTheory

open MonoidalCategory

namespace Monoidal

variable {C : Type _} [Category C] [MonoidalCategoryStruct C]

abbrev ltimes {X Y X' Y' : C} (f : X ⟶ Y) (g : X' ⟶ Y') : X ⊗ X' ⟶ Y ⊗ Y' := (f ▷ X') ≫ (Y ◁ g)

abbrev rtimes {X Y X' Y' : C} (f : X ⟶ Y) (g : X' ⟶ Y') : X ⊗ X' ⟶ Y ⊗ Y' := (X ◁ g) ≫ (f ▷ Y')

scoped infixr:81 " ⋉ " => ltimes

scoped infixr:81 " ⋊ " => rtimes

class Central {X Y : C} (f : X ⟶ Y) : Prop where
  left_sliding : ∀{X' Y' : C}, ∀g : X' ⟶ Y', f ⋉ g = f ⋊ g
  right_sliding : ∀{X' Y' : C}, ∀g : X' ⟶ Y', g ⋉ f = g ⋊ f

@[reassoc]
theorem left_sliding {X Y X' Y' : C}
  (f : X ⟶ Y) (g : X' ⟶ Y') [hf : Central f] : f ⋉ g = f ⋊ g := Central.left_sliding g

@[reassoc]
theorem right_sliding {X Y X' Y' : C}
  (f : X ⟶ Y) (g : X' ⟶ Y') [hg : Central g] : f ⋉ g = f ⋊ g := Central.right_sliding f

@[reassoc]
theorem left_exchange {X Y X' Y' : C}
  (f : X ⟶ Y) (g : X' ⟶ Y') [hf : Central f] : (f ▷ X') ≫ (Y ◁ g) = (X ◁ g) ≫ (f ▷ Y')
  := left_sliding f g

@[reassoc]
theorem right_exchange {X Y X' Y' : C}
  (f : X ⟶ Y) (g : X' ⟶ Y') [hg : Central g] : (f ▷ X') ≫ (Y ◁ g) = (X ◁ g) ≫ (f ▷ Y')
  := right_sliding f g

-- TODO: in fact, everything is central in a _binoidal_ category with sliding; can use this
-- to make things nicer...

end Monoidal

class IsBinoidal (C: Type u) [Category C] [MonoidalCategoryStruct C] : Prop where
  tensorHom_def {X₁ Y₁ X₂ Y₂ : C} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) :
    f ⊗ g = (f ▷ X₂) ≫ (Y₁ ◁ g) := by
      aesop_cat
  whiskerLeft_id : ∀ (X Y : C), X ◁ 𝟙 Y = 𝟙 (X ⊗ Y) := by
    aesop_cat
  id_whiskerRight : ∀ (X Y : C), 𝟙 X ▷ Y = 𝟙 (X ⊗ Y) := by
    aesop_cat
  whiskerLeft_comp : ∀ {X Y Z W : C} (f : X ⟶ Y) (g : Y ⟶ Z), W ◁ (f ≫ g) = (W ◁ f) ≫ (W ◁ g)
    := by aesop_cat
  whiskerRight_comp : ∀ {X Y Z W : C} (f : X ⟶ Y) (g : Y ⟶ Z), (f ≫ g) ▷ W = (f ▷ W) ≫ (g ▷ W)
    := by aesop_cat

class IsPremonoidal (C: Type u) [Category C] [MonoidalCategoryStruct C]
  extends IsBinoidal C : Prop where
  associator_central : ∀ {X Y Z : C}, Monoidal.Central (α_ X Y Z).hom := by aesop_cat
  leftUnitor_central : ∀ {X : C}, Monoidal.Central (λ_ X).hom := by aesop_cat
  rightUnitor_central : ∀ {X : C}, Monoidal.Central (ρ_ X).hom := by aesop_cat
  /-- Naturality of the associator isomorphism: `(f₁ ⊗ f₂) ⊗ f₃ ≃ f₁ ⊗ (f₂ ⊗ f₃)` -/
  associator_naturality :
    ∀ {X₁ X₂ X₃ Y₁ Y₂ Y₃ : C} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (f₃ : X₃ ⟶ Y₃),
      ((f₁ ⊗ f₂) ⊗ f₃) ≫ (α_ Y₁ Y₂ Y₃).hom = (α_ X₁ X₂ X₃).hom ≫ (f₁ ⊗ (f₂ ⊗ f₃)) := by
    aesop_cat
  /--
  Naturality of the left unitor, commutativity of `𝟙_ C ⊗ X ⟶ 𝟙_ C ⊗ Y ⟶ Y` and `𝟙_ C ⊗ X ⟶ X ⟶ Y`
  -/
  leftUnitor_naturality :
    ∀ {X Y : C} (f : X ⟶ Y), 𝟙_ _ ◁ f ≫ (λ_ Y).hom = (λ_ X).hom ≫ f := by
    aesop_cat
  /--
  Naturality of the right unitor: commutativity of `X ⊗ 𝟙_ C ⟶ Y ⊗ 𝟙_ C ⟶ Y` and `X ⊗ 𝟙_ C ⟶ X ⟶ Y`
  -/
  rightUnitor_naturality :
    ∀ {X Y : C} (f : X ⟶ Y), f ▷ 𝟙_ _ ≫ (ρ_ Y).hom = (ρ_ X).hom ≫ f := by
    aesop_cat
  /--
  The pentagon identity relating the isomorphism between `X ⊗ (Y ⊗ (Z ⊗ W))` and `((X ⊗ Y) ⊗ Z) ⊗ W`
  -/
  pentagon :
    ∀ W X Y Z : C,
      (α_ W X Y).hom ▷ Z ≫ (α_ W (X ⊗ Y) Z).hom ≫ W ◁ (α_ X Y Z).hom =
        (α_ (W ⊗ X) Y Z).hom ≫ (α_ W X (Y ⊗ Z)).hom := by
    aesop_cat
  /--
  The identity relating the isomorphisms between `X ⊗ (𝟙_ C ⊗ Y)`, `(X ⊗ 𝟙_ C) ⊗ Y` and `X ⊗ Y`
  -/
  triangle :
    ∀ X Y : C, (α_ X (𝟙_ _) Y).hom ≫ X ◁ (λ_ Y).hom = (ρ_ X).hom ▷ Y := by
    aesop_cat

class IsMonoidal (C : Type u) [Category C] [MonoidalCategoryStruct C] extends
  IsPremonoidal C : Prop where
  tensor_comp : ∀ {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : C}
    (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (g₁ : Y₁ ⟶ Z₁) (g₂ : Y₂ ⟶ Z₂),
    (f₁ ≫ g₁) ⊗ (f₂ ≫ g₂) = (f₁ ⊗ f₂) ≫ (g₁ ⊗ g₂) := by aesop_cat
-- TODO: ideally, MonoidalCategory extends PremonoidalCategory.
-- TODO: also, MonoidalCategoryStruct would best extend BinoidalCategory, but that's just me...

namespace Monoidal

variable {C : Type _} [Category C]

def instMonoidalCategory [MonoidalCategory C] : IsMonoidal C where
  tensorHom_def := MonoidalCategory.tensorHom_def
  associator_central := ⟨λg => by simp [ltimes, rtimes], λg => by simp [ltimes, rtimes]⟩
  leftUnitor_central := ⟨λg => by simp [ltimes, rtimes], λg => by simp [ltimes, rtimes]⟩
  rightUnitor_central := ⟨λg => by simp [ltimes, rtimes], λg => by simp [ltimes, rtimes]⟩

variable [MonoidalCategoryStruct C]

theorem whiskerRight_comp_rtimes {X Y Z X' Y' : C} (f : X ⟶ Y) (g : Y ⟶ Z) (h : X' ⟶ Y') :
  f ▷ X' ≫ g ⋊ h = f ⋉ h ≫ g ▷ Y' := by simp

theorem whiskerLeft_comp_ltimes {X Y Z X' Y' : C} (f : X ⟶ Y) (g : X' ⟶ Y') (h : Y ⟶ Z) :
  X' ◁ f ≫ g ⋉ h = g ⋊ f ≫ Y' ◁ h := by simp

class IsStrict (C : Type u) [Category C] [MonoidalCategoryStruct C] : Prop where
  tensor_assoc : ∀ {X Y Z : C}, (X ⊗ Y) ⊗ Z = X ⊗ (Y ⊗ Z)
  unit_tensor : ∀ {X : C}, 𝟙_ C ⊗ X = X
  tensor_unit : ∀ {X : C}, X ⊗ 𝟙_ C = X
  associator_eq_id : ∀ {X Y Z : C}, (α_ X Y Z).hom = eq_hom tensor_assoc
  leftUnitor_eq_id : ∀ {X : C}, (λ_ X).hom = eq_hom unit_tensor
  rightUnitor_eq_id : ∀ {X : C}, (ρ_ X).hom = eq_hom tensor_unit

section IsBinoidal

variable [IsBinoidal C]

@[simp]
theorem whiskerLeft_id {X Y : C} : X ◁ 𝟙 Y = 𝟙 (X ⊗ Y)
  := IsBinoidal.whiskerLeft_id _ _

@[simp]
theorem id_whiskerRight {X Y : C} : 𝟙 X ▷ Y = 𝟙 (X ⊗ Y)
  := IsBinoidal.id_whiskerRight _ _

@[simp]
theorem whiskerLeft_eq_hom {X Y Z : C} (p : Y = Z) : X ◁ (eq_hom p) = eq_hom (by rw [p])
  := by cases p; simp

@[simp]
theorem eq_hom_whiskerRight {X Y Z : C} (p : X = Y) : eq_hom p ▷ Z = eq_hom (by rw [p])
  := by cases p; simp

@[reassoc, simp]
theorem whiskerLeft_comp {X Y Z W : C} (f : X ⟶ Y) (g : Y ⟶ Z)
  : W ◁ (f ≫ g) = (W ◁ f) ≫ (W ◁ g) := IsBinoidal.whiskerLeft_comp f g

@[reassoc, simp]
theorem whiskerRight_comp {X Y Z W : C} (f : X ⟶ Y) (g : Y ⟶ Z)
  : (f ≫ g) ▷ W = (f ▷ W) ≫ (g ▷ W) :=  IsBinoidal.whiskerRight_comp f g

@[reassoc, simp]
theorem whiskerRight_comp_inv {X Y Z : C} (f : X ⟶ Y) [IsIso f]
  : f ▷ Z ≫ inv f ▷ Z = 𝟙 (X ⊗ Z) := by simp [<-whiskerRight_comp]

@[reassoc, simp]
theorem whiskerRight_inv_comp {X Y Z : C} (f : X ⟶ Y) [IsIso f]
  : inv f ▷ Z ≫ f ▷ Z = 𝟙 (Y ⊗ Z) := by simp [<-whiskerRight_comp]

@[reassoc, simp]
theorem whiskerLeft_comp_inv {X Y Z : C} (f : X ⟶ Y) [IsIso f]
  : Z ◁ f ≫ Z ◁ inv f = 𝟙 (Z ⊗ X) := by simp [<-whiskerLeft_comp]

@[reassoc, simp]
theorem whiskerLeft_inv_comp {X Y Z : C} (f : X ⟶ Y) [IsIso f]
  : Z ◁ inv f ≫ Z ◁ f = 𝟙 (Z ⊗ Y) := by simp [<-whiskerLeft_comp]

instance whiskerRight_isIso {X Y Z : C} (f : X ⟶ Y) [IsIso f] : IsIso (f ▷ Z) where
  out := ⟨inv f ▷ Z, whiskerRight_comp_inv f, whiskerRight_inv_comp f⟩

instance whiskerLeft_isIso {X Y Z : C} (f : X ⟶ Y) [IsIso f] : IsIso (Z ◁ f) where
  out := ⟨Z ◁ inv f, whiskerLeft_comp_inv f, whiskerLeft_inv_comp f⟩

@[simp]
theorem inv_whiskerRight {X Y Z : C} (f : X ⟶ Y) [IsIso f] : inv (f ▷ Z) = inv f ▷ Z
  := by aesop_cat

@[simp]
theorem inv_whiskerLeft {X Y Z : C} (f : X ⟶ Y) [IsIso f] : inv (Z ◁ f) = Z ◁ inv f
  := by aesop_cat

theorem inv_ltimes {X Y X' Y' : C} (f : X ⟶ Y) (g : X' ⟶ Y') [IsIso f] [IsIso g] :
  inv (f ⋉ g) = inv f ⋊ inv g := by simp

theorem inv_rtimes {X Y X' Y' : C} (f : X ⟶ Y) (g : X' ⟶ Y') [IsIso f] [IsIso g] :
  inv (f ⋊ g) = inv f ⋉ inv g := by simp

-- TODO: tensorHom is iso, ltimes is iso, rtimes is iso

theorem tensorHom_def {X₁ Y₁ X₂ Y₂ : C} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) :
  f ⊗ g = (f ▷ X₂) ≫ (Y₁ ◁ g) := IsBinoidal.tensorHom_def f g

theorem tensor_eq_ltimes {X₁ Y₁ X₂ Y₂ : C} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) :
  f ⊗ g = f ⋉ g := tensorHom_def f g

theorem tensor_eq_rtimes_left {X₁ Y₁ X₂ Y₂ : C} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) [Central f] :
  f ⊗ g = f ⋊ g := by rw [tensor_eq_ltimes, left_sliding]

theorem tensor_eq_rtimes_right {X₁ Y₁ X₂ Y₂ : C} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) [Central g] :
  f ⊗ g = f ⋉ g := by rw [tensor_eq_ltimes, right_sliding]

instance IsIso.instTensor' {X₁ Y₁ X₂ Y₂ : C} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) [IsIso f] [IsIso g] :
  IsIso (f ⊗ g) := by rw [tensor_eq_ltimes]; infer_instance

@[simp]
theorem inv_tensor_left {X₁ Y₁ X₂ Y₂ : C} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂)
  [IsIso f] [IsIso g] [Central f] :
  inv (f ⊗ g) = inv f ⊗ inv g := by simp [tensorHom_def, left_sliding]

@[simp]
theorem inv_tensor_right {X₁ Y₁ X₂ Y₂ : C} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂)
  [IsIso f] [IsIso g] [Central g] :
  inv (f ⊗ g) = inv f ⊗ inv g := by simp [tensorHom_def, right_sliding]

@[simp]
theorem tensor_id {X Y : C} : 𝟙 X ⊗ 𝟙 Y = 𝟙 (X ⊗ Y) := by simp [tensorHom_def]

@[simp]
theorem tensorHom_eq_hom {X₁ Y₁ X₂ Y₂ : C} (p : X₁ = Y₁) (q : X₂ = Y₂) :
  eq_hom p ⊗ eq_hom q = eq_hom (by rw [p, q]) := by cases p; cases q; simp

theorem id_tensorHom {X Y Z : C} (f : X ⟶ Y) : 𝟙 Z ⊗ f = Z ◁ f := by simp [tensorHom_def]

theorem tensorHom_id {X Y Z : C} (f : X ⟶ Y) : f ⊗ 𝟙 Z = f ▷ Z := by simp [tensorHom_def]

@[simp]
theorem ltimes_id {X Y : C} : 𝟙 X ⋉ 𝟙 Y = 𝟙 (X ⊗ Y) := by simp [ltimes]

@[simp]
theorem rtimes_id {X Y : C} : 𝟙 X ⋊ 𝟙 Y = 𝟙 (X ⊗ Y) := by simp [rtimes]

theorem comp_ltimes {X Y Z X' Y' : C} (f : X ⟶ Y) (g : Y ⟶ Z) (h : X' ⟶ Y') :
  (f ≫ g) ⋉ h = f ▷ X' ≫ g ⋉ h := by simp [ltimes]

theorem ltimes_comp {X Y X' Y' Z' : C} (f : X ⟶ Y) (g : X' ⟶ Y') (h : Y' ⟶ Z') :
  f ⋉ (g ≫ h) = f ⋉ g ≫ Y ◁ h := by simp [ltimes]

theorem comp_rtimes {X Y Z X' Y' : C} (f : X ⟶ Y) (g : Y ⟶ Z) (h : X' ⟶ Y') :
  (f ≫ g) ⋊ h = f ⋊ h ≫ (g ▷ Y') := by simp [rtimes]

theorem rtimes_comp {X Y X' Y' Z' : C} (f : X ⟶ Y) (g : X' ⟶ Y') (h : Y' ⟶ Z') :
  f ⋊ (g ≫ h) = X ◁ g ≫ f ⋊ h := by simp [rtimes]

@[simp]
instance Central.id {X : C} : Central (𝟙 X) where
  left_sliding := by simp [ltimes, rtimes]
  right_sliding := by simp [ltimes, rtimes]

@[simp]
instance Central.eq_hom {X Y : C} (p : X = Y) : Central (eq_hom p) := by cases p; simp

instance Central.comp {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z}
  [hf : Central f] [hg : Central g] : Central (f ≫ g) where
  left_sliding h := by
    simp only [ltimes, whiskerRight_comp, Category.assoc, left_exchange g h, rtimes]
    rw [<-Category.assoc, left_exchange f h, Category.assoc]
  right_sliding h := by
    simp only [ltimes, whiskerLeft_comp, rtimes, Category.assoc, <-right_exchange h g]
    rw [<-Category.assoc, right_exchange h f, Category.assoc]

instance Central.inv {X Y : C} {f : X ⟶ Y} [IsIso f] [Central f] : Central (inv f) where
  left_sliding g := (cancel_epi (f ▷ _)).mp (by
    simp only [← Category.assoc, whiskerRight_comp_inv, Category.id_comp, left_exchange]
    simp)
  right_sliding g := (cancel_epi (_ ◁ f)).mp (by
    rw [whiskerLeft_comp_ltimes, <-right_sliding g]
    simp only [rtimes, ← Category.assoc, whiskerLeft_comp_inv, Category.id_comp]
    simp)

instance Central.inv_hom {X Y : C} {f : X ≅ Y} [hf : Central f.hom] : Central f.inv := by
  convert Central.inv (f := f.hom)
  simp

theorem Central.hom_inv {X Y : C} {f : X ≅ Y} [hf : Central f.inv] : Central f.hom := by
  convert Central.inv (f := f.inv)
  simp

end IsBinoidal

section IsStrict

variable [IsStrict C]

theorem tensor_assoc {X Y Z : C} : (X ⊗ Y) ⊗ Z = X ⊗ (Y ⊗ Z) := IsStrict.tensor_assoc

theorem unit_tensor {X : C} : 𝟙_ C ⊗ X = X := IsStrict.unit_tensor

theorem tensor_unit {X : C} : X ⊗ 𝟙_ C = X := IsStrict.tensor_unit

theorem associator_eq_id {X Y Z : C} : (α_ X Y Z).hom = eq_hom tensor_assoc
  := IsStrict.associator_eq_id

theorem leftUnitor_eq_id {X : C} : (λ_ X).hom = eq_hom unit_tensor := IsStrict.leftUnitor_eq_id

theorem rightUnitor_eq_id {X : C} : (ρ_ X).hom = eq_hom tensor_unit := IsStrict.rightUnitor_eq_id

section IsBinoidal

variable [IsBinoidal C]

theorem associator_central_of_strict {X Y Z : C} : Central (α_ X Y Z).hom
  := by simp [associator_eq_id]

theorem leftUnitor_central_of_strict {X : C} : Central (λ_ X).hom
  := by simp [leftUnitor_eq_id]

theorem rightUnitor_central_of_strict {X : C} : Central (ρ_ X).hom
  := by simp [rightUnitor_eq_id]

theorem pentagon_of_strict {W X Y Z : C} :
  (α_ W X Y).hom ▷ Z ≫ (α_ W (X ⊗ Y) Z).hom ≫ W ◁ (α_ X Y Z).hom =
    (α_ (W ⊗ X) Y Z).hom ≫ (α_ W X (Y ⊗ Z)).hom
  := by simp [associator_eq_id]

theorem triangle_of_strict {X Y : C} :
  (α_ X (𝟙_ _) Y).hom ≫ X ◁ (λ_ Y).hom = (ρ_ X).hom ▷ Y
  := by simp [associator_eq_id, leftUnitor_eq_id, rightUnitor_eq_id]

end IsBinoidal

end IsStrict

section IsPremonoidal

variable [IsPremonoidal C]

theorem associator_naturality {X₁ X₂ X₃ Y₁ Y₂ Y₃ : C} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (f₃ : X₃ ⟶ Y₃) :
  ((f₁ ⊗ f₂) ⊗ f₃) ≫ (α_ Y₁ Y₂ Y₃).hom = (α_ X₁ X₂ X₃).hom ≫ (f₁ ⊗ (f₂ ⊗ f₃))
  := IsPremonoidal.associator_naturality f₁ f₂ f₃

theorem associator_naturality_right {X Y Z : C} (f : X ⟶ X') :
  (f ▷ Y) ▷ Z ≫ (α_ X' Y Z).hom = (α_ X Y Z).hom ≫ f ▷ (Y ⊗ Z) := by
  convert associator_naturality f (𝟙 Y) (𝟙 Z) using 1 <;> simp [tensorHom_def]

theorem associator_naturality_middle {X Y Z : C} (f : Y ⟶ Y') :
  (X ◁ f) ▷ Z ≫ (α_ X Y' Z).hom = (α_ X Y Z).hom ≫ X ◁ (f ▷ Z) := by
  convert associator_naturality (𝟙 _) f (𝟙 _) using 1 <;> simp [tensorHom_def]

theorem associator_naturality_left {X Y Z : C} (f : Z ⟶ Z') :
  (X ⊗ Y) ◁ f ≫ (α_ X Y Z').hom = (α_ X Y Z).hom ≫ X ◁ (Y ◁ f) := by
  convert associator_naturality (𝟙 _) (𝟙 _) f using 1 <;> simp [tensorHom_def]

theorem associator_inv_naturality
  {X₁ X₂ X₃ Y₁ Y₂ Y₃ : C} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (f₃ : X₃ ⟶ Y₃) :
  (f₁ ⊗ (f₂ ⊗ f₃)) ≫ (α_ Y₁ Y₂ Y₃).inv = (α_ X₁ X₂ X₃).inv ≫ ((f₁ ⊗ f₂) ⊗ f₃)
  := (cancel_mono (α_ Y₁ Y₂ Y₃).hom).mp (by simp [associator_naturality])

theorem associator_inv_naturality_right {X Y Z : C} (f : X ⟶ X') :
  f ▷ (Y ⊗ Z) ≫ (α_ X' Y Z).inv = (α_ X Y Z).inv ≫ f ▷ Y ▷ Z := by
  convert associator_inv_naturality f (𝟙 _) (𝟙 _) using 1 <;> simp [tensorHom_def]

theorem associator_inv_naturality_middle {X Y Z : C} (f : Y ⟶ Y') :
  X ◁ (f ▷ Z) ≫ (α_ X Y' Z).inv = (α_ X Y Z).inv ≫ (X ◁ f) ▷ Z := by
  convert associator_inv_naturality (𝟙 _) f (𝟙 _) using 1 <;> simp [tensorHom_def]

theorem associator_inv_naturality_left {X Y Z : C} (f : Z ⟶ Z') :
  X ◁ (Y ◁ f) ≫ (α_ X Y Z').inv = (α_ X Y Z).inv ≫ (X ⊗ Y) ◁ f := by
  convert associator_inv_naturality (𝟙 _) (𝟙 _) f using 1 <;> simp [tensorHom_def]

@[reassoc]
theorem leftUnitor_naturality {X Y : C} (f : X ⟶ Y) :
  𝟙_ C ◁ f ≫ (λ_ Y).hom = (λ_ X).hom ≫ f := IsPremonoidal.leftUnitor_naturality f

@[reassoc]
theorem leftUnitor_inv_naturality {X Y : C} (f : X ⟶ Y) :
  f ≫ (λ_ Y).inv = (λ_ X).inv ≫ 𝟙_C ◁ f := by
  apply (cancel_mono (λ_ Y).hom).mp
  simp [leftUnitor_naturality]

@[reassoc]
theorem rightUnitor_naturality {X Y : C} (f : X ⟶ Y) :
  f ▷ 𝟙_ C ≫ (ρ_ Y).hom = (ρ_ X).hom ≫ f := IsPremonoidal.rightUnitor_naturality f

@[reassoc]
theorem rightUnitor_inv_naturality {X Y : C} (f : X ⟶ Y) :
  f ≫ (ρ_ Y).inv = (ρ_ X).inv ≫ f ▷ 𝟙_ C := by
  apply (cancel_mono (ρ_ Y).hom).mp
  simp [rightUnitor_naturality]

section IsStrict

variable [IsStrict C]

theorem tensorHom_assoc {X₁ Y₁ X₂ Y₂ X₃ Y₃ : C} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (f₃ : X₃ ⟶ Y₃) :
  HEq ((f₁ ⊗ f₂) ⊗ f₃) (f₁ ⊗ (f₂ ⊗ f₃)) := by
  rw [<-heq_iff_eq_hom_right_left]
  convert associator_naturality f₁ f₂ f₃ using 1 <;> simp [associator_eq_id]
  all_goals simp [tensor_assoc]

theorem whiskerRight_whiskerRight_heq {X Y Z Z' : C} {f : Z ⟶ Z'}
  : HEq (f ▷ X ▷ Y) (f ▷ (X ⊗ Y)) := by
  rw [<-heq_iff_eq_hom_right_left]
  convert associator_naturality_right f using 1 <;> simp [associator_eq_id]
  all_goals simp [tensor_assoc]

theorem whiskerRight_whiskerLeft_heq {X Y Z Z' : C} {f : Z ⟶ Z'}
  : HEq ((X ◁ f) ▷ Y) (X ◁ f ▷ Y) := by
  rw [<-heq_iff_eq_hom_right_left]
  convert associator_naturality_middle f using 1 <;> simp [associator_eq_id]
  all_goals simp [tensor_assoc]

theorem whiskerLeft_whiskerLeft_heq {X Y Z Z' : C} {f : Z ⟶ Z'}
  : HEq ((X ⊗ Y) ◁ f) (X ◁ Y ◁ f) := by
  rw [<-heq_iff_eq_hom_right_left]
  convert associator_naturality_left f using 1 <;> simp [associator_eq_id]
  all_goals simp [tensor_assoc]

theorem unit_whiskerLeft_heq {X Y : C} (f : X ⟶ Y) : HEq (𝟙_ C ◁ f) f := by
  rw [<-heq_iff_eq_hom_right_left]
  convert leftUnitor_naturality f using 1 <;> simp [leftUnitor_eq_id]
  all_goals simp [unit_tensor]

theorem whiskerRight_unit_heq {X Y : C} (f : X ⟶ Y) : HEq (f ▷ 𝟙_ C) f := by
  rw [<-heq_iff_eq_hom_right_left]
  convert rightUnitor_naturality f using 1 <;> simp [rightUnitor_eq_id]
  all_goals simp [tensor_unit]

end IsStrict

theorem pentagon {W X Y Z : C} :
  (α_ W X Y).hom ▷ Z ≫ (α_ W (X ⊗ Y) Z).hom ≫ W ◁ (α_ X Y Z).hom =
    (α_ (W ⊗ X) Y Z).hom ≫ (α_ W X (Y ⊗ Z)).hom := IsPremonoidal.pentagon W X Y Z

theorem triangle {X Y : C} : (α_ X (𝟙_ _) Y).hom ≫ X ◁ (λ_ Y).hom = (ρ_ X).hom ▷ Y
  := IsPremonoidal.triangle X Y

-- TODO: interactions with ltimes, rtimes...

instance Central.whiskerRight {X Y Z : C} (f : X ⟶ Y) [hf : Central f] : Central (f ▷ Z) where
  left_sliding g := by
    rw [ltimes]
    apply (cancel_mono (α_ _ _ _).hom).mp
    rw [
      Category.assoc, associator_naturality_left, <-Category.assoc,
      associator_naturality_right, Category.assoc, left_exchange,
      <-Category.assoc, <-associator_naturality_left, Category.assoc,
      <-associator_naturality_right, Category.assoc
    ]
  right_sliding g := by
    rw [ltimes]
    apply (cancel_mono (α_ _ _ _).inv).mp
    rw [
      Category.assoc, associator_inv_naturality_middle, <-Category.assoc,
      associator_inv_naturality_right, Category.assoc, <-whiskerRight_comp, right_exchange,
      whiskerRight_comp, <-Category.assoc, <-associator_inv_naturality_middle, Category.assoc,
      <-associator_inv_naturality_right, rtimes, Category.assoc
    ]

instance Central.whiskerLeft {X Y Z : C} (f : X ⟶ Y) [hf : Central f] : Central (Z ◁ f) where
  left_sliding g := by
    rw [ltimes]
    apply (cancel_mono (α_ _ _ _).hom).mp
    rw [
      Category.assoc, associator_naturality_left, <-Category.assoc,
      associator_naturality_middle, Category.assoc, <-whiskerLeft_comp, left_exchange,
      whiskerLeft_comp, <-Category.assoc, <-associator_naturality_left, Category.assoc,
      <-associator_naturality_middle, rtimes, Category.assoc
    ]
  right_sliding g := by
    rw [rtimes]
    apply (cancel_mono (α_ _ _ _).inv).mp
    rw [
      Category.assoc, associator_inv_naturality_left, <-Category.assoc,
      associator_inv_naturality_right, Category.assoc, right_exchange,
      <-Category.assoc, <-associator_inv_naturality_left, Category.assoc,
      <-associator_inv_naturality_right, Category.assoc
    ]

instance Central.tensorHom {X₁ Y₁ X₂ Y₂ : C} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂)
  [hf : Central f] [hg : Central g] : Central (f ⊗ g) := by rw [tensorHom_def]; infer_instance

instance associator_central {X Y Z : C} : Central (α_ X Y Z).hom := IsPremonoidal.associator_central

theorem associator_inv_central {X Y Z : C} : Central (α_ X Y Z).inv := inferInstance

instance leftUnitor_central {X : C} : Central (λ_ X).hom := IsPremonoidal.leftUnitor_central

theorem leftUnitor_inv_central {X : C} : Central (λ_ X).inv := inferInstance

instance rightUnitor_central {X : C} : Central (ρ_ X).hom := IsPremonoidal.rightUnitor_central

theorem rightUnitor_inv_central {X : C} : Central (ρ_ X).inv := inferInstance

theorem tensor_comp_left {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : C}
  (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (g₁ : Y₁ ⟶ Z₁) (g₂ : Y₂ ⟶ Z₂) [Central g₁] :
  (f₁ ≫ g₁) ⊗ (f₂ ≫ g₂) = (f₁ ⊗ f₂) ≫ (g₁ ⊗ g₂) := by
    simp only [tensorHom_def, whiskerRight_comp, whiskerLeft_comp, <-Category.assoc]
    apply congrArg₂ _ _ rfl
    simp only [Category.assoc, left_exchange g₁ f₂]

theorem tensor_comp_right {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : C}
  (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (g₁ : Y₁ ⟶ Z₁) (g₂ : Y₂ ⟶ Z₂) [Central f₂] :
  (f₁ ≫ g₁) ⊗ (f₂ ≫ g₂) = (f₁ ⊗ f₂) ≫ (g₁ ⊗ g₂) := by
    simp only [tensorHom_def, whiskerRight_comp, whiskerLeft_comp, <-Category.assoc]
    apply congrArg₂ _ _ rfl
    simp only [Category.assoc, right_exchange g₁ f₂]

instance IsMonoidal.of_all_central
  [all_central : ∀{X Y : C}, ∀f : X ⟶ Y, Central f] : IsMonoidal C where
  tensor_comp f₁ f₂ g₁ g₂ := have h := all_central g₁; by rw [tensor_comp_left]

end IsPremonoidal

section IsMonoidal

variable [IsMonoidal C]

theorem tensor_comp {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : C}
  (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (g₁ : Y₁ ⟶ Z₁) (g₂ : Y₂ ⟶ Z₂) :
  (f₁ ≫ g₁) ⊗ (f₂ ≫ g₂) = (f₁ ⊗ f₂) ≫ (g₁ ⊗ g₂) := IsMonoidal.tensor_comp f₁ f₂ g₁ g₂

theorem whisker_exchange {X Y X' Y' : C} (f : X ⟶ Y) (g : X' ⟶ Y')
  : f ▷ X' ≫ Y ◁ g = X ◁ g ≫ f ▷ Y'
  := by simp [<-tensorHom_id, <-id_tensorHom, <-tensor_comp]

theorem sliding {X Y X' Y' : C} (f : X ⟶ Y) (g : X' ⟶ Y') : f ⋉ g = f ⋊ g
  := whisker_exchange f g

@[simp]
instance Central.monoidal {X Y : C} (f : X ⟶ Y) : Central f where
  left_sliding g := sliding f g
  right_sliding g := sliding g f

theorem tensor_eq_rtimes {X₁ Y₁ X₂ Y₂ : C} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) :
  f ⊗ g = f ⋊ g := by rw [<-sliding, tensor_eq_ltimes]

end IsMonoidal

end Monoidal

end CategoryTheory
