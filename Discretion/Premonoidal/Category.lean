import Mathlib.CategoryTheory.Monoidal.Category

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

theorem left_sliding {X Y X' Y' : C}
  (f : X ⟶ Y) (g : X' ⟶ Y') [Central f] : f ⋉ g = f ⋊ g := Central.left_sliding g

theorem right_sliding {X Y X' Y' : C}
  (f : X ⟶ Y) (g : X' ⟶ Y') [Central g] : f ⋉ g = f ⋊ g := Central.right_sliding f

theorem left_exchange {X Y X' Y' : C}
  (f : X ⟶ Y) (g : X' ⟶ Y') [Central f] : (f ▷ X') ≫ (Y ◁ g) = (X ◁ g) ≫ (f ▷ Y')
  := left_sliding f g

theorem right_exchange {X Y X' Y' : C}
  (f : X ⟶ Y) (g : X' ⟶ Y') [Central g] : (f ▷ X') ≫ (Y ◁ g) = (X ◁ g) ≫ (f ▷ Y')
  := right_sliding f g

end Monoidal

-- TODO: is it worth it to separate out IsBinoidal with
-- {tensorHom_def, whisker{Left, Right}_comp, whiskerLeft_id, id_whiskerRight}?

class IsPremonoidal (C: Type u) [Category C] [MonoidalCategoryStruct C] : Prop where
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

@[simp]
instance Central.monoidal [MonoidalCategory C] {X Y : C} (f : X ⟶ Y) : Central f where
  left_sliding := by simp [whisker_exchange]
  right_sliding := by simp [whisker_exchange]

def instMonoidalCategory [MonoidalCategory C] : IsMonoidal C where
  tensorHom_def := MonoidalCategory.tensorHom_def

variable [MonoidalCategoryStruct C]

theorem whiskerRight_comp_rtimes {X Y Z X' Y' : C} (f : X ⟶ Y) (g : Y ⟶ Z) (h : X' ⟶ Y') :
  f ▷ X' ≫ g ⋊ h = f ⋉ h ≫ g ▷ Y' := by simp

theorem whiskerLeft_comp_ltimes {X Y Z X' Y' : C} (f : X ⟶ Y) (g : X' ⟶ Y') (h : Y ⟶ Z) :
  X' ◁ f ≫ g ⋉ h = g ⋊ f ≫ Y' ◁ h := by simp

variable [IsPremonoidal C]

@[simp]
theorem whiskerLeft_id {X Y : C} : X ◁ 𝟙 Y = 𝟙 (X ⊗ Y)
  := IsPremonoidal.whiskerLeft_id _ _

@[simp]
theorem id_whiskerRight {X Y : C} : 𝟙 X ▷ Y = 𝟙 (X ⊗ Y)
  := IsPremonoidal.id_whiskerRight _ _

@[reassoc, simp]
theorem whiskerLeft_comp {X Y Z W : C} (f : X ⟶ Y) (g : Y ⟶ Z)
  : W ◁ (f ≫ g) = (W ◁ f) ≫ (W ◁ g) := IsPremonoidal.whiskerLeft_comp f g

@[reassoc, simp]
theorem whiskerRight_comp {X Y Z W : C} (f : X ⟶ Y) (g : Y ⟶ Z)
  : (f ≫ g) ▷ W = (f ▷ W) ≫ (g ▷ W) :=  IsPremonoidal.whiskerRight_comp f g

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

-- TODO: tensorHom is iso, ltimes is iso, rtimes is iso

theorem tensorHom_def {X₁ Y₁ X₂ Y₂ : C} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) :
  f ⊗ g = (f ▷ X₂) ≫ (Y₁ ◁ g) := IsPremonoidal.tensorHom_def f g

@[simp]
theorem tensorHom_id {X Y : C} : 𝟙 X ⊗ 𝟙 Y = 𝟙 (X ⊗ Y) := by simp [tensorHom_def]

theorem tensorHom_id_left {X Y : C} (f : X ⟶ Y) : 𝟙 X ⊗ f = X ◁ f := by simp [tensorHom_def]

theorem tensorHom_id_right {X Y : C} (f : X ⟶ Y) : f ⊗ 𝟙 Y = f ▷ Y := by simp [tensorHom_def]

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

-- TODO: interactions with ltimes, rtimes...

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

instance Central.id {X : C} : Central (𝟙 X) where
  left_sliding := by simp [ltimes, rtimes]
  right_sliding := by simp [ltimes, rtimes]

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

end Monoidal

end CategoryTheory
