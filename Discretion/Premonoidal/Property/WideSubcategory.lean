import Discretion.Premonoidal.Property.Basic
import Discretion.Premonoidal.Property.Braided
import Mathlib.CategoryTheory.Widesubcategory

namespace CategoryTheory

variable {C : Type u} [Category C]

@[ext]
theorem WideSubcategory.hom_ext {W : MorphismProperty C} [W.IsMultiplicative]
  {X Y : WideSubcategory W} (f g : X ⟶ Y)
  (h : f.val = g.val) : f = g := by cases f; cases g; cases h; rfl

open scoped MonoidalCategory

open MonoidalCategory'

open PremonoidalCategory

open MorphismProperty

section PremonoidalCategory

variable [PremonoidalCategory C]

instance WideSubcategory.monoidalCategoryStruct (W : MorphismProperty C) [W.IsMonoidal]
  : MonoidalCategoryStruct (WideSubcategory W) where
  tensorObj X Y := ⟨X.obj ⊗ Y.obj⟩
  whiskerLeft Z X Y f := ⟨Z.obj ◁ f.val, whiskerLeft_mem f.prop⟩
  whiskerRight f Z := ⟨f.val ▷ Z.obj, whiskerRight_mem f.prop⟩
  tensorHom f g := ⟨f.val ⊗ g.val, tensorHom_mem f.prop g.prop⟩
  tensorUnit := ⟨𝟙_ C⟩
  associator X Y Z := ⟨
      ⟨(α_ _ _ _).hom, associator_hom_mem⟩, ⟨(α_ _ _ _).inv, associator_inv_mem⟩,
      by ext; simp, by ext; simp
    ⟩
  leftUnitor X := ⟨
      ⟨(λ_ _).hom, leftUnitor_hom_mem⟩, ⟨(λ_ _).inv, leftUnitor_inv_mem⟩,
      by ext; simp, by ext; simp
    ⟩
  rightUnitor X := ⟨
      ⟨(ρ_ _).hom, rightUnitor_hom_mem⟩, ⟨(ρ_ _).inv, rightUnitor_inv_mem⟩,
      by ext; simp, by ext; simp
    ⟩

@[simp]
theorem obj_tensorObj {W : MorphismProperty C} [W.IsMonoidal]
  (X Y : WideSubcategory W) : (X ⊗ Y).obj = X.obj ⊗ Y.obj := rfl

@[simp]
theorem coe_tensorHom {W : MorphismProperty C} [W.IsMonoidal]
  {X Y X' Y' : WideSubcategory W} (f : X ⟶ Y) (g : X' ⟶ Y') : (f ⊗ g).val = f.val ⊗ g.val := rfl

@[simp]
theorem coe_whiskerLeft {W : MorphismProperty C} [W.IsMonoidal]
  {Z X Y : WideSubcategory W} (f : X ⟶ Y) : (Z ◁ f).val = Z.obj ◁ f.val := rfl

@[simp]
theorem coe_whiskerRight {W : MorphismProperty C} [W.IsMonoidal]
  {X Y Z : WideSubcategory W} (f : X ⟶ Y) : (f ▷ Z).val = f.val ▷ Z.obj := rfl

@[simp]
theorem coe_ltimes {W : MorphismProperty C} [W.IsMonoidal]
  {X Y X' Y' : WideSubcategory W} (f : X ⟶ Y) (g : X' ⟶ Y') : (f ⋉ g).val = f.val ⋉ g.val := rfl

@[simp]
theorem coe_rtimes {W : MorphismProperty C} [W.IsMonoidal]
  {X Y X' Y' : WideSubcategory W} (f : X ⟶ Y) (g : X' ⟶ Y') : (f ⋊ g).val = f.val ⋊ g.val := rfl

theorem PremonoidalCategory.Central.wide {W : MorphismProperty C} [W.IsMonoidal]
  {X Y : C} (f : X ⟶ Y) [Central f] (hf : W f)
  : Central (C := WideSubcategory W) (X := ⟨X⟩) (Y := ⟨Y⟩) (Subtype.mk f hf) where
  left_exchange g := by ext; simp [Central.left_exchange]
  right_exchange g := by ext; simp [Central.right_exchange]

theorem PremonoidalCategory.Central.of_val {W : MorphismProperty C} [W.IsMonoidal]
  {X Y : WideSubcategory W} (f : X ⟶ Y) [Central f.val]
  : Central f where
  left_exchange g := by ext; simp [PremonoidalCategory.Central.left_exchange]
  right_exchange g := by ext; simp [PremonoidalCategory.Central.right_exchange]

instance PremonoidalCategory.Central.ofCentral {W : MorphismProperty C} [W.IsMonoidal] [W.Central]
  {X Y : WideSubcategory W} (f : X ⟶ Y)
  : Central f where
  left_exchange g := by
    ext; have _ := mem_central f.prop;
    simp [PremonoidalCategory.Central.left_exchange]
  right_exchange g := by
    ext; have _ := mem_central f.prop;
    simp [PremonoidalCategory.Central.right_exchange]

instance WideSubcategory.instPremonoidalCategory (W : MorphismProperty C) [W.IsMonoidal]
  : PremonoidalCategory (WideSubcategory W) where
  tensorHom_def f g := by ext; simp [PremonoidalCategory.tensorHom_def]
  associator_central := Central.wide (α_ _ _ _).hom _
  leftUnitor_central := Central.wide (λ_ _).hom _
  rightUnitor_central := Central.wide (ρ_ _).hom _
  associator_naturality f g h := by ext; apply PremonoidalCategory.associator_naturality
  leftUnitor_naturality f := by ext; apply PremonoidalCategory.leftUnitor_naturality
  rightUnitor_naturality f := by ext; apply PremonoidalCategory.rightUnitor_naturality
  pentagon W X Y Z := by ext; apply PremonoidalCategory.pentagon
  triangle X Y := by ext; apply PremonoidalCategory.triangle

instance WideSubcategory.instMonoidalCategory (W : MorphismProperty C)
  [W.IsMonoidal] [HWC : W.Central] : MonoidalCategory' (WideSubcategory W) where
  whisker_exchange | ⟨f, hf⟩, ⟨g, hg⟩
                    => by simp [CategoryStruct.comp, (HWC.central hf).left_exchange g]

-- TODO: WideSubcategory also inherits braidedness

end PremonoidalCategory
