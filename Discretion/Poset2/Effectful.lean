import Discretion.Premonoidal.Effectful
import Discretion.Poset2.Premonoidal

namespace CategoryTheory

open scoped MonoidalCategory

open PremonoidalCategory MonoidalCategory'

open MorphismProperty

open HasCommRel

class RightMover [Category C] [MonoidalCategoryStruct C] [Refines C]
  (L R : MorphismProperty C) where
  left_fwd : ∀ {X Y X' Y' : C} (f : X ⟶ Y) (g : X' ⟶ Y'), L f → R g → f ⋉ g ↠ f ⋊ g
  right_fwd : ∀ {X Y X' Y' : C} (f : X ⟶ Y) (g : X' ⟶ Y'), L f → R g → g ⋊ f ↠ g ⋉ f

abbrev LeftMover [Category C] [MonoidalCategoryStruct C] [Refines C]
  (L R : MorphismProperty C) := RightMover R L

theorem Commutes.of_left_right
  [Category C] [MonoidalCategoryStruct C] [Poset2 C]
  (L R : MorphismProperty C) [right : RightMover L R] [left : LeftMover L R]
  : Commutes L R where
  left_exchange f g hf hg
    := refines_antisymm (RightMover.left_fwd f g hf hg) (RightMover.right_fwd g f hg hf)
  right_exchange f g hf hg
    := refines_antisymm (RightMover.left_fwd g f hg hf) (RightMover.right_fwd f g hf hg)

theorem Commutes.right
  [Category C] [MonoidalCategoryStruct C] [Poset2 C]
  (L R : MorphismProperty C) [hC : Commutes L R] : RightMover L R where
  left_fwd f g hf hg := refines_of_eq (Commutes.left_exchange f g hf hg)
  right_fwd f g hf hg := refines_of_eq (Commutes.right_exchange f g hf hg).symm

theorem Commutes.left
  [Category C] [MonoidalCategoryStruct C] [Poset2 C]
  (L R : MorphismProperty C) [hC : Commutes L R] : LeftMover L R
  := right R L (hC := hC.symm)

class Effectful2
  (C : Type v) [Category C] [PremonoidalCategory C] [BraidedCategory' C]
  (ε : Type u) [EffectSystem ε] extends EffectfulCategory C ε, MonPoset2 C where
  eff_right_mover : ∀{e e' : ε}, e ⇀ e' → RightMover (eff e) (eff e')
  eff_comm h
    := Commutes.of_left_right _ _ (right := eff_right_mover h.1) (left := eff_right_mover h.2)

variable {C : Type v} [Category C] [PremonoidalCategory C] [BraidedCategory' C]
  {ε : Type u} [EffectSystem ε] [EC : Effectful2 C ε]

theorem Effectful2.eff_left_mover {e e' : ε} (h : e ↽ e') : LeftMover (EC.eff e) (EC.eff e')
  := eff_right_mover h

theorem Effectful2.eff_commutes {e e' : ε} (h : e ⇌ e') : Commutes (EC.eff e) (EC.eff e')
  := Commutes.of_left_right (EC.eff e) (EC.eff e')
      (right := eff_right_mover h.1)
      (left := eff_left_mover h.2)

theorem Effectful2.eff_left_fwd
  {X₁ Y₁ X₂ Y₂ : C} {el er : ε} (h : el ⇀ er)
    (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) [hf : EC.HasEff el f] [hg : EC.HasEff er g] :
    f ▷ X₂ ≫ Y₁ ◁ g ↠ X₁ ◁ g ≫ f ▷ Y₂
    := (EC.eff_right_mover h).left_fwd f g hf.has_eff hg.has_eff

theorem Effectful2.eff_right_fwd
  {X₁ Y₁ X₂ Y₂ : C} {el er : ε} (h : el ⇀ er)
    (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) [hf : EC.HasEff el f] [hg : EC.HasEff er g] :
    _ ◁ f ≫ g ▷ _ ↠ g ▷ _ ≫ _ ◁ f
    := (EC.eff_right_mover h).right_fwd f g hf.has_eff hg.has_eff

theorem Effectful2.eff_left_bwd
  {X₁ Y₁ X₂ Y₂ : C} {el er : ε} (h : el ↽ er)
    (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) [hf : EC.HasEff el f] [hg : EC.HasEff er g] :
    f ▷ X₂ ≫ Y₁ ◁ g ↞ X₁ ◁ g ≫ f ▷ Y₂
    := (EC.eff_left_mover h).right_fwd g f hg.has_eff hf.has_eff

theorem Effectful2.eff_right_bwd
  {X₁ Y₁ X₂ Y₂ : C} {el er : ε} (h : el ↽ er)
    (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) [hf : EC.HasEff el f] [hg : EC.HasEff er g] :
    _ ◁ f ≫ g ▷ _ ↞ g ▷ _ ≫ _ ◁ f
    := (EC.eff_left_mover h).left_fwd g f hg.has_eff hf.has_eff


theorem Effectful2.eff_left_fwd_assoc_app
  {X₁ Y₁ X₂ Y₂ Z : C} {el er : ε} (he : el ⇀ er)
    (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂)
    {h h' : Y₁ ⊗ Y₂ ⟶ Z} (hh : h ↠ h')
    [hf : EC.HasEff el f] [hg : EC.HasEff er g] :
    f ▷ X₂ ≫ Y₁ ◁ g ≫ h ↠ X₁ ◁ g ≫ f ▷ Y₂ ≫ h'
  := by
  rw [<-Category.assoc, <-Category.assoc]
  exact refines_comp (eff_left_fwd he f g) hh

theorem Effectful2.eff_left_fwd_assoc
  {X₁ Y₁ X₂ Y₂ Z : C} {el er : ε} (he : el ⇀ er)
    (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂)
    (h : Y₁ ⊗ Y₂ ⟶ Z)
    [hf : EC.HasEff el f] [hg : EC.HasEff er g] :
    f ▷ X₂ ≫ Y₁ ◁ g ≫ h ↠ X₁ ◁ g ≫ f ▷ Y₂ ≫ h
  := eff_left_fwd_assoc_app he f g (refines_refl h)

theorem Effectful2.eff_right_fwd_assoc_app
  {X₁ Y₁ X₂ Y₂ Z : C} {el er : ε} (he : el ⇀ er)
    (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂)
    {h h' : Y₂ ⊗ Y₁ ⟶ Z} (hh : h ↠ h')
    [hf : EC.HasEff el f] [hg : EC.HasEff er g] :
    _ ◁ f ≫ g ▷ _ ≫ h ↠ g ▷ _ ≫ _ ◁ f ≫ h'
  := by
  rw [<-Category.assoc, <-Category.assoc]
  exact refines_comp (eff_right_fwd he f g) hh

theorem Effectful2.eff_right_fwd_assoc
  {X₁ Y₁ X₂ Y₂ Z : C} {el er : ε} (he : el ⇀ er)
    (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂)
    (h : Y₂ ⊗ Y₁ ⟶ Z)
    [hf : EC.HasEff el f] [hg : EC.HasEff er g] :
    _ ◁ f ≫ g ▷ _ ≫ h ↠ g ▷ _ ≫ _ ◁ f ≫ h
  := eff_right_fwd_assoc_app he f g (refines_refl h)

theorem Effectful2.eff_left_bwd_assoc_app
  {X₁ Y₁ X₂ Y₂ Z : C} {el er : ε} (he : el ↽ er)
    (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂)
    {h h' : Y₁ ⊗ Y₂ ⟶ Z} (hh : h ↞ h')
    [hf : EC.HasEff el f] [hg : EC.HasEff er g] :
    f ▷ X₂ ≫ Y₁ ◁ g ≫ h ↞ X₁ ◁ g ≫ f ▷ Y₂ ≫ h'
  := by
  rw [<-Category.assoc, <-Category.assoc]
  exact refines_comp (eff_left_bwd he f g) hh

theorem Effectful2.eff_left_bwd_assoc
  {X₁ Y₁ X₂ Y₂ Z : C} {el er : ε} (he : el ↽ er)
    (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂)
    (h : Y₁ ⊗ Y₂ ⟶ Z)
    [hf : EC.HasEff el f] [hg : EC.HasEff er g] :
    f ▷ X₂ ≫ Y₁ ◁ g ≫ h ↞ X₁ ◁ g ≫ f ▷ Y₂ ≫ h
  := eff_left_bwd_assoc_app he f g (refines_refl h)

theorem Effectful2.eff_right_bwd_assoc_app
  {X₁ Y₁ X₂ Y₂ Z : C} {el er : ε} (he : el ↽ er)
    (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂)
    {h h' : Y₂ ⊗ Y₁ ⟶ Z} (hh : h ↞ h')
    [hf : EC.HasEff el f] [hg : EC.HasEff er g] :
    _ ◁ f ≫ g ▷ _ ≫ h ↞ g ▷ _ ≫ _ ◁ f ≫ h'
  := by
  rw [<-Category.assoc, <-Category.assoc]
  exact refines_comp (eff_right_bwd he f g) hh

theorem Effectful2.eff_right_bwd_assoc
  {X₁ Y₁ X₂ Y₂ Z : C} {el er : ε} (he : el ↽ er)
    (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂)
    (h : Y₂ ⊗ Y₁ ⟶ Z)
    [hf : EC.HasEff el f] [hg : EC.HasEff er g] :
    _ ◁ f ≫ g ▷ _ ≫ h ↞ g ▷ _ ≫ _ ◁ f ≫ h
  := eff_right_bwd_assoc_app he f g (refines_refl h)
