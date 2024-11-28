import Mathlib.CategoryTheory.Iso

namespace CategoryTheory

variable {C : Type u}

def eq_hom [CategoryStruct C] {X Y : C} (p : X = Y) : X ⟶ Y := p ▸ 𝟙 X

variable [Category C]

@[simp]
theorem eq_hom_refl {X : C} : eq_hom (Eq.refl X) = 𝟙 X := rfl

@[simp]
theorem eq_hom_comp {X Y Z : C} (p : X = Y) (q : Y = Z)
  : eq_hom p ≫ eq_hom q = eq_hom (p.trans q) := by cases p; cases q; simp

instance IsIso.eq_hom {X Y : C} (p : X = Y) : IsIso (eq_hom p)
  := by cases p; rw [eq_hom_refl]; infer_instance

@[simp]
theorem inv_eq_hom {X Y : C} (p : X = Y) : inv (eq_hom p) = eq_hom p.symm := by cases p; simp

theorem inv_eq_hom' {X Y : C} (p : X = Y) : eq_hom p = inv (eq_hom p.symm) := by cases p; simp

theorem heq_iff_eq_hom_left {X Y Z : C} (p : X = Y) (f : Y ⟶ Z) (g : X ⟶ Z)
  : eq_hom p ≫ f = g ↔ HEq f g := by cases p; simp

theorem heq_iff_eq_hom_right {X Y Z : C} (f : X ⟶ Y) (p : Y = Z) (g : X ⟶ Z)
  : f ≫ eq_hom p = g ↔ HEq f g := by cases p; simp

theorem heq_iff_eq_hom {X Y Z W : C} (p : X = Y) (f : Y ⟶ Z) (q : Z = W) (g : X ⟶ W)
  : eq_hom p ≫ f ≫ eq_hom q = g ↔ HEq f g := by cases p; cases q; simp

theorem heq_iff_eq_hom' {X Y Z W : C} (p : X = Y) (f : Y ⟶ Z) (q : Z = W) (g : X ⟶ W)
  : (eq_hom p ≫ f) ≫ eq_hom q = g ↔ HEq f g := by cases p; cases q; simp

theorem heq_iff_eq_hom_right_left {X Y Z W : C} (p : X = Y) (f : X ⟶ Z) (q : Z = W) (g : Y ⟶ W)
  : f ≫ eq_hom q = eq_hom p ≫ g ↔ HEq f g := by cases p; cases q; simp

theorem heq_iff_eq_hom_left_right {X Y Z W : C} (p : X = Y) (f : Y ⟶ W) (q : Z = W) (g : X ⟶ Z)
  : eq_hom p ≫ f = g ≫ eq_hom q ↔ HEq f g := by cases p; cases q; simp
