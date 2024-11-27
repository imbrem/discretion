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
