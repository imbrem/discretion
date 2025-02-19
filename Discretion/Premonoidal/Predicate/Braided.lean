-- import Mathlib.CategoryTheory.Monoidal.Category
-- import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
-- import Mathlib.CategoryTheory.Limits.Shapes.Terminal

-- import Discretion.Premonoidal.Predicate.Basic
-- import Discretion.Premonoidal.Property.Braided

-- namespace CategoryTheory

-- open MonoidalCategory
-- open Limits
-- open MorphismProperty

-- namespace Monoidal

-- variable {C : Type _} [Category C] [MonoidalCategoryStruct C] [BraidedCategoryStruct C]

-- theorem TensorClosure.exists_braided {X Y : C} (h : TensorClosure SymmOps X Y)
--   : ∃f : X ⟶ Y, braided C f
--   := by induction h with
--   | refl => exact ⟨𝟙 _, braided.id⟩
--   | tensor_right h I => exact ⟨I.choose ▷ _, braided.whiskerRight I.choose_spec⟩
--   | tensor_left h I => exact ⟨_ ◁ I.choose, braided.whiskerLeft I.choose_spec⟩
--   | trans h1 h2 I1 I2 => exact ⟨I1.choose ≫ I2.choose, braided.comp I1.choose_spec I2.choose_spec⟩
--   | base h => cases h with
--   | swap => exact ⟨σ_ _ _, braided.s (by constructor)⟩
--   | _ => exact ⟨_, braided.monoidalS (by constructor)⟩

-- theorem TensorClosure.of_braided {X Y : C} (f : X ⟶ Y) (hf : braided C f)
--   : TensorClosure SymmOps X Y
--   := by induction hf using braided.induction' with
--   | comp => apply TensorClosure.trans <;> assumption
--   | _ => repeat first | assumption | constructor

-- theorem TensorClosure.exists_braided_iff {X Y : C}
--   : TensorClosure SymmOps X Y ↔ ∃f : X ⟶ Y, braided C f
--   := ⟨TensorClosure.exists_braided, λ⟨f, hf⟩ => of_braided f hf⟩

-- end Monoidal
