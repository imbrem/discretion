import Mathlib.Order.Defs.Unbundled

instance eq_isPartialOrder {α : Type u} : IsPartialOrder α (· = ·) where
  antisymm _ _ h h' := by cases h; cases h'; rfl
