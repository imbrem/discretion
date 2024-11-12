import Mathlib.Logic.Basic

theorem cast_apply_uniform {α : Sort u} {β β' : α → Sort v}
  (h : ∀i, β i = β' i) (f : ∀i, β i) (i : α) : cast (pi_congr h) f i = cast (h i) (f i)
  := by cases funext h; rfl
