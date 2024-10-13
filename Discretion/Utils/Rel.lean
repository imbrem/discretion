import Mathlib.Data.Rel

theorem Rel.inv_eq {α : Type u} : Rel.inv (Eq (α := α)) = Eq := by ext; simp [Eq.comm, inv, flip]
