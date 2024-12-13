import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Card

variable {α : Type u} {β : Type v} [Fintype α] [DecidableEq β]

def Finset.preimageF1 (f : α → β) (b : β)
  : Finset α := Finset.univ.filter (f · = b)

theorem Finset.mem_preimageF1_iff (f : α → β) (b : β)
  (a : α) : a ∈ preimageF1 f b ↔ f a = b := by simp [preimageF1]

theorem Finset.mem_preimageF1_iff' (f : α → β) (b : β)
  (a : α) : a ∈ preimageF1 f b ↔ a ∈ f⁻¹' {b} := by simp [preimageF1]

theorem Finset.eq_of_preimageF1 (f : α → β) (a : α) (b c : β)
  : a ∈ preimageF1 f b → a ∈ preimageF1 f c → b = c := by
  simp only [mem_preimageF1_iff]
  intro h h'; cases h; cases h'; rfl

theorem Finset.preimageF1_disjoint (f : α → β) (a b : β) (hab : a ≠ b)
  : Disjoint (preimageF1 f a) (preimageF1 f b)
  := Finset.disjoint_left.mpr (λk hk hk' => hab (eq_of_preimageF1 f k a b hk hk'))

def Fintype.preimageCard (f : α → β) (b : β) : ℕ
  := (Finset.preimageF1 f b).card
