import Discretion.Nonempty.Set

class SupNSet (α : Type u) where
  nsSup : NSet α → α

class NSemilatticeSup (α : Type u) [PartialOrder α] extends SupNSet α where
  le_nsSup (s : NSet α) (a : α) : a ∈ s → a ≤ nsSup s
  nsSup_le (s : NSet α) (a : α) : (∀b ∈ s, b ≤ a) → nsSup s ≤ a

-- @[priority std.default.priority-1]
instance SupNSet.ofSupSet (α : Type u) [SupSet α] : SupNSet α where
  nsSup s := sSup s
