import Discretion.Discrete
import Discretion.WithDefault

import Mathlib.Order.WithBot
import Mathlib.Order.Bounds.Basic

/-- A type `α` is equipped with a discrete order, i.e. `a ≤ b → a = b` -/
class DiscreteOrder (α : Type u) [LE α] : Prop where
  le_eq (a b : α) : a ≤ b → a = b

theorem BddAbove.subsingleton_of_discrete {α} [Preorder α] [DiscreteOrder α]
  (s : Set α) : BddAbove s → s.Subsingleton := by
    intro ⟨a, ha⟩
    intro x hx y hy
    simp only [upperBounds, Set.mem_setOf_eq] at ha
    cases DiscreteOrder.le_eq _ _ (ha hx); cases DiscreteOrder.le_eq _ _ (ha hy); rfl

theorem bddAbove_subsingleton {α} [Preorder α] [Nonempty α]
  (s : Set α) (h : s.Subsingleton) : BddAbove s := by
    classical
      if hs : Nonempty s then
        have ⟨x, hx⟩ := hs;
        exact ⟨x, λ_ hy => h hx hy ▸ le_refl x⟩
      else
        exact ⟨Classical.ofNonempty, λx hx => (hs ⟨x, hx⟩).elim⟩

theorem DiscreteOrder.bddAbove_iff {α} [Preorder α] [Nonempty α] [DiscreteOrder α]
  (s : Set α) : BddAbove s ↔ s.Subsingleton := ⟨
    BddAbove.subsingleton_of_discrete s,
    bddAbove_subsingleton s⟩

theorem BddBelow.subsingleton_of_discrete {α} [Preorder α] [DiscreteOrder α]
  (s : Set α) : BddBelow s → s.Subsingleton := by
    intro ⟨a, ha⟩
    intro x hx y hy
    simp only [lowerBounds, Set.mem_setOf_eq] at ha
    cases DiscreteOrder.le_eq _ _ (ha hx); cases DiscreteOrder.le_eq _ _ (ha hy); rfl

theorem bddBelow_subsingleton {α} [Preorder α] [Nonempty α]
  (s : Set α) (h : s.Subsingleton) : BddBelow s := by
    classical
      if hs : Nonempty s then
        have ⟨x, hx⟩ := hs;
        exact ⟨x, λ_ hy => h hx hy ▸ le_refl x⟩
      else
        exact ⟨Classical.ofNonempty, λx hx => (hs ⟨x, hx⟩).elim⟩

theorem DiscreteOrder.bddBelow_iff {α} [Preorder α] [Nonempty α] [DiscreteOrder α]
  (s : Set α) : BddBelow s ↔ s.Subsingleton := ⟨
    BddBelow.subsingleton_of_discrete s,
    bddBelow_subsingleton s⟩

instance Disc.instDiscreteOrder {α} : DiscreteOrder (Disc α) where
  le_eq _ _ h := h

instance OrderDual.instDiscreteOrder {α} [LE α] [DiscreteOrder α]
  : DiscreteOrder (OrderDual α) where
  le_eq a b h := (DiscreteOrder.le_eq (OrderDual.ofDual b) (OrderDual.ofDual a) h).symm

/-- A type `α` is discrete except for a bottom element, i.e., for `a ≠ ⊥`, `a ≤ b → a = b` -/
class DiscreteBotOrder (α : Type u) [LE α] [Bot α] : Prop where
  le_bot_or_eq (a b : α) : a ≤ b → a = ⊥ ∨ a = b

instance {α} [LE α] [Bot α] [DiscreteOrder α] : DiscreteBotOrder α where
  le_bot_or_eq a b h := Or.inr (DiscreteOrder.le_eq a b h)

theorem DiscreteOrder.bot_coe_le_coe {α} {a b : α} [LE α] [DiscreteOrder α]
  : (a : WithBot α) ≤ (b : WithBot α) → a = b
  := by simp only [WithBot.coe_le_coe]; exact le_eq a b

instance WithBot.instDiscreteBotOrder {α} [LE α] [DiscreteOrder α]
  : DiscreteBotOrder (WithBot α) where
  le_bot_or_eq
    | ⊥, b, _ => Or.inl rfl
    | some a, ⊥, h => by simp at h
    | some a, some b, h => Or.inr (by cases DiscreteOrder.bot_coe_le_coe h; rfl)

/-- A type `α` is discrete except for a top element, i.e., for `a ≠ ⊤`, `a ≤ b → a = b` -/
class DiscreteTopOrder (α : Type u) [LE α] [Top α] : Prop where
  le_top_or_eq (a b : α) : a ≤ b → b = ⊤ ∨ a = b

instance {α} [LE α] [Top α] [DiscreteOrder α] : DiscreteTopOrder α where
  le_top_or_eq a b h := Or.inr (DiscreteOrder.le_eq a b h)

theorem DiscreteOrder.top_coe_le_coe {α} {a b : α} [LE α] [DiscreteOrder α]
  : (a : WithTop α) ≤ (b : WithTop α) → a = b
  := by simp only [WithTop.coe_le_coe]; exact le_eq a b

instance WithTop.instDiscreteTopOrder {α} [LE α] [DiscreteOrder α]
  : DiscreteTopOrder (WithTop α) where
  le_top_or_eq
    | a, ⊤, _ => Or.inl rfl
    | ⊤, some b, h => by simp at h
    | some a, some b, h => Or.inr (by cases DiscreteOrder.top_coe_le_coe h; rfl)

class DiscreteBoundedOrder (α : Type u) [LE α] [Bot α] [Top α] : Prop where
  le_bot_or_top_or_eq (a b : α) : a ≤ b → a = ⊥ ∨ b = ⊤ ∨ a = b

def DiscreteOrder.toDiscreteTopOrder {α} [LE α] [Bot α] [Top α] [DiscreteTopOrder α]
  : DiscreteBoundedOrder α where
  le_bot_or_top_or_eq a b h := Or.inr (DiscreteTopOrder.le_top_or_eq a b h)

def DiscreteOrder.toDiscreteBotOrder {α} [LE α] [Bot α] [Top α] [DiscreteBotOrder α]
  : DiscreteBoundedOrder α where
  le_bot_or_top_or_eq a b h := (DiscreteBotOrder.le_bot_or_eq a b h).elim Or.inl (Or.inr ∘ Or.inr)

instance WithBot.instTop {α} [t : Top α] : Top (WithBot α) where
  top := t.top

-- TODO: equality lemmas

instance WithBot.instOrderTop {α} [LE α] [OrderTop α] : OrderTop (WithBot α) where
  le_top | ⊥ => by simp | some a => by simp [instTop, coe_le_coe]

instance WithTop.instBot {α} [b : Bot α] : Bot (WithTop α) where
  bot := b.bot

-- TODO: equality lemmas

instance WithTop.instOrderBot {α} [LE α] [OrderBot α] : OrderBot (WithTop α) where
  bot_le | ⊤ => by simp | some a => by simp [instBot, coe_le_coe]

theorem DiscreteBotOrder.withTop_le {α} [LE α] [αb : Bot α] [DiscreteBotOrder α]
  : {a b : WithTop α} → a ≤ b → a = ⊥ ∨ b = ⊤ ∨ a = b
  | ⊤, _ => by aesop
  | _, ⊤ => by simp
  | some a, some b => by
    simp only [WithTop.some_le_some, WithTop.instBot, false_or]
    intro h
    cases DiscreteBotOrder.le_bot_or_eq a b h <;> simp [WithTop.some, *]

theorem DiscreteTopOrder.withBot_le {α} [LE α] [αt : Top α] [DiscreteTopOrder α]
  : {a b : WithBot α} → a ≤ b → a = ⊥ ∨ b = ⊤ ∨ a = b
  | ⊥, _ => by simp
  | _, ⊥ => by aesop
  | some a, some b => by
    simp only [WithBot.some_le_some, WithBot.instTop, false_or]
    intro h
    cases DiscreteTopOrder.le_top_or_eq a b h <;> simp [WithBot.some, *]

instance WithBot.instDiscreteBoundedOrder {α} [LE α] [Top α] [DiscreteTopOrder α]
  : DiscreteBoundedOrder (WithBot α) where
  le_bot_or_top_or_eq _ _ := DiscreteTopOrder.withBot_le

instance WithTop.instDiscreteBoundedOrder {α} [LE α] [Bot α] [DiscreteBotOrder α]
  : DiscreteBoundedOrder (WithTop α) where
  le_bot_or_top_or_eq _ _ := DiscreteBotOrder.withTop_le

-- TODO: is it a problem that this might cause cycles?
instance DiscreteOrder.isPartialOrder {α} [o : Preorder α] [DiscreteOrder α] : PartialOrder α where
  toPreorder := o
  le_antisymm _ _ h _ := le_eq _ _ h

instance WithBot.instDiscreteOrderSemilatticeInf
  {α} [DecidableEq α] [PartialOrder α] [DiscreteOrder α]
  : SemilatticeInf (WithBot α) where
  inf
    | ⊥, _ => ⊥
    | _, ⊥ => ⊥
    | some a, some b => if a = b then some a else ⊥
  inf_le_left a b := by
    cases a <;> cases b
    case some.some =>
      simp only; split;
      case inl h => cases h; rfl
      case inr => simp
    all_goals simp
  inf_le_right a b := by
    cases a <;> cases b
    case some.some =>
      simp only; split;
      case inl h => cases h; rfl
      case inr => simp
    all_goals simp
  le_inf
    | ⊥, _, _ => by simp
    | _, ⊥, _ => λh => by simp only [le_bot_iff] at h; cases h; simp
    | _, _, ⊥ => λ_ h => by simp only [le_bot_iff] at h; cases h; simp
    | some a, some b, some c => by
      simp only [coe_le_coe]
      intro h h'
      cases DiscreteOrder.le_eq _ _ h
      cases DiscreteOrder.le_eq _ _ h'
      simp

instance WithBot.instDiscreteTopOrderSemilatticeInf
  {α} [DecidableEq α] [PartialOrder α] [OrderTop α] [DiscreteTopOrder α]
  : SemilatticeInf (WithBot α) where
  inf
    | ⊥, _ => ⊥
    | _, ⊥ => ⊥
    | some a, some b => if a = b
      then some a
      else if a = ⊤
      then some b
      else if b = ⊤
      then some a
      else ⊥
  inf_le_left a b := by
    cases a <;> cases b
    case some.some =>
      simp only; split_ifs;
      case neg => simp
      all_goals rename_i h; cases h; apply WithBot.coe_le_coe.mpr; simp
    all_goals simp
  inf_le_right a b := by
    cases a <;> cases b
    case some.some =>
      simp only; split_ifs;
      case neg => simp
      all_goals rename_i h; cases h; apply WithBot.coe_le_coe.mpr; simp
    all_goals simp
  le_inf
    | ⊥, _, _ => by simp
    | _, ⊥, _ => λh => by simp only [le_bot_iff] at h; cases h; simp
    | _, _, ⊥ => λ_ h => by simp only [le_bot_iff] at h; cases h; simp
    | some a, some b, some c => by
      simp only [coe_le_coe]
      intro h h'
      cases DiscreteTopOrder.le_top_or_eq _ _ h with
      | inl h => cases DiscreteTopOrder.le_top_or_eq _ _ h' with
        | inl h' => simp [h, h']
        | inr h' => split <;> simp [*]
      | inr h => cases DiscreteTopOrder.le_top_or_eq _ _ h' with
        | inl h' =>
          cases h'; cases h
          split_ifs <;> simp at *
        | inr h' => rw [<-h, <-h']; simp

instance WithTop.instDiscreteOrderSemilatticeInf
  {α} [DecidableEq α] [PartialOrder α] [DiscreteOrder α]
  : SemilatticeSup (WithTop α) where
  sup
    | ⊤, _ => ⊤
    | _, ⊤ => ⊤
    | some a, some b => if a = b then some a else ⊤
  le_sup_left a b := by
    cases a <;> cases b
    case some.some =>
      simp only; split;
      case inl h => cases h; rfl
      case inr => simp
    all_goals simp
  le_sup_right a b := by
    cases a <;> cases b
    case some.some =>
      simp only; split;
      case inl h => cases h; rfl
      case inr => simp
    all_goals simp
  sup_le
    | ⊤, _, _ => λh => by simp only [top_le_iff] at h; cases h; simp
    | _, ⊤, _ => λ_ h => by simp only [top_le_iff] at h; cases h; simp
    | _, _, ⊤ => by simp
    | some a, some b, some c => by
      simp only [coe_le_coe]
      intro h h'
      cases DiscreteOrder.le_eq _ _ h
      cases DiscreteOrder.le_eq _ _ h'
      simp

instance WithTop.instDiscreteTopOrderSemilatticeInf
  {α} [DecidableEq α] [PartialOrder α] [OrderBot α] [DiscreteBotOrder α]
  : SemilatticeSup (WithTop α) where
  sup
    | ⊤, _ => ⊤
    | _, ⊤ => ⊤
    | some a, some b => if a = b
      then some a
      else if a = ⊥
      then some b
      else if b = ⊥
      then some a
      else ⊤
  le_sup_left a b := by
    cases a <;> cases b
    case some.some =>
      simp only; split_ifs;
      case neg => simp
      all_goals rename_i h; cases h; apply WithTop.coe_le_coe.mpr; simp
    all_goals simp
  le_sup_right a b := by
    cases a <;> cases b
    case some.some =>
      simp only; split_ifs;
      case neg => simp
      all_goals rename_i h; cases h; apply WithTop.coe_le_coe.mpr; simp
    all_goals simp
  sup_le
    | ⊤, _, _ => λh => by simp only [top_le_iff] at h; cases h; simp
    | _, ⊤, _ => λ_ h => by simp only [top_le_iff] at h; cases h; simp
    | _, _, ⊤ => by simp
    | some a, some b, some c => by
      simp only [coe_le_coe]
      intro h h'
      cases DiscreteBotOrder.le_bot_or_eq _ _ h with
      | inl h => cases DiscreteBotOrder.le_bot_or_eq _ _ h' with
        | inl h' => simp [h, h']
        | inr h' => split <;> simp [*]
      | inr h => cases DiscreteBotOrder.le_bot_or_eq _ _ h' with
        | inl h' =>
          cases h'; cases h
          split_ifs <;> simp at *
        | inr h' => rw [h, h']; simp

-- TODO: lattice instances? Or should we do some hax here?

-- instance WithBot.Disc.instSemilatticeInf {α} [DecidableEq α]
--     : SemilatticeInf (WithBot (Disc α)) where
--   inf
--     | ⊥, _ => ⊥
--     | _, ⊥ => ⊥
--     | some a, some b => if a = b then some a else ⊥
--   inf_le_left a b := by
--     cases a <;> cases b
--     case some.some =>
--       simp only; split;
--       case inl h => cases h; rfl
--       case inr => simp
--     all_goals simp
--   inf_le_right a b := by
--     cases a <;> cases b
--     case some.some =>
--       simp only; split;
--       case inl h => cases h; rfl
--       case inr => simp
--     all_goals simp
--   le_inf
--     | ⊥, _, _ => by simp
--     | _, ⊥, _ => λh => by simp only [le_bot_iff] at h; cases h; simp
--     | _, _, ⊥ => λ_ h => by simp only [le_bot_iff] at h; cases h; simp
--     | some a, some b, some c => λh h' => by
--       cases WithBot.coe_le_coe.mp h
--       cases WithBot.coe_le_coe.mp h'
--       simp

-- -- TODO: port to discrete (preorder)

-- instance WithTop.Disc.instSemilatticeSup {α} [DecidableEq α]
--     : SemilatticeSup (WithTop (Disc α)) where
--   sup
--     | ⊤, _ => ⊤
--     | _, ⊤ => ⊤
--     | some a, some b => if a = b then some a else ⊤
--   le_sup_left a b := by
--     cases a <;> cases b
--     case some.some =>
--       simp only; split;
--       case inl h => cases h; rfl
--       case inr => simp
--     all_goals simp
--   le_sup_right a b := by
--     cases a <;> cases b
--     case some.some =>
--       simp only; split;
--       case inl h => cases h; rfl
--       case inr => simp
--     all_goals simp
--   sup_le
--     | _, _, ⊤ => by simp
--     | ⊤, _, _ => λh _ => by simp only [top_le_iff] at h; cases h; simp
--     | _, ⊤, _ => λ_ h => by simp only [top_le_iff] at h; cases h; simp
--     | some a, some b, some c => λh h' => by
--       cases WithTop.coe_le_coe.mp h
--       cases WithTop.coe_le_coe.mp h'
--       simp

-- -- TODO: port to discrete (preorder)

-- instance WithTop.WithBot.Disc.instLattice {α} [DecidableEq α]
--   : Lattice (WithTop (WithBot (Disc α))) where
--   sup
--     | ⊤, _ => ⊤
--     | _, ⊤ => ⊤
--     | ⊥, a => a
--     | a, ⊥ => a
--     | some (some a), some (some b) => if a = b then some (some a) else ⊤
--   le_sup_left
--     | ⊤, a => by aesop
--     | some a, ⊤ => by aesop
--     | ⊥, some a => by simp
--     | some (some a), ⊥ => le_refl _
--     | some (some a), some (some b) => by aesop
--   le_sup_right
--     | ⊤, a => by aesop
--     | some a, ⊤ => by aesop
--     | ⊥, some (some a) => le_refl _
--     | some a, ⊥ => by simp
--     | some (some a), some (some b) => by aesop
--   sup_le
--     | _, _, ⊤ => by simp
--     | _, ⊤, _ => by aesop
--     | ⊤, _, _ => by aesop
--     | ⊥, some (some a), some (some b) => λ_ => id
--     | some (some a), ⊥, some b => λh _ => h
--     | ⊥, ⊥, some b => λh _ => h
--     | a, b, ⊥ => by simp only [le_bot_iff]; intro h h'; cases h; cases h'; rfl
--     | some (some a), some (some b), some (some c) => by
--       simp only [coe_le_coe]
--       intro h h'
--       cases WithBot.coe_le_coe.mp h
--       cases WithBot.coe_le_coe.mp h'
--       simp
--   inf_le_left := by aesop
--   inf_le_right := by aesop
--   le_inf := by aesop

-- -- TODO: port to discrete (preorder)

-- instance WithBot.WithTop.Disc.instLattice {α} [DecidableEq α]
--   : Lattice (WithBot (WithTop (Disc α))) where
--   inf
--     | ⊥, _ => ⊥
--     | _, ⊥ => ⊥
--     | ⊤, a => a
--     | a, ⊤ => a
--     | some (some a), some (some b) => if a = b then some (some a) else ⊥
--   le_sup_left := by aesop
--   le_sup_right := by aesop
--   sup_le := by aesop
--   inf_le_left
--     | ⊥, a => by aesop
--     | some a, ⊥ => by aesop
--     | ⊤, ⊤ => le_refl _
--     | ⊤, some (some a) => by simp
--     | some (some a), ⊤ => le_refl _
--     | some (some a), some (some b) => by aesop
--   inf_le_right
--     | ⊥, a => by aesop
--     | some a, ⊥ => by aesop
--     | ⊤, ⊤ => le_refl _
--     | ⊤, some (some a) => le_refl _
--     | some (some a), ⊤ => by aesop
--     | some (some a), some (some b) => by aesop
--   le_inf
--     | ⊥, _, _ => by simp
--     | _, ⊥, _ => λh => by simp only [le_bot_iff] at h; cases h; simp
--     | _, _, ⊥ => λ_ h => by simp only [le_bot_iff] at h; cases h; simp
--     | some (some a), some (some b), ⊤ => λh _ => h
--     | some a, ⊤, some (some b) => λ_ h => h
--     | some a, ⊤, ⊤ => λ_ _ => le_top
--     | ⊤, a, b => by simp only [top_le_iff]; intro h h'; cases h; cases h'; rfl
--     | some (some a), some (some b), some (some c) => by
--       simp only [coe_le_coe]
--       intro h h'
--       cases WithTop.coe_le_coe.mp h
--       cases WithTop.coe_le_coe.mp h'
--       simp
