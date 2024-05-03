import Discretion.Discrete
import Discretion.WithDefault

import Mathlib.Order.WithBot
import Mathlib.Order.Bounds.Basic

-- TODO: can generalize this to a "no nontrivial sup/inf" property
-- TODO: join-complete and meet-complete; this needs to be added to mathlib Someday (TM)

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

instance instOrderBotDiscreteBotOrderSemilatticeInf
  {α} [DecidableEq α] [PartialOrder α] [OrderBot α] [DiscreteBotOrder α]
  : SemilatticeInf α where
  inf a b := if a = b then a else ⊥
  inf_le_left a b := by simp only; split <;> simp
  inf_le_right a b := by simp only; split <;> simp [*]
  le_inf a b c ha hb := by
    cases DiscreteBotOrder.le_bot_or_eq _ _ ha with
    | inl ha => cases ha; simp
    | inr ha => cases ha; cases DiscreteBotOrder.le_bot_or_eq _ _ hb <;> simp [*]

instance instOrderTopDiscreteTopOrderSemilatticeSup
  {α} [DecidableEq α] [PartialOrder α] [OrderTop α] [DiscreteTopOrder α]
  : SemilatticeSup α where
  sup a b := if a = b then a else ⊤
  le_sup_left a b := by simp only; split <;> simp
  le_sup_right a b := by simp only; split <;> simp [*]
  sup_le a b c ha hb := by
    cases DiscreteTopOrder.le_top_or_eq _ _ hb with
    | inl hb => cases hb; simp
    | inr hb => cases hb; cases DiscreteTopOrder.le_top_or_eq _ _ ha <;> simp [*]

instance instDiscreteBoundedOrderLattice
  {α} [DecidableEq α] [PartialOrder α] [BoundedOrder α] [DiscreteBoundedOrder α]
  : Lattice α where
  inf a b := if a = b then a else if a = ⊤ then b else if b = ⊤ then a else ⊥
  inf_le_left a b := by simp only; split_ifs <;> simp [*]
  inf_le_right a b := by simp only; split_ifs <;> simp [*]
  le_inf a b c ha hb := by
    cases DiscreteBoundedOrder.le_bot_or_top_or_eq _ _ ha with
    | inl ha => cases ha; simp
    | inr ha => cases ha with
      | inl ha => cases ha; cases DiscreteBoundedOrder.le_bot_or_top_or_eq _ _ hb with
        | inl hb => cases hb; simp
        | inr hb => cases hb with
          | inl hb => cases hb; simp
          | inr hb => cases hb; simp only; split <;> simp
      | inr ha => cases ha; cases DiscreteBoundedOrder.le_bot_or_top_or_eq _ _ hb with
        | inl hb => cases hb; simp
        | inr hb => cases hb with
          | inl hb => cases hb; simp only; split <;> simp
          | inr hb => cases hb; simp only; split_ifs <;> simp
  sup a b := if a = b then a else if a = ⊥ then b else if b = ⊥ then a else ⊤
  le_sup_left a b := by simp only; split_ifs <;> simp [*]
  le_sup_right a b := by simp only; split_ifs <;> simp [*]
  sup_le a b c ha hb := by
    cases DiscreteBoundedOrder.le_bot_or_top_or_eq _ _ hb with
    | inl hb => cases hb; simp only; split <;> simp [ha]
    | inr hb => cases hb with
      | inl hb => cases hb; cases DiscreteBoundedOrder.le_bot_or_top_or_eq _ _ ha with
        | inl ha => cases ha; simp
        | inr ha => simp
      | inr hb => cases hb; cases DiscreteBoundedOrder.le_bot_or_top_or_eq _ _ ha with
        | inl ha => cases ha; simp only; split <;> simp
        | inr ha => cases ha with
          | inl ha => cases ha; simp
          | inr ha => cases ha; simp
