import Mathlib.Order.Basic
import Mathlib.Order.BoundedOrder

/-- The empty order on a type `α` -/
def EmptyLE (α : Type u) : LE α where
  le _ _ := False

/-- The discrete order on a type `α` -/
def DiscreteLE (α : Type u) : LE α where
  le := Eq

@[simp]
theorem discreteLE_le : LE.le (self := DiscreteLE α) a b ↔ a = b := Iff.rfl

/-- The discrete preorder on a type `α` -/
def DiscretePreorder (α : Type u) : Preorder α where
  toLE := DiscreteLE α
  le_refl _ := rfl
  le_trans _ _ _ := Eq.trans

@[simp]
theorem discretePreorder_le : LE.le (self := (DiscretePreorder α).toLE) a b ↔ a = b := Iff.rfl

/-- The discrete partial order on a type `α` -/
def DiscretePartialOrder (α : Type u) : PartialOrder α where
  toPreorder := DiscretePreorder α
  le_antisymm _ _ _ := Eq.symm

@[simp]
theorem discretePartialOrder_le : LE.le (self := (DiscretePartialOrder α).toLE) a b ↔ a = b
  := Iff.rfl

/-- The indiscrete order on a type `α` -/
def IndiscreteLE (α : Type u) : LE α where
  le _ _ := True

/-- The indiscrete preorder on a type `α` -/
def IndiscretePreorder (α : Type u) : Preorder α where
  toLE := IndiscreteLE α
  le_refl _ := True.intro
  le_trans _ _ _ _ _ := True.intro

instance LE.instLE {α : Type u} : LE (LE α) where
  le h1 h2 := h1.le ≤ h2.le

theorem LE.le_of_le_le {α : Type u} {h1 h2 : LE α} (h : h1.le ≤ h2.le) : h1 ≤ h2 := h
theorem LE.le_le_of_le {α : Type u} {h1 h2 : LE α} (h : h1 ≤ h2) : h1.le ≤ h2.le := h

instance LE.instPartialOrder {α : Type u} : PartialOrder (LE α) where
  le_refl _ := @le_refl (α → α → Prop) _ _
  le_trans _ _ _ := @le_trans (α → α → Prop) _ _ _ _
  le_antisymm _ _ h h' := LE.ext (le_antisymm h h')

-- TODO: `LE` is a distributive, complete semilattice, with empty as ⊥ and indiscrete as ⊤

instance Preorder.instLE {α : Type u} : LE (Preorder α) where
  le h1 h2 := h1.le ≤ h2.le

theorem Preorder.le_of_le_le {α : Type u} {h1 h2 : LE α} (h : h1.le ≤ h2.le) : h1 ≤ h2 := h
theorem Preorder.le_le_of_le {α : Type u} {h1 h2 : LE α} (h : h1 ≤ h2) : h1.le ≤ h2.le := h

instance Preorder.instPartialOrder {α : Type u} : PartialOrder (Preorder α) where
  le_refl _ := @le_refl (α → α → Prop) _ _
  le_trans _ _ _ := @le_trans (α → α → Prop) _ _ _ _
  le_antisymm _ _ h h'
    := Preorder.ext (λ_ _ => le_antisymm (le_le_of_le h) (le_le_of_le h') ▸ Iff.rfl)

-- TODO: `Preorder` is a complete semilattice, with discrete as ⊥ and indiscrete as ⊤

-- TODO: `toLE` is order-preserving and inf-preserving but *not* sup-preserving

instance PartialOrder.instLE {α : Type u} : LE (PartialOrder α) where
  le h1 h2 := h1.le ≤ h2.le

theorem PartialOrder.le_of_le_le {α : Type u} {h1 h2 : LE α} (h : h1.le ≤ h2.le) : h1 ≤ h2 := h
theorem PartialOrder.le_le_of_le {α : Type u} {h1 h2 : LE α} (h : h1 ≤ h2) : h1.le ≤ h2.le := h

instance PartialOrder.instPartialOrder {α : Type u} : PartialOrder (PartialOrder α) where
  le_refl _ := @le_refl (α → α → Prop) _ _
  le_trans _ _ _ := @le_trans (α → α → Prop) _ _ _ _
  le_antisymm _ _ h h'
    := PartialOrder.ext (λ_ _ => _root_.le_antisymm (le_le_of_le h) (le_le_of_le h') ▸ Iff.rfl)

instance PartialOrder.instOrderBot {α : Type u} : OrderBot (PartialOrder α) where
  bot := DiscretePartialOrder α
  bot_le p a b h := by cases h; apply le_refl _

@[simp]
theorem partial_order_bot_le {α} {a b : α}
  : LE.le (self := (⊥ : PartialOrder α).toLE) a b ↔ a = b := Iff.rfl

instance PartialOrder.instSemilatticeInf {α : Type u} : SemilatticeInf (PartialOrder α) where
  inf p q := {
    le := λa b => p.le a b ∧ q.le a b
    lt := λa b => (p.le a b ∧ q.le a b) ∧ ¬(p.le b a ∧ q.le b a)
    le_refl := λa => ⟨p.le_refl a, q.le_refl a⟩
    le_trans := λa b c hab hbc => ⟨p.le_trans a b c hab.1 hbc.1, q.le_trans a b c hab.2 hbc.2⟩
    le_antisymm := λa b hab hba => p.le_antisymm a b hab.1 hba.1
    lt_iff_le_not_le := λ_ _ => Iff.rfl
  }
  inf_le_left _ _ _ _ h := h.1
  inf_le_right _ _ _ _ h := h.2
  le_inf _ _ _ hpq hqr a b h := ⟨hpq a b h, hqr a b h⟩

-- It has no ⊤ if nontrivial.

-- TODO: `toPreorder` is order-preserving and inf-preserving

-- TODO: `toLE` is order-preserving and inf-preserving

-- TODO: A `LinearOrder`'s corresponding `PartialOrder` is maximal

-- TODO: `LinearOrder` has the discrete order, and other facts about this
