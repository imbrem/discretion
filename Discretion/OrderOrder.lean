import Mathlib.Order.Basic

/-- The empty order on a type `α` -/
def EmptyLE (α : Type u) : LE α where
  le _ _ := False

/-- The discrete order on a type `α` -/
def DiscreteLE (α : Type u) : LE α where
  le := Eq

/-- The discrete preorder on a type `α` -/
def DiscretePreorder (α : Type u) : Preorder α where
  toLE := DiscreteLE α
  le_refl _ := rfl
  le_trans _ _ _ := Eq.trans

/-- The discrete partial order on a type `α` -/
def DiscretePartialOrder (α : Type u) : PartialOrder α where
  toPreorder := DiscretePreorder α
  le_antisymm _ _ _ := Eq.symm

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

-- TODO: `PartialOrder` is a `SemilatticeInf` and `OrderBot`, with discrete as ⊥
-- It has no ⊤ if nontrivial.

-- TODO: `toPreorder` is order-preserving and inf-preserving

-- TODO: `toLE` is order-preserving and inf-preserving

-- TODO: A `LinearOrder`'s corresponding `PartialOrder` is maximal

-- TODO: `LinearOrder` has the discrete order, and other facts about this
