import Mathlib.Data.Set.Finite
import Mathlib.Data.Sum.Order
import Mathlib.Order.Interval.Finset.Defs

import Discretion.Order.Basic
import Discretion.Order.Discrete

def HasFiniteHeight {α : Type u} (_ : Preorder α) : Prop := ∀a : α, Set.Finite (Set.Iic a)

theorem HasFiniteHeight.ofFinite {α : Type u} [Finite α] (p : Preorder α)
  : HasFiniteHeight p := λ_ => Set.toFinite _

theorem HasFiniteHeight.natsLinear : HasFiniteHeight (α := ℕ) inferInstance
  | n => Set.Finite.ofFinset (List.range (n + 1)).toFinset (λx => by simp [Nat.lt_succ])

-- TODO: every discrete order has finite height

-- TODO: iff LocallyFiniteOrderBot

def Preorder.sum {α β} (p : Preorder α) (q : Preorder β) : Preorder (α ⊕ β) :=
  @Sum.instPreorderSum _ _ p q

theorem HasFiniteHeight.sum {p : Preorder α} {q : Preorder β}
  (l : HasFiniteHeight p) (r : HasFiniteHeight q) : HasFiniteHeight (p.sum q)
  | Sum.inl a => by convert Set.Finite.image Sum.inl (l a); ext k; cases k <;> simp
  | Sum.inr b => by convert Set.Finite.image Sum.inr (r b); ext k; cases k <;> simp

def Preorder.prod {α β} (p : Preorder α) (q : Preorder β) : Preorder (α × β) :=
  @Prod.instPreorder _ _ p q

theorem HasFiniteHeight.prod {α β} {p : Preorder α} {q : Preorder β}
  (l : HasFiniteHeight p) (r : HasFiniteHeight q) : HasFiniteHeight (p.prod q)
  | (a, b) => Set.Finite.prod (l a) (r b)

theorem HasFiniteHeight.iso {α β : Type u} {p : Preorder α} {q : Preorder β}
  (r : RelIso p.le q.le) (h : HasFiniteHeight p) : HasFiniteHeight q := λb => by
    convert (h (r.symm b)).map r; ext k
    simp only [Set.mem_Iic, Set.fmap_eq_image, Set.mem_image]
    constructor
    · intro h; exact ⟨r.symm k, by simp [h], by simp⟩
    · intro ⟨k', h, h'⟩; cases h'; rw [<-r.symm.map_rel_iff]; simp [h]

theorem HasFiniteHeight.iso_iff  {α β : Type u} {p : Preorder α} {q : Preorder β}
  (r : RelIso p.le q.le) : HasFiniteHeight p ↔ HasFiniteHeight q
  := ⟨HasFiniteHeight.iso r, HasFiniteHeight.iso r.symm⟩

instance Sum.instLocallyFiniteOrderBot
  [Preorder α] [Preorder β] [l : LocallyFiniteOrderBot α] [r : LocallyFiniteOrderBot β]
  : LocallyFiniteOrderBot (α ⊕ β) where
  finsetIio
    | Sum.inl a => (l.finsetIio a).map Function.Embedding.inl
    | Sum.inr b => (r.finsetIio b).map Function.Embedding.inr
  finsetIic
    | Sum.inl a => (l.finsetIic a).map Function.Embedding.inl
    | Sum.inr b => (r.finsetIic b).map Function.Embedding.inr
  finset_mem_Iic c d := by cases c <;> cases d <;> simp [l.finset_mem_Iic, r.finset_mem_Iic]
  finset_mem_Iio c d := by cases c <;> cases d <;> simp [l.finset_mem_Iio, r.finset_mem_Iio]

-- TODO: LocallyFiniteOrderBot iff preorder HasFiniteHeight

-- TODO: WithBot has LocallyFiniteOrderBot

-- TODO: Every fintype is a LocallyFiniteOrderBot, but this is not generally computable

-- TODO: Every type with the discrete order is LocallyFiniteOrderBot in a trivial way

instance Nat.instLocallyFiniteOrderBot : LocallyFiniteOrderBot ℕ where
  finsetIio n := (List.range n).toFinset
  finsetIic n := (List.range (n + 1)).toFinset
  finset_mem_Iic n i := by simp [Nat.lt_succ]
  finset_mem_Iio n i := by simp

-- TODO: in fact, every countable set with a linear order and a bottom element is a
-- LocallyFiniteOrderBot, since it is either finite or isomorphic to the naturals. This
-- might not be computable, though!
