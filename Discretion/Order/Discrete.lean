import Discretion.WithDefault
import Discretion.Disc

import Mathlib.Order.WithBot
import Mathlib.Order.Bounds.Basic

import Mathlib.Data.Sum.Order
import Mathlib.Data.Sigma.Order

-- TODO: can generalize this to a "no nontrivial sup/inf" property
-- TODO: join-complete and meet-complete; this needs to be added to mathlib Someday (TM)

/-- A type `α` is equipped with a discrete order, i.e. `a ≤ b → a = b` -/
class DiscreteOrder (α : Type u) [LE α] : Prop where
  le_eq (a b : α) : a ≤ b → a = b

theorem discrete_order {α} [LE α] [DiscreteOrder α] {a b : α} (h : a ≤ b) : a = b
  := DiscreteOrder.le_eq _ _ h

theorem DiscreteOrder.le_symm {α} [Preorder α] [DiscreteOrder α] {a b : α} (h : a ≤ b) : b ≤ a
  := discrete_order h ▸ le_refl a

@[simp]
theorem DiscreteOrder.not_lt {α} [Preorder α] [DiscreteOrder α] {a b : α} : ¬a < b
  := λh => not_le_of_lt h (le_symm (le_of_lt h))

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

instance {α} [LE α] [Subsingleton α] : DiscreteOrder α where
  le_eq a b _ := Subsingleton.elim a b

instance {α} [LE α] [da : DiscreteOrder α] : DiscreteOrder (WithDefault α) where
  le_eq
  | none, none, _ => rfl
  | some a, some b, h => by rw [da.le_eq _ _ h]

instance {α} [LE α] [LE β]
  [da : DiscreteOrder α] [db : DiscreteOrder β] : DiscreteOrder (α ⊕ β) where
  le_eq a b h := by cases h with | inl h => rw [da.le_eq _ _ h] | inr h => rw [db.le_eq _ _ h]

instance {α} [LE α] [LE β]
  [da : DiscreteOrder α] [db : DiscreteOrder β] : DiscreteOrder (α × β) where
  le_eq | ⟨al, ar⟩, ⟨bl, br⟩, ⟨hl, hr⟩ => by cases da.le_eq _ _ hl; cases db.le_eq _ _ hr; rfl

instance {α} {β : α → Type u} [(a : α) → LE (β a)] [db : (a : α) → DiscreteOrder (β a)]
  : DiscreteOrder ((a : α) × β a) where
  le_eq
  | ⟨al, ar⟩, ⟨bl, br⟩, h =>
    by cases (Sigma.le_def.mp h).1; cases (db _).le_eq _ _ (Sigma.le_def.mp h).2; rfl

instance {ι} {α : ι → Type _} [(i : ι) → LE (α i)] [da : (i : ι) → DiscreteOrder (α i)]
  : DiscreteOrder ((i : ι) → (α i)) where
  le_eq _ _ h := funext (λi => (da i).le_eq _ _ (h i))

instance {α} {p : α → Prop} [LE α] [da : DiscreteOrder α] : DiscreteOrder (Subtype p) where
  le_eq | ⟨a, _⟩, ⟨b, _⟩, h => by cases da.le_eq _ _ h; rfl

/-- A type `α` is discrete except for a bottom element, i.e., for `a ≠ ⊥`, `a ≤ b → a = b` -/
class DiscreteBotOrder (α : Type u) [LE α] [Bot α] : Prop where
  le_bot_or_eq (a b : α) : a ≤ b → a = ⊥ ∨ a = b

theorem discrete_bot_order {α} [LE α] [Bot α] [DiscreteBotOrder α] {a b : α} (h : a ≤ b)
  : a = ⊥ ∨ a = b := DiscreteBotOrder.le_bot_or_eq _ _ h

theorem DiscreteBotOrder.eq_bot_of_ne_of_le
  {α} [LE α] [Bot α] [DiscreteBotOrder α] {a b : α} (h : a ≤ b) (h' : a ≠ b) : a = ⊥
  := (or_iff_left h').mp (discrete_bot_order h)

theorem DiscreteBotOrder.eq_bot_of_lt
  {α} [Preorder α] [Bot α] [DiscreteBotOrder α] {a b : α} (h : a < b) : a = ⊥
  := eq_bot_of_ne_of_le (le_of_lt h) (ne_of_lt h)

theorem DiscreteBotOrder.eq_of_ne_bot_of_le
  {α} [LE α] [Bot α] [DiscreteBotOrder α] {a b : α} (h : a ≤ b) (h' : a ≠ ⊥) : a = b
  := (or_iff_right h').mp (discrete_bot_order h)

theorem DiscreteBotOrder.bot_or_eq
  {α} [LE α] [Bot α] [DiscreteBotOrder α] {a b c : α} (h : c ≤ a) (h' : c ≤ b) : c = ⊥ ∨ a = b
  := match discrete_bot_order h with
  | Or.inl h => Or.inl h
  | Or.inr rfl => discrete_bot_order h'

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

theorem discrete_top_order {α} [LE α] [Top α] [DiscreteTopOrder α] {a b : α} (h : a ≤ b)
  : b = ⊤ ∨ a = b := DiscreteTopOrder.le_top_or_eq _ _ h

theorem DiscreteTopOrder.eq_top_of_ne_of_le
  {α} [LE α] [Top α] [DiscreteTopOrder α] {a b : α} (h : a ≤ b) (h' : a ≠ b) : b = ⊤
  := (or_iff_left h').mp (discrete_top_order h)

theorem DiscreteTopOrder.eq_top_of_lt
  {α} [Preorder α] [Top α] [DiscreteTopOrder α] {a b : α} (h : a < b) : b = ⊤
  := eq_top_of_ne_of_le (le_of_lt h) (ne_of_lt h)

theorem DiscreteTopOrder.eq_of_ne_top_of_le
  {α} [LE α] [Top α] [DiscreteTopOrder α] {a b : α} (h : a ≤ b) (h' : b ≠ ⊤) : a = b
  := (or_iff_right h').mp (discrete_top_order h)

theorem DiscreteTopOrder.top_or_eq
  {α} [LE α] [Top α] [DiscreteTopOrder α] {a b c : α} (h : a ≤ c) (h' : b ≤ c) : c = ⊤ ∨ a = b
  := match discrete_top_order h, discrete_top_order h' with
  | Or.inl h, _ => Or.inl h
  | Or.inr rfl, Or.inl h => Or.inl h
  | Or.inr rfl, Or.inr h => Or.inr h.symm

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

theorem discrete_bounded_order {α} [LE α] [Bot α] [Top α] [DiscreteBoundedOrder α]
  {a b : α} (h : a ≤ b) : a = ⊥ ∨ b = ⊤ ∨ a = b := DiscreteBoundedOrder.le_bot_or_top_or_eq _ _ h

theorem DiscreteBoundedOrder.eq_bounds_of_ne_of_le
  {α} [LE α] [Bot α] [Top α] [DiscreteBoundedOrder α] {a b : α} (h : a ≤ b) (h' : a ≠ b)
  : a = ⊥ ∨ b = ⊤ := match discrete_bounded_order h with
  | Or.inl h => Or.inl h
  | Or.inr (Or.inl h) => Or.inr h
  | Or.inr (Or.inr h) => (h' h).elim

theorem DiscreteBoundedOrder.eq_bounds_of_lt
  {α} [Preorder α] [Bot α] [Top α] [DiscreteBoundedOrder α] {a b : α} (h : a < b) : a = ⊥ ∨ b = ⊤
  := eq_bounds_of_ne_of_le (le_of_lt h) (ne_of_lt h)

-- TODO: think about this
instance DiscreteTopOrder.toDiscreteBoundedOrder {α} [LE α] [Bot α] [Top α] [DiscreteTopOrder α]
  : DiscreteBoundedOrder α where
  le_bot_or_top_or_eq a b h := Or.inr (DiscreteTopOrder.le_top_or_eq a b h)

-- TODO: think about this...
instance DiscreteBotOrder.toDiscreteBoundedOrder {α} [LE α] [Bot α] [Top α] [DiscreteBotOrder α]
  : DiscreteBoundedOrder α where
  le_bot_or_top_or_eq a b h := (DiscreteBotOrder.le_bot_or_eq a b h).elim Or.inl (Or.inr ∘ Or.inr)

theorem DiscreteBotOrder.withTop_le {α} [LE α] [αb : Bot α] [DiscreteBotOrder α]
  : {a b : WithTop α} → a ≤ b → a = ⊥ ∨ b = ⊤ ∨ a = b
  | ⊤, _ => by aesop
  | _, ⊤ => by simp
  | WithTop.some a, WithTop.some b => by
    simp only [WithTop.coe_le_coe, WithTop.instBot, false_or]
    intro h
    cases DiscreteBotOrder.le_bot_or_eq a b h <;> simp [WithTop.some, *]

theorem DiscreteTopOrder.withBot_le {α} [LE α] [αt : Top α] [DiscreteTopOrder α]
  : {a b : WithBot α} → a ≤ b → a = ⊥ ∨ b = ⊤ ∨ a = b
  | ⊥, _ => by simp
  | _, ⊥ => by aesop
  | WithBot.some a, WithBot.some b => by
    simp only [WithBot.coe_le_coe, WithBot.instTop, false_or]
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

-- TODO: decidability for discrete (bounded) orders?

-- TODO: pointwise order on lists; this is a discrete order if the underlying is discrete

-- TODO: a _nontrivial_ order is an order that is not discrete

-- TODO: every linear order on a nontrivial type is nontrivial

-- TODO: WithBot, WithTop on a nontrivial type induce nontrivial orders

-- Some other fun facts:
-- - Every preorder on a subsingleton is a partial order

def DiscTop (α : Type u) := WithTop (Disc α)

instance DiscTop.instPartialOrder {α} : PartialOrder (DiscTop α)
  := (inferInstance : PartialOrder (WithTop (Disc α)))

instance DiscTop.instOrderTop {α} : OrderTop (DiscTop α)
  := (inferInstance : OrderTop (WithTop (Disc α)))

instance DiscTop.instDiscreteTopOrder {α} : DiscreteTopOrder (DiscTop α)
  := (inferInstance : DiscreteTopOrder (WithTop (Disc α)))

def DiscTop.some {α} (a : α) : DiscTop α := WithTop.some a

instance DiscTop.instCoeTC {α} : CoeTC α (DiscTop α) where
  coe := some

@[simp]
theorem DiscTop.coe_le_coe {α} {a b : α} : (a : DiscTop α) ≤ (b : DiscTop α) ↔ a = b
  := WithTop.coe_le_coe

@[elab_as_elim, cases_eliminator]
def DiscTop.casesOn {α} {motive : DiscTop α → Sort v}
  (top : motive ⊤) (coe : (a : α) → motive a) (a : DiscTop α) : motive a
  := match a with
  | ⊤ => top
  | (a : α) => coe a

def DiscTop.leCases {α} {motive : DiscTop α → DiscTop α → Sort v}
  (top : ∀a, motive a ⊤)
  (coe : ∀a : α, motive a a)
  {a b : DiscTop α} (h : a ≤ b)
  : motive a b := match a, b, h with
  | a, ⊤, _ => top _
  | (a : α), (b : α), h => coe_le_coe.mp h ▸ coe a
  | ⊤, (a : α), h => by simp at h; cases h

def DiscTop.leCases' {α} {motive : DiscTop α → DiscTop α → Sort v}
  (top_top : motive ⊤ ⊤)
  (coe_top : ∀a, motive a ⊤)
  (coe_coe : ∀a : α, motive a a)
  {a b : DiscTop α} (h : a ≤ b)
  : motive a b := match a, b, h with
  | ⊤, ⊤, _ => top_top
  | (a : α), ⊤, _ => coe_top _
  | (a : α), (b : α), h => coe_le_coe.mp h ▸ coe_coe a
  | ⊤, (a : α), h => by simp at h; cases h

def DiscBot (α : Type u) := WithBot (Disc α)

instance DiscBot.instPartialOrder {α} : PartialOrder (DiscBot α)
  := (inferInstance : PartialOrder (WithBot (Disc α)))

instance DiscBot.instOrderBot {α} : OrderBot (DiscBot α)
  := (inferInstance : OrderBot (WithBot (Disc α)))

instance DiscBot.instDiscreteBotOrder {α} : DiscreteBotOrder (DiscBot α)
  := (inferInstance : DiscreteBotOrder (WithBot (Disc α)))

def DiscBot.some {α} (a : α) : DiscBot α := WithBot.some a

instance DiscBot.instCoeTC {α} : CoeTC α (DiscBot α) where
  coe := some

@[simp]
theorem DiscBot.coe_le_coe {α} {a b : α} : (a : DiscBot α) ≤ (b : DiscBot α) ↔ a = b
  := WithBot.coe_le_coe

@[elab_as_elim, cases_eliminator]
def DiscBot.casesOn {α} {motive : DiscBot α → Sort v}
  (a : DiscBot α) (bot : motive ⊥) (coe : (a : α) → motive a) : motive a
  := match a with
  | ⊥ => bot
  | (a : α) => coe a

def DiscBot.leCases {α} {motive : DiscBot α → DiscBot α → Sort v}
  (bot : ∀a, motive ⊥ a)
  (coe : ∀a : α, motive a a)
  {a b : DiscBot α} (h : a ≤ b)
  : motive a b := match a, b, h with
  | ⊥, a, _ => bot _
  | (a : α), (b : α), h => coe_le_coe.mp h ▸ coe a
  | (a : α), ⊥, h => by simp at h; cases h

def DiscBot.leCases' {α} {motive : DiscBot α → DiscBot α → Sort v}
  (bot_bot : motive ⊥ ⊥)
  (bot_coe : ∀a, motive ⊥ a)
  (coe_coe : ∀a : α, motive a a)
  {a b : DiscBot α} (h : a ≤ b)
  : motive a b := match a, b, h with
  | ⊥, ⊥, _ => bot_bot
  | ⊥, (a : α), _ => bot_coe _
  | (a : α), (b : α), h => coe_le_coe.mp h ▸ coe_coe a
  | (a : α), ⊥, h => by simp at h; cases h

def DiscBounds (α : Type u) := WithTop (WithBot (Disc α))

instance DiscBounds.instPartialOrder {α} : PartialOrder (DiscBounds α)
  := (inferInstance : PartialOrder (WithTop (WithBot (Disc α))))

instance DiscBounds.instBoundedOrder {α} : BoundedOrder (DiscBounds α)
  := (inferInstance : BoundedOrder (WithTop (WithBot (Disc α))))

instance DiscBounds.instDiscreteBoundedOrder {α} : DiscreteBoundedOrder (DiscBounds α)
  := (inferInstance : DiscreteBoundedOrder (WithTop (WithBot (Disc α))))

def DiscBounds.some {α} (a : α) : DiscBounds α := WithTop.some (WithBot.some a)

instance DiscBounds.instCoeTC {α} : CoeTC α (DiscBounds α) where
  coe := some

@[elab_as_elim, cases_eliminator]
def DiscBounds.casesOn {α} {motive : DiscBounds α → Sort v}
  (a : DiscBounds α) (bot : motive ⊥) (top : motive ⊤) (coe : (a : α) → motive a) : motive a
  := match a with
  | ⊥ => bot
  | ⊤ => top
  | (a : α) => coe a
