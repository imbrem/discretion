import Mathlib.Order.Basic
import Mathlib.Logic.Equiv.Defs
import Mathlib.Logic.Nontrivial.Defs
import Mathlib.Data.Fintype.Basic
import Mathlib.Order.BoundedOrder

/-- A type synonym to equip a type with the indiscrete preorder, i.e. `∀ a b, a ≤ b` -/
def Indiscrete (α : Type u) : Type u := α

instance Indiscrete.instNonemptyDisc {α} [h : Nonempty α] : Nonempty (Indiscrete α) := h

instance Indiscrete.instSubsingletonDisc {α} [h : Subsingleton α] : Subsingleton (Indiscrete α) := h

instance Indiscrete.instForAllInhabitedDisc {α} [h : Inhabited α] : Inhabited (Indiscrete α) := h

instance Indiscrete.instPreorder {α} : Preorder (Indiscrete α) where
  le _ _ := True
  le_refl _ := True.intro
  le_trans _ _ _ _ _ := True.intro

/-- `toIndiscrete` is the identity function from `α` to `α` equipped with the indiscrete order  -/
@[match_pattern]
def toIndiscrete {α} : α ≃ Indiscrete α := Equiv.refl α

/-- `ofIndiscrete` is the identity function from `α` equipped with the indiscrete order to `α` -/
@[match_pattern]
def ofIndiscrete {α} : Indiscrete α ≃ α := Equiv.refl (Indiscrete α)

@[simp]
theorem toIndiscrete_symm_eq {α} : toIndiscrete.symm = @ofIndiscrete α := rfl

@[simp]
theorem ofIndiscrete_symm_eq {α} : ofIndiscrete.symm = @toIndiscrete α := rfl

@[simp]
theorem toIndiscrete_ofIndiscrete {α} (a : Indiscrete α) : toIndiscrete (ofIndiscrete a) = a := rfl

@[simp]
theorem ofIndiscrete_toIndiscrete {α} (a : α) : ofIndiscrete (toIndiscrete a) = a := rfl

theorem toIndiscrete_inj {α} {a b : α} : toIndiscrete a = toIndiscrete b ↔ a = b := Iff.rfl

theorem ofIndiscrete_inj {α} {a b : Indiscrete α} : ofIndiscrete a = ofIndiscrete b ↔ a = b
  := Iff.rfl

/-- A recursor for `Indiscrete`. Use as `induction x using Indiscrete.rec`. -/
def Indiscrete.rec {α} {β : Indiscrete α -> Sort _}
  (h : (a : α) → β (toIndiscrete a)) (a : Indiscrete α) : β a := h (ofIndiscrete a)

@[simp]
theorem Indiscrete.forall {α} {p : Indiscrete α → Prop}
  : (∀a : Indiscrete α, p a) ↔ ∀a : α, p (toIndiscrete a) := Iff.rfl

@[simp]
theorem Indiscrete.exists {α} {p : Indiscrete α → Prop}
  : (∃a : Indiscrete α, p a) ↔ ∃a : α, p (toIndiscrete a) := Iff.rfl

instance Indiscrete.instNontrivialDisc {α} [h : Nontrivial α] : Nontrivial (Indiscrete α) := h

instance Indiscrete.fintype {α} [h : Fintype α] : Fintype (Indiscrete α) := h

instance Indiscrete.finite {α} [h : Finite α] : Finite (Indiscrete α) := h

instance Indiscrete.instBoundedOrder {α} [Inhabited α] : BoundedOrder (Indiscrete α) where
  top := default
  le_top _ := True.intro
  bot := default
  bot_le _ := True.intro
