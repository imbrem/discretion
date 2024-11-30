/- == Imports == -/

/- This part should go in Mathlib.Order.Synonym -/
import Mathlib.Order.Basic
import Mathlib.Logic.Equiv.Defs
import Mathlib.Logic.Nontrivial.Defs
/- This part should go in Mathlib.Order.Max -/
import Mathlib.Order.Max
/- This part should go in Mathlib.Data.Fintype.Basic -/
import Mathlib.Data.Fintype.Basic

/- == Definitions == -/

/- This part should go in Mathlib.Order.Synonym -/

/-- A type synonym to equip a type with the discrete partial order, i.e. `a ≤ b` iff `a = b` -/
def Disc (α : Type u) : Type u := α

instance Disc.instNonemptyDisc {α} [h : Nonempty α] : Nonempty (Disc α) := h

instance Disc.instSubsingletonDisc {α} [h : Subsingleton α] : Subsingleton (Disc α) := h

instance Disc.instForAllInhabitedDisc {α} [h : Inhabited α] : Inhabited (Disc α) := h

instance Disc.instPartialOrder {α} : PartialOrder (Disc α) where
  le := Eq
  le_refl _ := rfl
  le_trans _ _ _ := Eq.trans
  le_antisymm _ _ _ := Eq.symm

theorem Disc.le_symm {α} {a b : Disc α} : a ≤ b → b ≤ a := Eq.symm

/-- `toDisc` is the identity function from `α` to `α` equipped with the discrete order  -/
@[match_pattern]
def toDisc {α} : α ≃ Disc α := Equiv.refl α

/-- `ofDisc` is the identity function from `α` equipped with the discrete order to `α` -/
@[match_pattern]
def ofDisc {α} : Disc α ≃ α := Equiv.refl (Disc α)

theorem Disc.toDisc_le_toDisc {α} {a b : α} : toDisc a ≤ toDisc b ↔ a = b := Iff.rfl

theorem Disc.toDisc_lt_toDisc {α} {a b : α} : ¬toDisc a < toDisc b := λh => h.2 (h.1 ▸ rfl)

@[simp]
theorem toDisc_symm_eq {α} : toDisc.symm = @ofDisc α := rfl

@[simp]
theorem ofDisc_symm_eq {α} : ofDisc.symm = @toDisc α := rfl

@[simp]
theorem toDisc_ofDisc {α} (a : Disc α) : toDisc (ofDisc a) = a := rfl

@[simp]
theorem ofDisc_toDisc {α} (a : α) : ofDisc (toDisc a) = a := rfl

theorem toDisc_inj {α} {a b : α} : toDisc a = toDisc b ↔ a = b := Iff.rfl

theorem ofDisc_inj {α} {a b : Disc α} : ofDisc a = ofDisc b ↔ a = b := Iff.rfl

/-- A recursor for `Disc`. Use as `induction x using Disc.rec`. -/
def Disc.rec {α} {β : Disc α -> Sort _} (h : (a : α) → β (toDisc a)) (a : Disc α) : β a
  := h (ofDisc a)

@[simp]
theorem Disc.forall {α} {p : Disc α → Prop} : (∀a : Disc α, p a) ↔ ∀a : α, p (toDisc a) := Iff.rfl

@[simp]
theorem Disc.exists {α} {p : Disc α → Prop} : (∃a : Disc α, p a) ↔ ∃a : α, p (toDisc a) := Iff.rfl

instance Disc.instNontrivialDisc {α} [h : Nontrivial α] : Nontrivial (Disc α) := h

/- This part should go in Mathlib.Order.Max -/

instance Disc.instNoBotOrder {α} [h : Nontrivial α] : NoBotOrder (Disc α) where
  exists_not_ge a := by
    have ⟨x, y, hxy⟩ := h.exists_pair_ne
    if h : a = x then
      exact ⟨y, h ▸ hxy⟩
    else
      exact ⟨x, h⟩

instance Disc.instNoTopOrder {α} [h : Nontrivial α] : NoTopOrder (Disc α) where
  exists_not_le a := by
    have ⟨x, y, hxy⟩ := h.exists_pair_ne
    if h : x = a then
      exact ⟨y, h ▸ hxy.symm⟩
    else
      exact ⟨x, h⟩

/- This part should go in Mathlib.Data.Fintype.Basic -/

instance Disc.fintype {α} [h : Fintype α] : Fintype (Disc α) := h

instance Disc.finite {α} [h : Finite α] : Finite (Disc α) := h

instance Disc.instDecidableEq {α} [h : DecidableEq α] : DecidableEq (Disc α) := h
