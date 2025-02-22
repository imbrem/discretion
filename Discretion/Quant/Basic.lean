-- import Mathlib.Data.Fintype.Order -- NOTE: this breaks partialorder for bool... lower priority?
import Mathlib.Data.Fintype.Prod
import Mathlib.Algebra.Group.WithOne.Defs
import Mathlib.Algebra.Group.Pointwise.Set.Basic
import Mathlib.Algebra.Order.Monoid.Unbundled.WithTop
import Mathlib.Algebra.GroupWithZero.Pointwise.Set.Basic
import Mathlib.Algebra.Order.Ring.Defs
import Discretion.Utils
import Discretion.Vector.Basic

inductive DupCap : Type
  | copy
  | del
  deriving DecidableEq

instance DupCap.instFintype : Fintype DupCap where
  elems := {DupCap.copy, DupCap.del}
  complete x := by cases x <;> simp

def Quant := Bool × Bool

@[match_pattern]
def Quant.copy : Quant := ⟨true, false⟩

@[match_pattern]
def Quant.del : Quant := ⟨false, true⟩

abbrev Quant.is_copy (q : Quant) : Bool := q.1

@[simp]
theorem Quant.copy_is_copy : copy.is_copy := rfl

@[simp]
theorem Quant.del_is_copy : del.is_copy = false := rfl

abbrev Quant.is_del (q : Quant) : Bool := q.2

@[simp]
theorem Quant.copy_is_del : copy.is_del = false := rfl

@[simp]
theorem Quant.del_is_del : del.is_del := rfl

instance Quant.instMax : Max Quant := (inferInstance : Max (Bool × Bool))

instance Quant.instMin : Min Quant := (inferInstance : Min (Bool × Bool))

instance Quant.instBooleanAlgebra : BooleanAlgebra Quant
  := (inferInstance : BooleanAlgebra (Bool × Bool))

theorem Quant.is_copy_le {q : Quant} (h : q.is_copy) : .copy ≤ q := ⟨by simp [h], by simp⟩

theorem Quant.is_del_le {q : Quant} (h : q.is_del) : .del ≤ q := ⟨by simp, by simp [h]⟩

instance Quant.instDecidableEq : DecidableEq Quant
  := (inferInstance : DecidableEq (Bool × Bool))

instance Quant.instDecidableLE : DecidableRel (· ≤ · : Quant → Quant → Prop)
  := (inferInstance : DecidableRel (· ≤ · : Bool × Bool → Bool × Bool → Prop))

def Quant.dc (q : Quant) : Set DupCap | .copy => q.is_copy | .del => q.is_del

theorem Quant.copy_mem_dc {q : Quant} : .copy ∈ q.dc ↔ q.is_copy := Iff.rfl

theorem Quant.del_mem_dc {q : Quant} : .del ∈ q.dc ↔ q.is_del := Iff.rfl

@[simp]
theorem Quant.dc_copy : copy.dc = {DupCap.copy}
  := by ext c; cases c <;> simp [copy_mem_dc, del_mem_dc]

@[simp]
theorem Quant.dc_del : del.dc = {DupCap.del} := by ext c; cases c <;> simp [copy_mem_dc, del_mem_dc]

instance Quant.instOne : One Quant where one := ⟨false, false⟩

instance Quant.instTop : Top Quant where top := ⟨true, true⟩

instance Quant.instBot : Bot Quant where bot := 1

@[simp]
theorem Quant.dc_top : dc ⊤ = Set.univ
  := by ext c; cases c <;> simp [copy_mem_dc, del_mem_dc, Top.top]

@[simp]
theorem Quant.dc_bot : dc ⊥ = ∅ := by ext c; cases c <;> simp [copy_mem_dc, del_mem_dc]

noncomputable def ofDc (dc : Set DupCap) : Quant
  := open Classical in ⟨DupCap.copy ∈ dc, DupCap.del ∈ dc⟩

-- TODO: dc is a lattice isomorphism with inverse ofDc

@[simp]
theorem Quant.top_ne_bot : (⊤ : Quant) ≠ ⊥ := by intro h; cases h

@[simp]
theorem Quant.bot_ne_top : (⊥ : Quant) ≠ ⊤ := by intro h; cases h

@[simp]
theorem Quant.copy_ne_bot : Quant.copy ≠ ⊥ := by intro h; cases h

@[simp]
theorem Quant.bot_ne_copy : ⊥ ≠ Quant.copy := by intro h; cases h

@[simp]
theorem Quant.copy_ne_top : Quant.copy ≠ ⊤ := by intro h; cases h

@[simp]
theorem Quant.top_ne_copy : ⊤ ≠ Quant.copy := by intro h; cases h

@[simp]
theorem Quant.del_ne_bot : Quant.del ≠ ⊥ := by intro h; cases h

@[simp]
theorem Quant.bot_ne_del : ⊥ ≠ Quant.del := by intro h; cases h

@[simp]
theorem Quant.del_ne_top : Quant.del ≠ ⊤ := by intro h; cases h

@[simp]
theorem Quant.top_ne_del : ⊤ ≠ Quant.del := by intro h; cases h

@[elab_as_elim, cases_eliminator]
def Quant.casesOn {motive : Quant → Sort _}
  (top : motive ⊤)
  (copy : motive Quant.copy)
  (del : motive Quant.del)
  (one : motive 1)
  : ∀(q : Quant), motive q
  | ⊤ => top
  | Quant.copy => copy
  | Quant.del => del
  | 1 => one

theorem Quant.is_del_iff {q : Quant} : q.is_del ↔ .del ≤ q := by cases q <;> decide

theorem Quant.is_copy_iff {q : Quant} : q.is_copy ↔ .copy ≤ q := by cases q <;> decide

@[simp]
theorem Quant.one_le {q : Quant} : 1 ≤ q := by cases q <;> decide

@[simp]
theorem Quant.one_ne_top : (1 : Quant) ≠ ⊤ := by intro h; cases h

@[elab_as_elim, cases_eliminator]
def Quant.le.casesOn_all {motive : ∀{q q' : Quant}, q ≤ q' → Sort _}
  (top_top : @motive ⊤ ⊤ (by simp))
  (copy_top : @motive .copy ⊤ (by simp))
  (del_top : @motive .del ⊤ (by simp))
  (bot_top : @motive ⊥ ⊤ (by simp))
  (copy_copy : @motive .copy .copy (by simp))
  (bot_copy : @motive ⊥ .copy (by simp))
  (del_del : @motive .del .del (by simp))
  (bot_del : @motive ⊥ .del (by simp))
  (bot_bot : @motive ⊥ ⊥ (by simp))
  {q q'} (h : q ≤ q') : motive h
  := match q, q' with
  | ⊤, ⊤ => top_top
  | .copy, ⊤ => copy_top
  | .del, ⊤ => del_top
  | ⊥, ⊤ => bot_top
  | .copy, .copy => copy_copy
  | ⊥, .copy => bot_copy
  | .del, .del => del_del
  | ⊥, .del => bot_del
  | ⊥, ⊥ => bot_bot

def Quant.casesOn_le {motive : ∀{q q' : Quant}, q ≤ q' → Sort _}
  (top : ∀q, @motive q ⊤ (by simp))
  (copy : @motive .copy .copy (by rfl))
  (del : @motive .del .del (by rfl))
  (bot_copy : @motive ⊥ .copy (by simp))
  (bot_del : @motive ⊥ .del (by simp))
  (bot : @motive ⊥ ⊥ (by simp))
  {q q'} (h : q ≤ q') : motive h
  := match q, q' with
  | q, ⊤ => top q
  | .copy, .copy => copy
  | .del, .del => del
  | ⊥, .copy => bot_copy
  | ⊥, .del => bot_del
  | ⊥, ⊥ => bot

def Quant.casesOn_le_db {motive : ∀{q q' : Quant}, q ≤ q' → Sort _}
  (diag : ∀q, @motive q q (by rfl))
  (top : ∀q, q ≠ ⊤ → @motive q ⊤ (by simp))
  (bot : ∀q, q ≠ ⊥ → @motive ⊥ q (by simp))
  {q q'} (h : q ≤ q') : motive h
  := match q, q' with
  | ⊤, ⊤ => diag ⊤
  | .copy, ⊤ => top .copy (by simp)
  | .del, ⊤ => top .del (by simp)
  | ⊥, ⊤ => top ⊥ (by simp)
  | .copy, .copy => diag .copy
  | .del, .del => diag .del
  | ⊥, .copy => bot .copy (by simp)
  | ⊥, .del => bot .del (by simp)
  | ⊥, ⊥ => diag ⊥

instance Quant.instFintype : Fintype Quant where
  elems := {1, copy, del, ⊤}
  complete x := by cases x <;> simp

def DupCap.c : DupCap → Set ℕ | .copy => Set.Ici 1 | .del => {0, 1}

@[simp]
theorem DupCap.c_copy : copy.c = Set.Ici 1 := rfl

@[simp]
theorem DupCap.c_del : del.c = {0, 1} := rfl

@[simp]
theorem DupCap.iUnion_c : ⋃d : DupCap, d.c = Set.univ := by
  ext n;
  simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
  cases n with
  | zero => exact ⟨.del, by simp [DupCap.c]⟩
  | succ n => exact ⟨.copy, by simp [DupCap.c]⟩

@[simp]
def DupCap.bc (d : DupCap) : Bool → Set ℕ
  | true => d.c
  | false => {1}

def Quant.c (q : Quant) : Set ℕ := { n | n = 1 ∨ (q.is_del ∧ n = 0) ∨ (q.is_copy ∧ n > 1) }

@[simp]
theorem Quant.top_is_copy : (⊤ : Quant).is_copy := rfl

@[simp]
theorem Quant.top_is_del : (⊤ : Quant).is_del := rfl

@[simp]
theorem Quant.bot_is_not_copy : ¬(⊥ : Quant).is_copy := by simp [Bot.bot]

@[simp]
theorem Quant.bot_is_not_del : ¬(⊥ : Quant).is_del := by simp [Bot.bot]

@[simp]
theorem Quant.c_top : c ⊤ = Set.univ := by ext n; simp [Quant.c]; omega

@[simp]
theorem Quant.c_copy : c copy = Set.Ici 1 := by ext n; simp [Quant.c]; omega

@[simp]
theorem Quant.c_del : c del = {0, 1} := by ext n; simp [Quant.c]; omega

@[simp]
theorem Quant.c_bot : c ⊥ = {1} := by ext n; simp [Quant.c]

@[simp]
theorem Quant.c_one : c 1 = {1} := by simp [Quant.c]

theorem Quant.is_del_mono {l r : Quant} : l ≤ r → l.is_del → r.is_del := by
  cases l <;> cases r <;> simp [copy, Top.top, Bot.bot, del, LE.le]

theorem Quant.is_copy_mono {l r : Quant} : l ≤ r → l.is_copy → r.is_copy := by
  cases l <;> cases r <;> simp [copy, Top.top, Bot.bot, del, LE.le]

theorem Quant.inf_is_del {l r : Quant} : (l ⊓ r).is_del ↔ l.is_del ∧ r.is_del
  := by simp [is_del, min, SemilatticeInf.inf, Lattice.inf]

theorem Quant.sup_is_del {l r : Quant} : (l ⊔ r).is_del ↔ l.is_del ∨ r.is_del
  := by simp [is_del, max, SemilatticeSup.sup]

theorem Quant.inf_is_copy {l r : Quant} : (l ⊓ r).is_copy ↔ l.is_copy ∧ r.is_copy
  := by simp [is_copy, min, SemilatticeInf.inf, Lattice.inf]

theorem Quant.sup_is_copy {l r : Quant} : (l ⊔ r).is_copy ↔ l.is_copy ∨ r.is_copy
  := by simp [is_copy, max, SemilatticeSup.sup]

theorem Quant.c_inf {l r : Quant} : c (l ⊓ r) = c l ∩ c r
  := by ext n; simp only [c, inf_is_del, inf_is_copy]; aesop

theorem Quant.c_sup {l r : Quant} : c (l ⊔ r) = c l ∪ c r
  := by ext n; simp only [c, sup_is_del, sup_is_copy]; aesop

theorem Quant.c_def' {q : Quant} : q.c = DupCap.del.bc q.is_del ∪ DupCap.copy.bc q.is_copy := by
  ext n; cases q <;> simp; omega

-- theorem Quant.c_def_bigUnion {q : Quant} : q.c = {1} ∪ ⋃d ∈ q.dc, d.c := by cases q <;> simp

@[simp]
theorem Quant.zero_mem_c_iff {q : Quant} : 0 ∈ q.c ↔ .del ≤ q
  := by simp [Quant.c, is_del_iff]

@[simp]
theorem Quant.one_mem_c {q : Quant} : 1 ∈ q.c := by simp [Quant.c]

@[simp]
theorem Quant.n_plus_two_mem_c_iff {q : Quant} {n} : n + 2 ∈ q.c ↔ .copy ≤ q
  := by simp [Quant.c, is_copy_iff]

theorem Quant.two_mem_c_iff {q : Quant} : 2 ∈ q.c ↔ .copy ≤ q := n_plus_two_mem_c_iff

instance Quant.instAddCommSemigroup : AddCommSemigroup Quant where
  add
  | .copy, .copy | ⊥, .copy | .copy, ⊥ | ⊥, ⊥ => .copy
  | _, _ => ⊤
  add_assoc a b c := by cases a <;> cases b <;> cases c <;> rfl
  add_comm a b := by cases a <;> cases b <;> rfl

theorem Quant.add_mono {l r l' r' : Quant} (hl : l ≤ l') (hr : r ≤ r') : l + r ≤ l' + r' := by
  cases hl <;> cases hr <;> decide

@[simp]
theorem Quant.left_le_add {l r : Quant} : l ≤ l + r := by cases l <;> cases r <;> decide

@[simp]
theorem Quant.right_le_add {l r : Quant} : r ≤ l + r := by cases l <;> cases r <;> decide

open Pointwise

theorem Quant.c_add {l r : Quant} : (c l) + (c r) ⊆ c (l + r) := λn ⟨x, hx, y, hy, hxy⟩ => by
  cases l <;> cases r <;> simp [HAdd.hAdd, Add.add] <;> simp [Set.mem_add] at * <;> omega

instance Quant.instCommMonoid : CommMonoid Quant where
  mul
  | 1, q | q, 1 => q
  | .del, .del => .del
  | .copy, .copy => .copy
  | _, _ => ⊤
  one_mul a := by cases a <;> rfl
  mul_one a := by cases a <;> rfl
  mul_assoc a b c := by cases a <;> cases b <;> cases c <;> rfl
  mul_comm a b := by cases a <;> cases b <;> rfl

@[simp]
theorem Quant.mul_top {q : Quant} : q * ⊤ = ⊤ := by cases q <;> rfl

@[simp]
theorem Quant.top_mul {q : Quant} : ⊤ * q = ⊤ := by cases q <;> rfl

@[simp]
theorem Quant.copy_mul_copy : Quant.copy * Quant.copy = Quant.copy := rfl

@[simp]
theorem Quant.del_mul_del : Quant.del * Quant.del = Quant.del := rfl

@[simp]
theorem Quant.copy_mul_del : Quant.copy * Quant.del = ⊤ := rfl

@[simp]
theorem Quant.del_mul_copy : Quant.del * Quant.copy = ⊤ := rfl

theorem Quant.c_subset_mul {l r : Quant} : (c l) * (c r) ⊆ c (l * r) := by
  cases l <;> cases r <;> simp
  case copy.copy =>
    intro n ⟨x, hx, y, hy, hxy⟩
    cases hxy; simp only [Set.mem_Ici, ge_iff_le] at *; apply one_le_mul <;> assumption
  case del.del =>
    intro n ⟨x, hx, y, hy, hxy⟩
    cases hxy; cases hx <;> cases hy <;> simp_all

@[simp]
theorem Set.Ici_one_mul_Ici_one [MulOneClass α] [Preorder α] [MulLeftMono α]
  : Set.Ici (α := α) 1 * Set.Ici 1 = Set.Ici 1 := by
  ext n; simp only [mem_mul, mem_Ici]
  constructor
  intro ⟨x, hx, y, hy, hxy⟩
  cases hxy; apply one_le_mul <;> assumption
  intro hn
  exact ⟨1, le_refl _, n, hn, by simp⟩

@[simp]
theorem Set.zero_one_mul_zero_one [MulZeroOneClass α]
  : ({0, 1} : Set α) * {0, 1} = {0, 1}
  := by ext k; simp [mem_mul]; tauto

@[simp]
theorem Set.one_mem_mul_univ {α : Type _} [MulOneClass α]
  (s : Set α) (hs : 1 ∈ s) : s * Set.univ = Set.univ := by
  ext k
  simp only [mem_mul, mem_univ, true_and, iff_true]
  exists 1
  simp [*]

@[simp]
theorem Set.one_mem_univ_mul {α : Type _} [MulOneClass α]
  (s : Set α) (hs : 1 ∈ s) : Set.univ * s = Set.univ := by
  ext k
  simp only [mem_mul, mem_univ, true_and, iff_true]
  exists k
  exists 1
  simp [*]

@[simp]
theorem Set.zero_one_mul_Ici_one : ({0, 1} : Set ℕ) * Set.Ici 1 = Set.univ := by
  ext k
  cases k <;> simp [mem_mul]; exists 1

@[simp]
theorem Set.Ici_one_mul_zero_one : Set.Ici 1 * {0, 1} = Set.univ := by
  ext k
  cases k <;> simp [mem_mul]; exists 1

theorem Quant.c_mul {l r : Quant} : c (l * r) = (c l) * (c r) := by
  have hl := l.one_mem_c; have hr := r.one_mem_c; cases l <;> cases r <;> simp

-- NOTE: this operation should have another name
-- section Mul

-- instance Quant.instCommSemigroup : CommSemigroup Quant where
--   mul
--   | .del, q => q
--   | q, .del => q
--   | ⊤, _ => ⊤
--   | _, ⊤ => ⊤
--   | _, _ => .copy
--   mul_assoc a b c := by cases a <;> cases b <;> cases c <;> rfl
--   mul_comm a b := by cases a <;> cases b <;> rfl

-- -- This is scoped because I don't like the "1" instance it requires
-- scoped instance Quant.sep_comm_monoid : CommMonoid Quant where
--   one := .del
--   one_mul a := by cases a <;> rfl
--   mul_one a := by cases a <;> rfl
--   mul_comm := CommSemigroup.mul_comm

-- @[simp]
-- theorem Quant.mul_del {q : Quant} : .del * q = q := by cases q <;> rfl

-- @[simp]
-- theorem Quant.del_mul {q : Quant} : q * .del = q := by cases q <;> rfl

-- @[simp]
-- theorem Quant.mul_top {q : Quant} : q * ⊤ = ⊤ := by cases q <;> rfl

-- @[simp]
-- theorem Quant.top_mul {q : Quant} : ⊤ * q = ⊤ := by cases q <;> rfl

-- @[simp]
-- theorem Quant.copy_mul_copy : Quant.copy * .copy = .copy := rfl

-- @[simp]
-- theorem Quant.copy_mul_bot : Quant.copy * ⊥ = .copy := rfl

-- @[simp]
-- theorem Quant.bot_mul_copy : ⊥ * Quant.copy = .copy := rfl

-- @[simp]
-- theorem Quant.bot_mul_bot : ⊥ * ⊥ = Quant.copy := rfl

-- @[simp]
-- theorem Quant.le_mul_self {q : Quant} : q ≤ q * q := by cases q <;> simp

-- end Mul

def EQuant : Type := Option Quant

@[match_pattern]
def EQuant.zero : EQuant := none

instance EQuant.instZero : Zero EQuant := ⟨EQuant.zero⟩

@[coe, match_pattern]
def EQuant.some : Quant → EQuant := Option.some

instance EQuant.instCoeTC : CoeTC Quant EQuant := ⟨EQuant.some⟩

def EQuant.casesOn' {motive : EQuant → Sort _}
  (zero : motive 0)
  (coe : ∀a : Quant, motive a)
  : ∀(q : EQuant), motive q
  | 0 => zero
  | (a : Quant) => coe a

@[match_pattern]
def EQuant.copy : EQuant := Quant.copy

theorem EQuant.copy_def : EQuant.copy = Quant.copy := rfl

@[match_pattern]
def EQuant.del : EQuant := Quant.del

theorem EQuant.del_def : EQuant.del = Quant.del := rfl

instance EQuant.instOne : One EQuant where one := (⊥ : Quant)

theorem EQuant.one_def : (1 : EQuant) = (⊥ : Quant) := rfl

instance EQuant.instTop : Top EQuant where top := (⊤ : Quant)

@[simp]
theorem EQuant.coe_top : ((⊤ : Quant) : EQuant) = ⊤ := rfl

@[simp]
theorem EQuant.coe_bot : ((⊥ : Quant) : EQuant) = 1 := rfl

instance EQuant.instFintype : Fintype EQuant := (inferInstance : Fintype (Option Quant))

@[elab_as_elim, cases_eliminator]
def EQuant.casesOn {motive : EQuant → Sort _}
  (zero : motive 0)
  (one : motive 1)
  (copy : motive .copy)
  (del : motive .del)
  (top : motive ⊤)
  : ∀(q : EQuant), motive q
  | 0 => zero
  | 1 => one
  | .copy => copy
  | .del => del
  | ⊤ => top

@[elab_as_elim, induction_eliminator]
def EQuant.casesZero {motive : EQuant → Sort _}
  (zero : motive 0)
  (rest : ∀q : Quant, motive q)
  : ∀(q : EQuant), motive q
  | 0 => zero
  | (q : Quant) => rest q

instance EQuant.instDecidableEq : DecidableEq EQuant := (inferInstance : DecidableEq (Option Quant))

instance EQuant.instLE : LE EQuant where
  le
  | (a : Quant), (b : Quant) => a ≤ b
  | 0, (b : Quant) => .del ≤ b
  | (_ : Quant), 0 => False
  | 0, 0 => True

@[simp]
theorem EQuant.coe_le_coe {l r : Quant} : (l : EQuant) ≤ r ↔ l ≤ r := by rfl

instance EQuant.instDecidableLE : DecidableRel (· ≤ · : EQuant → EQuant → Prop) := λ
  | (a : Quant), (b : Quant) => Quant.instDecidableLE a b
  | 0, (b : Quant) => Quant.instDecidableLE .del b
  | (_ : Quant), 0 => isFalse (by tauto)
  | 0, 0 => isTrue (by trivial)

instance EQuant.instOrderTop : OrderTop EQuant where
  le_top a := by cases a <;> simp [LE.le, Top.top]

@[simp]
theorem EQuant.zero_le_del : (0 : EQuant) ≤ .del := by decide

@[simp]
theorem EQuant.one_le_del : (1 : EQuant) ≤ .del := by decide

@[simp]
theorem EQuant.one_le_copy : (1 : EQuant) ≤ .copy := by decide

@[simp]
theorem EQuant.one_le_coe {q : Quant} : (1 : EQuant) ≤ q := by simp [LE.le]

theorem EQuant.zero_le_coe_iff {q : Quant} : (0 : EQuant) ≤ q ↔ .del ≤ q := by simp [LE.le]

def EQuant.le.casesLE {motive : ∀{q q' : EQuant}, q ≤ q' → Sort _}
  (top : ∀q, motive (q := q) (q' := ⊤) (by simp))
  (zero : @motive 0 0 (by simp [LE.le]))
  (one : @motive 1 1 (by simp [LE.le]))
  (del : @motive .del .del (by simp [LE.le]))
  (copy : @motive .copy .copy (by simp [LE.le]))
  (zero_le_del : @motive 0 .del (by simp))
  (one_le_del : @motive 1 .del (by simp))
  (one_le_copy : @motive 1 .copy (by simp))
  : ∀{q q' : EQuant} (h : q ≤ q'), @motive q q' h
  | q, ⊤, _ => top q
  | 0, 0, _ => zero
  | 1, 1, _ => one
  | .del, .del, _ => del
  | .copy, .copy, _ => copy
  | 0, .del, _ => zero_le_del
  | 1, .del, _ => one_le_del
  | 1, .copy, _ => one_le_copy

@[elab_as_elim, cases_eliminator]
def EQuant.le.casesLE_all {motive : ∀{q q' : EQuant}, q ≤ q' → Sort _}
  (top_top : @motive ⊤ ⊤ (by simp))
  (copy_top : @motive .copy ⊤ (by simp))
  (del_top : @motive .del ⊤ (by simp))
  (one_top : @motive 1 ⊤ (by simp))
  (zero_top : @motive 0 ⊤ (by simp))
  (copy_copy : @motive .copy .copy (by simp [LE.le]))
  (one_copy : @motive 1 .copy (by simp [LE.le]))
  (del_del : @motive .del .del (by simp [LE.le]))
  (one_del : @motive 1 .del (by simp [LE.le]))
  (zero_del : @motive 0 .del (by simp))
  (one_one : @motive 1 1 (by simp [LE.le]))
  (zero_zero : @motive 0 0 (by simp [LE.le]))
  : ∀{q q' : EQuant} (h : q ≤ q'), @motive q q' h
  | ⊤, ⊤, _ => top_top
  | .copy, ⊤, _ => copy_top
  | .del, ⊤, _ => del_top
  | 1, ⊤, _ => one_top
  | 0, ⊤, _ => zero_top
  | .copy, .copy, _ => copy_copy
  | 1, .copy, _ => one_copy
  | .del, .del, _ => del_del
  | 1, .del, _ => one_del
  | 0, .del, _ => zero_del
  | 1, 1, _ => one_one
  | 0, 0, _ => zero_zero

theorem EQuant.le_refl (a : EQuant) : a ≤ a := by cases a <;> simp [LE.le]

@[simp]
theorem EQuant.not_zero_le_one : ¬(0 : EQuant) ≤ 1 := by simp [LE.le]

@[simp]
theorem EQuant.not_zero_le_copy : ¬(0 : EQuant) ≤ .copy := by simp [LE.le]

@[simp]
theorem EQuant.not_one_le_zero : ¬(1 : EQuant) ≤ 0 := by simp [LE.le]

@[simp]
theorem EQuant.not_copy_le_zero : ¬EQuant.copy ≤ 0 := by simp [LE.le]

@[simp]
theorem EQuant.not_copy_le_one : ¬EQuant.copy ≤ 1 := by simp [LE.le]

@[simp]
theorem EQuant.not_copy_le_del : ¬EQuant.copy ≤ .del := by simp [LE.le]

instance EQuant.instPartialOrder : PartialOrder EQuant where
  le_refl := le_refl
  le_trans a b c h h' := by cases h <;> cases h' <;> simp [le_refl]
  le_antisymm a b h h' := by cases h <;> cases h' <;> rfl

theorem EQuant.one_le_iff_ne_zero (q : EQuant) : 1 ≤ q ↔ q ≠ 0 := by cases q <;> decide

@[simp]
theorem EQuant.one_le_of_ne_zero {q : EQuant} (h : q ≠ 0) : 1 ≤ q
  := by rw [one_le_iff_ne_zero]; exact h

@[simp]
theorem EQuant.ne_zero_of_one_le {q : EQuant} (h : 1 ≤ q) : q ≠ 0
  := by rw [one_le_iff_ne_zero] at h; exact h

@[simp]
theorem EQuant.one_le_of_coe_le {q : Quant} {q' : EQuant} (h : q ≤ q') : 1 ≤ q'
  := le_trans one_le_coe h

instance EQuant.instMax : Max EQuant where
  max
  | (a : Quant), (b : Quant) => (a ⊔ b : Quant)
  | 0, .del | .del, 0 | 0, 1 | 1, 0 => .del
  | 0, 0 => 0
  | _, _ => ⊤

theorem EQuant.sup_top (a : EQuant) : a ⊔ ⊤ = ⊤ := by cases a <;> rfl

theorem EQuant.top_sup (a : EQuant) : ⊤ ⊔ a = ⊤ := by cases a <;> rfl

theorem EQuant.sup_self (a : EQuant) : a ⊔ a = a := by cases a <;> rfl

@[simp]
theorem EQuant.del_sup_copy : EQuant.del ⊔ .copy = ⊤ := by rfl

@[simp]
theorem EQuant.copy_sup_del : EQuant.copy ⊔ .del = ⊤ := by rfl

@[simp]
theorem EQuant.del_sup_one : EQuant.del ⊔ 1 = .del := by rfl

@[simp]
theorem EQuant.one_sup_del : 1 ⊔ EQuant.del = .del := by rfl

@[simp]
theorem EQuant.copy_sup_one : EQuant.copy ⊔ 1 = .copy := by rfl

@[simp]
theorem EQuant.one_sup_copy : 1 ⊔ EQuant.copy = .copy := by rfl

@[simp]
theorem EQuant.del_sup_zero : EQuant.del ⊔ 0 = .del := by rfl

@[simp]
theorem EQuant.zero_sup_del : 0 ⊔ EQuant.del = .del := by rfl

@[simp]
theorem EQuant.copy_sup_zero : EQuant.copy ⊔ 0 = ⊤ := by rfl

@[simp]
theorem EQuant.zero_sup_copy : 0 ⊔ EQuant.copy = ⊤ := by rfl

@[simp]
theorem EQuant.zero_sup_one : (0 : EQuant) ⊔ 1 = .del := by rfl

@[simp]
theorem EQuant.one_sup_zero : 1 ⊔ (0 : EQuant) = .del := by rfl

instance EQuant.instSemilatticeSup : SemilatticeSup EQuant where
  sup := (· ⊔ ·)
  le_sup_left a b := by cases a <;> cases b <;> decide
  le_sup_right a b := by cases a <;> cases b <;> decide
  sup_le a b c h h' := by cases h <;> cases h' <;> simp [sup_self]

def EQuant.ofUse : Bool → Quant → EQuant
  | false => 0
  | true => λq => q

instance EQuant.instAddCommMonoid : AddCommMonoid EQuant where
  -- NOTE: while 1 + .del would be .copy under set semantics, the resulting operation would not
  -- be associative, and therefore would be hard to assign semantics to!
  add
  | (l : Quant), (r : Quant) => (l + r : Quant)
  | 0, q | q, 0 => q
  add_assoc a b c := by cases a <;> cases b <;> cases c <;> rfl
  zero_add a := by cases a <;> rfl
  add_zero a := by cases a <;> rfl
  add_comm a b := by cases a <;> cases b <;> rfl
  nsmul
  | 0, q => 0
  | 1, q => q
  | n + 2, q => match q with | 0 => 0 | 1 | .copy => .copy | .del | ⊤ => ⊤
  nsmul_zero q := by cases q <;> rfl
  nsmul_succ n q := by cases n using Nat.cases2 <;> cases q <;> rfl

-- def EQuant.instAddZeroClass : AddZeroClass EQuant := inferInstance

theorem EQuant.coe_add {l r : Quant} : ((l + r : Quant) : EQuant) = (l : EQuant) + (r : EQuant)
  := by cases l <;> cases r <;> rfl

theorem EQuant.add_mono {l r l' r' : EQuant} (hl : l ≤ l') (hr : r ≤ r') : l + r ≤ l' + r' := by
  cases hl <;> cases hr <;> decide

theorem EQuant.coe_left_le_add {l : Quant} {r : EQuant} : l ≤ l + r
  := by cases l <;> cases r <;> decide

theorem EQuant.coe_right_le_add {l : EQuant} {r : Quant} : r ≤ l + r
  := by cases l <;> cases r <;> decide

theorem EQuant.left_le_add_of_ne_zero {l r : EQuant} (h : l ≠ 0) : l ≤ l + r
  := by cases l <;> simp at h <;> cases r <;> decide

theorem EQuant.right_le_add_of_ne_zero {l r : EQuant} (h : r ≠ 0) : r ≤ l + r
  := by cases l <;> cases r <;> simp at h <;> decide

def EQuant.toQ : EQuant → Quant
  | 0 => ⊥
  | (q : Quant) => q

theorem EQuant.toQ_mono {l r : EQuant} (h : l ≤ r) : l.toQ ≤ r.toQ := by cases h <;> decide

@[simp]
theorem EQuant.toQ_add_le {l r : EQuant} : (l + r).toQ ≤ l.toQ + r.toQ := by
  cases l <;> cases r <;> decide

@[simp]
theorem EQuant.left_toQ_le_add {l r : EQuant} : (l.toQ : EQuant) ≤ l.toQ + r := by
  cases l <;> cases r <;> decide

@[simp]
theorem EQuant.right_toQ_le_add {l r : EQuant} : (r.toQ : EQuant) ≤ l + r.toQ := by
  cases l <;> cases r <;> decide

@[simp]
theorem EQuant.left_toQ_le_toQ_add {l r : EQuant} : l.toQ ≤ (l + r).toQ := by
  cases l <;> cases r <;> decide

@[simp]
theorem EQuant.right_toQ_le_toQ_add {l r : EQuant} : r.toQ ≤ (l + r).toQ := by
  cases l <;> cases r <;> decide

@[simp]
theorem EQuant.left_toQ_le_toQ_add' {l r : EQuant} : (l.toQ : EQuant) ≤ (l + r).toQ := by
  cases l <;> cases r <;> decide

@[simp]
theorem EQuant.right_toQ_le_toQ_of_add' {l r : EQuant} : (r.toQ : EQuant) ≤ (l + r).toQ := by
  cases l <;> cases r <;> decide

instance EQuant.instCommSemiring : CommSemiring EQuant where
  mul
  | 0, _ | _, 0 => 0
  | (q : Quant) , (q' : Quant) => q * q'
  mul_assoc a b c := by cases a <;> cases b <;> cases c <;> rfl
  one := 1
  one_mul a := by cases a <;> rfl
  mul_one a := by cases a <;> rfl
  mul_comm a b := by cases a <;> cases b <;> rfl
  zero_mul a := by cases a <;> rfl
  mul_zero a := by cases a <;> rfl
  left_distrib a b c := by cases a <;> cases b <;> cases c <;> rfl
  right_distrib a b c := by cases a <;> cases b <;> cases c <;> rfl

instance EQuant.instOrderedAddCommMonoid : OrderedAddCommMonoid EQuant where
  add_le_add_left a b h c := by cases h <;> cases c <;> decide

theorem EQuant.zero_le_add {l r : EQuant} (hl : 0 ≤ l) (hr : 0 ≤ r) : 0 ≤ l + r := by
  cases hl <;> cases hr <;> decide

theorem EQuant.one_le_add_left {l r : EQuant} (h : 1 ≤ l) : 1 ≤ l + r := by
  cases h <;> cases r <;> decide

theorem EQuant.one_le_add_right {l r : EQuant} (h : 1 ≤ r) : 1 ≤ l + r := by
  cases l <;> cases h <;> decide

theorem EQuant.zero_le_add_or {l r : EQuant} (h : 0 ≤ l + r) : 0 ≤ l ∨ 0 ≤ r := by
  cases l <;> cases r <;> cases h <;> decide

theorem EQuant.one_le_add_or {l r : EQuant} (h : 1 ≤ l + r) : 1 ≤ l ∨ 1 ≤ r := by
  cases l <;> cases r <;> cases h <;> decide

theorem EQuant.one_le_add_iff {l r : EQuant} : 1 ≤ l + r ↔ 1 ≤ l ∨ 1 ≤ r := ⟨
  one_le_add_or,
  λ| .inl h => one_le_add_left h | .inr h => one_le_add_right h
  ⟩

theorem EQuant.add_le_zero {l r : EQuant} (h : l + r ≤ 0) : l = 0 ∧ r = 0 := by
  cases l <;> cases r <;> cases h; decide

theorem EQuant.add_le_zero_iff {l r : EQuant} : l + r ≤ 0 ↔ l = 0 ∧ r = 0
  := ⟨add_le_zero, λh => by cases h.1; cases h.2; rfl⟩

@[simp]
theorem EQuant.copy_le_of_add_coe_le {l r : Quant} {q : EQuant} (h : l + r ≤ q)
  : .copy ≤ q := by cases l <;> cases r <;> cases h <;> decide

@[simp]
theorem EQuant.add_idem_of_copy_le {q : EQuant} (h : .copy ≤ q) : q + q = q := by
  cases h <;> decide

@[simp]
theorem EQuant.add_idem_of_add_coe_le {l r : Quant} {q : EQuant} (h : l + r ≤ q)
  : q + q = q := add_idem_of_copy_le (copy_le_of_add_coe_le h)

theorem EQuant.coe_mul {l r : Quant} : ((l * r : Quant) : EQuant) = (l : EQuant) * (r : EQuant)
  := rfl

-- def EQuant.toMQ : EQuant → Quant
--   | 0 => .del
--   | (q : Quant) => q

-- theorem EQuant.toMQ_mono {l r : EQuant} (h : l ≤ r) : l.toMQ ≤ r.toMQ
--   := by cases h <;> decide

-- theorem EQuant.toMQ_le_coe {l : EQuant} {r : Quant} (h : l ≤ r) : l.toMQ ≤ r
--   := by cases h <;> decide

-- @[simp]
-- theorem EQuant.toMQ_add_le {l r : EQuant} : (l + r).toMQ ≤ l.toMQ + r.toMQ := by
--   cases l <;> cases r <;> decide

-- @[simp]
-- theorem EQuant.toMQ_mul_toMQ_le {l r : EQuant} : l.toMQ * r.toMQ ≤ (l + r).toMQ := by
--   cases l <;> cases r <;> decide

-- @[simp]
-- theorem EQuant.toMQ_left_le_add {l r : EQuant} : (l.toMQ : EQuant) ≤ l.toMQ + r := by
--   cases l <;> cases r <;> decide

-- @[simp]
-- theorem EQuant.toMQ_right_le_add {l r : EQuant} : (r.toMQ : EQuant) ≤ l + r.toMQ := by
--   cases l <;> cases r <;> decide

def Vector'.toQE {n} (qs : Vector' EQuant n) : Vector' EQuant n := qs.map (λq => q.toQ)

@[simp]
theorem Vector'.toQE_nil : Vector'.toQE nil = nil := rfl

@[simp]
theorem Vector'.toQE_cons (q : EQuant) (qs : Vector' EQuant n)
  : Vector'.toQE (qs.cons q) = qs.toQE.cons ↑q.toQ := rfl

@[simp]
theorem Vector'.toQE_left_le_add {l r : Vector' EQuant n} : l.toQE ≤ l.toQE + r
  := by induction l <;> cases r <;> simp [*]

@[simp]
theorem Vector'.toQE_right_le_add {l r : Vector' EQuant n} : r.toQE ≤ l + r.toQE
  := by induction l <;> cases r <;> simp [*]

@[simp]
theorem Vector'.toQE_left_le_toQE_add {l r : Vector' EQuant n} : l.toQE ≤ (l + r).toQE
  := by induction l <;> cases r <;> simp [*]

@[simp]
theorem Vector'.toQE_right_le_toQE_add {l r : Vector' EQuant n} : r.toQE ≤ (l + r).toQE
  := by induction l <;> cases r <;> simp [*]

-- def Vector'.toMQE (qs : Vector' EQuant n) : Vector' EQuant n := qs.map (λq => q.toMQ)

-- @[simp]
-- theorem Vector'.toMQE_nil : Vector'.toMQE nil = nil := rfl

-- @[simp]
-- theorem Vector'.toMQE_cons (q : EQuant) (qs : Vector' EQuant n)
--   : Vector'.toMQE (qs.cons q) = qs.toMQE.cons ↑q.toMQ := rfl

-- @[simp]
-- theorem Vector'.toMQE_left_le_add {l r : Vector' EQuant n} : l.toMQE ≤ l.toMQE + r
--   := by induction l <;> cases r <;> simp [*]

-- @[simp]
-- theorem Vector'.toMQE_right_le_add {l r : Vector' EQuant n} : r.toMQE ≤ l + r.toMQE
--   := by induction l <;> cases r <;> simp [*]

def EQuant.c : EQuant → Set ℕ
  | 0 => {0}
  | (q : Quant) => q.c

@[simp]
theorem EQuant.c_zero : EQuant.c 0 = {0} := rfl

@[simp]
theorem EQuant.c_coe {q : Quant} : EQuant.c q = q.c := rfl

@[simp]
theorem EQuant.c_one : EQuant.c 1 = {1} := by rw [one_def, c_coe]; simp

@[simp]
theorem EQuant.c_copy : EQuant.c .copy = Set.Ici 1 := by simp [EQuant.copy]

@[simp]
theorem EQuant.c_del : EQuant.c .del = {0, 1} := by simp [EQuant.del]

@[simp]
theorem EQuant.c_top : EQuant.c ⊤ = Set.univ := by simp [<-EQuant.coe_top]

theorem EQuant.c_mono {l r : EQuant} (h : l ≤ r) : l.c ⊆ r.c := by
  cases h <;> simp

theorem EQuant.zero_mem_c_iff {q : EQuant} : 0 ∈ q.c ↔ 0 ≤ q := by cases q <;> simp [c]

theorem EQuant.one_mem_c_iff {q : EQuant} : 1 ∈ q.c ↔ 1 ≤ q := by cases q <;> simp [c]

theorem EQuant.n_plus_two_mem_c_iff {q : EQuant} {n} : n + 2 ∈ q.c ↔ .copy ≤ q
  := by cases q <;> simp [c]

theorem EQuant.two_mem_c_iff {q : EQuant} : 2 ∈ q.c ↔ .copy ≤ q := n_plus_two_mem_c_iff

theorem EQuant.c_add {l r : EQuant} : (c l) + (c r) ⊆ c (l + r) := λn ⟨x, hx, y, hy, hxy⟩ => by
  induction l <;> induction r <;> simp at *
  case rest.rest => rw [<-coe_add]; apply Quant.c_add; assumption
  all_goals simp [*]

theorem EQuant.c_mul {l r : EQuant} : (l * r).c = (l.c) * (r.c) := by
  cases l using casesOn' with
  | zero => cases r <;> simp
  | coe l => cases r using casesOn' with
    | zero => cases l <;> simp
    | coe r => simp [<-coe_mul, Quant.c_mul]

def Quant0 := EQuant

instance Quant0.instZero : Zero Quant0 := EQuant.instZero

instance Quant0.instOne : One Quant0 := EQuant.instOne

instance Quant0.instCoeTCQuant : CoeTC Quant Quant0 := EQuant.instCoeTC

instance Quant0.instDecidableEq : DecidableEq Quant0 := EQuant.instDecidableEq

instance Quant0.instLE : LE Quant0 where
  le
  | 0, _ => True
  | (_ : Quant), 0 => False
  | (a : Quant), (b : Quant) => a ≤ b

instance Quant0.instDecidableLE : DecidableRel (· ≤ · : Quant0 → Quant0 → Prop)
  | 0, a => Decidable.isTrue (by simp [LE.le])
  | (a : Quant), 0 => Decidable.isFalse (by simp [LE.le])
  | (a : Quant), (b : Quant) => (inferInstance : Decidable (a ≤ b))

theorem Quant0.le.of_equant {l r : EQuant} (h : l ≤ r) : Quant0.instLE.le l r
  := by cases h <;> decide

instance Quant0.instOrderTop : OrderTop Quant0 where
  top := (⊤ : EQuant)
  le_top a := by cases a <;> simp [LE.le, Top.top]

instance Quant0.instOrderBot : OrderBot Quant0 where
  bot := (0 : EQuant)
  bot_le a := by cases a <;> simp [LE.le]

@[match_pattern]
def Quant0.copy : Quant0 := EQuant.copy

@[match_pattern]
def Quant0.del : Quant0 := EQuant.del

@[elab_as_elim, cases_eliminator]
def Quant0.casesOn {motive : Quant0 → Sort _}
  (zero : motive 0)
  (one : motive 1)
  (copy : motive .copy)
  (del : motive .del)
  (top : motive ⊤)
  : ∀(q : Quant0), motive q
  := EQuant.casesOn zero one copy del top

@[elab_as_elim, cases_eliminator]
def Quant0.le.casesOn {motive : ∀{q q' : Quant0}, q ≤ q' → Sort _}
  (top_le_top : @motive ⊤ ⊤ (by decide))
  (copy_le_top : @motive .copy ⊤ (by decide))
  (del_le_top : @motive .del ⊤ (by decide))
  (one_le_top : @motive 1 ⊤ (by decide))
  (zero_le_top : @motive 0 ⊤ (by decide))
  (copy_le_copy : @motive .copy .copy (by decide))
  (one_le_copy : @motive 1 .copy (by decide))
  (zero_le_copy : @motive 0 .copy (by decide))
  (del_le_del : @motive .del .del (by decide))
  (one_le_del : @motive 1 .del (by decide))
  (zero_le_del : @motive 0 .del (by decide))
  (one_le_one : @motive 1 1 (by decide))
  (zero_le_one : @motive 0 1 (by decide))
  (zero_le_zero : @motive 0 0 (by decide))
  : ∀{q q' : Quant0} (h : q ≤ q'), @motive q q' h
  | ⊤, ⊤, _ => top_le_top
  | .copy, ⊤, _ => copy_le_top
  | .del, ⊤, _ => del_le_top
  | 1, ⊤, _ => one_le_top
  | 0, ⊤, _ => zero_le_top
  | .copy, .copy, _ => copy_le_copy
  | 1, .copy, _ => one_le_copy
  | 0, .copy, _ => zero_le_copy
  | .del, .del, _ => del_le_del
  | 1, .del, _ => one_le_del
  | 0, .del, _ => zero_le_del
  | 1, 1, _ => one_le_one
  | 0, 1, _ => zero_le_one
  | 0, 0, _ => zero_le_zero

@[elab_as_elim, induction_eliminator]
def Quant0.le.inductionOn {motive : ∀{q q' : Quant0}, q ≤ q' → Sort _}
  (zero_le_one : @motive 0 1 (by decide))
  (zero_le_copy : @motive 0 .copy (by decide))
  (rest : ∀{q q' : EQuant}, (h : q ≤ q') -> @motive q q' (Quant0.le.of_equant h))
  : ∀{q q' : Quant0} (h : q ≤ q'), @motive q q' h
  | ⊤, ⊤, _ => rest (by decide)
  | .copy, ⊤, _ => rest (by decide)
  | .del, ⊤, _ => rest (by decide)
  | 1, ⊤, _ => rest (by decide)
  | 0, ⊤, _ => rest (by decide)
  | .copy, .copy, _ => rest (by decide)
  | 1, .copy, _ => rest (by decide)
  | 0, .copy, _ => zero_le_copy
  | .del, .del, _ => rest (by decide)
  | 1, .del, _ => rest (by decide)
  | 0, .del, _ => rest (by decide)
  | 1, 1, _ => rest (by decide)
  | 0, 1, _ => zero_le_one
  | 0, 0, _ => rest (by decide)

instance Quant0.instPartialOrder : PartialOrder Quant0 where
  le_refl a := by cases a <;> decide
  le_trans a b c hab hbc := by cases hab <;> cases hbc <;> decide
  le_antisymm a b hab hbc := by cases hab <;> cases hbc <;> rfl

instance Quant0.instFintype : Fintype Quant0 := EQuant.instFintype

instance Quant0.instCommSemiring : CommSemiring Quant0 := EQuant.instCommSemiring

instance Quant0.instOrderedCommSemiring : OrderedCommSemiring Quant0 where
  add_le_add_left a b h c := by cases h <;> cases c <;> decide
  zero_le_one := by decide
  mul_le_mul_of_nonneg_left a b c h h' := by cases h <;> cases c <;> decide
  mul_comm := mul_comm

def Quant? := WithBot EQuant

@[coe, match_pattern]
def Quant?.some : EQuant → Quant? := WithBot.some

instance Quant?.instCoeTC : CoeTC EQuant Quant? := ⟨Quant?.some⟩

@[coe, match_pattern]
def Quant?.nz : Quant → Quant? := λq => (q : EQuant)

instance Quant?.instCoeTC' : CoeTC Quant Quant? := ⟨Quant?.nz⟩

instance Quant?.instZero : Zero Quant? := ⟨(0 : EQuant)⟩

instance Quant?.instOne : One Quant? := ⟨(1 : EQuant)⟩

theorem Quant?.zero_def : (0 : Quant?) = (0 : EQuant) := rfl

theorem Quant?.one_def : (1 : Quant?) = (1 : EQuant) := rfl

-- TODO: mathlib should be able to infer fintype for {WithBot, WithTop, and friends}
-- Make PR?
instance Quant?.instFintype : Fintype Quant? := (inferInstance : Fintype (Option EQuant))

instance Quant?.instPartialOrder : PartialOrder Quant?
  := (inferInstance : PartialOrder (WithBot EQuant))

instance Quant?.instBoundedOrder : BoundedOrder Quant?
  := (inferInstance : BoundedOrder (WithBot EQuant))

theorem Quant?.top_def : (⊤ : Quant?) = (⊤ : EQuant) := rfl

instance Quant?.instMax : Max Quant? := (inferInstance : Max (WithBot EQuant))

instance Quant?.instSemilatticeSup : SemilatticeSup Quant?
  := (inferInstance : SemilatticeSup (WithBot EQuant))

instance Quant?.instDecidableEq : DecidableEq Quant?
  := (inferInstance : DecidableEq (WithBot EQuant))

instance Quant?.instDecidableLE : DecidableRel (· ≤ · : Quant? → Quant? → Prop)
  := (inferInstance : DecidableRel (· ≤ · : WithBot EQuant → WithBot EQuant → Prop))

@[match_pattern]
def Quant?.copy : Quant? := Quant.copy

@[match_pattern]
def Quant?.del : Quant? := Quant.del

@[simp]
theorem Quant?.coe_le_coe {l r : EQuant} : (l : Quant?) ≤ r ↔ l ≤ r
  := WithBot.coe_le_coe (a := l) (b := r)

theorem Quant?.coe_quant_def {q : Quant} : (q : Quant?) = (q : EQuant) := rfl

@[simp]
theorem Quant?.coe_quant_le_coe {q : Quant} {q' : EQuant} : (q : Quant?) ≤ q' ↔ q ≤ q'
  := by simp [Quant?.coe_quant_def]

@[simp]
theorem Quant?.coe_le_coe_quant {q : EQuant} {q' : Quant} : (q : Quant?) ≤ q' ↔ q ≤ q'
  := by simp [Quant?.coe_quant_def]

@[simp]
theorem Quant?.coe_quant_le_coe_quant {l r : Quant} : (l : Quant?) ≤ r ↔ l ≤ r
  := by simp [coe_quant_def]

@[simp]
theorem Quant?.zero_le_del : (0 : Quant?) ≤ .del := by decide

@[simp]
theorem Quant?.one_le_del : (1 : Quant?) ≤ .del := by decide

@[simp]
theorem Quant?.not_zero_le_one : ¬(0 : Quant?) ≤ 1 := by decide

@[simp]
theorem Quant?.not_one_le_zero : ¬(1 : Quant?) ≤ 0 := by decide

@[simp]
theorem Quant?.not_zero_le_copy : ¬(0 : Quant?) ≤ .copy := by decide

@[simp]
theorem Quant?.not_copy_le_zero : ¬Quant?.copy ≤ 0 := by decide

@[elab_as_elim, cases_eliminator]
def Quant?.casesOn {motive : Quant? → Sort _}
  (top : motive ⊤)
  (zero : motive 0)
  (one : motive 1)
  (copy : motive .copy)
  (del : motive .del)
  (bot : motive ⊥)
  : ∀(q : Quant?), motive q
  | ⊤ => top
  | 0 => zero
  | 1 => one
  | .copy => copy
  | .del => del
  | ⊥ => bot

@[elab_as_elim, induction_eliminator]
def Quant.casesBot {motive : Quant? → Sort _}
  (bot : motive ⊥)
  (rest : ∀q : EQuant, motive q)
  : ∀(q : Quant?), motive q
  | ⊥ => bot
  | (q : EQuant) => rest q

instance Quant?.instLattice : Lattice Quant? where
  inf
  | .nz a, .nz b => (a ⊓ b : Quant)
  | 0, 0 | 0, .del | .del, 0 | 0, ⊤ | ⊤, 0 => 0
  | _, _ => ⊥
  inf_le_left a b := by cases a <;> cases b <;> decide
  inf_le_right a b := by cases a <;> cases b <;> decide
  le_inf a b c := by cases a <;> cases b <;> cases c <;> decide

@[simp]
theorem Quant?.copy_inf_del : Quant?.copy ⊓ .del = 1 := rfl

@[simp]
theorem Quant?.del_inf_copy : Quant?.del ⊓ .copy = 1 := rfl

@[simp]
theorem Quant?.one_inf_copy : (1 : Quant?) ⊓ .copy = 1 := rfl

@[simp]
theorem Quant?.copy_inf_one : Quant?.copy ⊓ 1 = 1 := rfl

@[simp]
theorem Quant?.one_inf_del : (1 : Quant?) ⊓ .del = 1 := rfl

@[simp]
theorem Quant?.del_inf_one : Quant?.del ⊓ 1 = 1 := rfl

@[simp]
theorem Quant?.zero_inf_one : (0 : Quant?) ⊓ 1 = ⊥ := rfl

@[simp]
theorem Quant?.one_inf_zero : (1 : Quant?) ⊓ 0 = ⊥ := rfl

@[simp]
theorem Quant?.zero_inf_copy : (0 : Quant?) ⊓ .copy = ⊥ := rfl

@[simp]
theorem Quant?.copy_inf_zero : Quant?.copy ⊓ 0 = ⊥ := rfl

@[simp]
theorem Quant?.zero_inf_del : (0 : Quant?) ⊓ .del = 0 := rfl

@[simp]
theorem Quant?.del_inf_zero : Quant?.del ⊓ 0 = 0 := rfl

def Quant?.c : Quant? → Set ℕ
  | ⊥ => ∅
  | (q : EQuant) => q.c

@[simp]
theorem Quant?.c_bot : Quant?.c ⊥ = ∅ := rfl

@[simp]
theorem Quant?.c_coe {q : EQuant} : Quant?.c q = q.c := rfl

@[simp]
theorem Quant?.c_coe_quant {q : Quant} : Quant?.c q = q.c := rfl

@[simp]
theorem Quant?.c_copy : Quant?.c .copy = Set.Ici 1 := by simp [Quant?.copy]

@[simp]
theorem Quant?.c_del : Quant?.c .del = {0, 1} := by simp [Quant?.del]

@[simp]
theorem Quant?.c_one : Quant?.c 1 = {1} := by simp [one_def]

@[simp]
theorem Quant?.c_zero : Quant?.c 0 = {0} := by simp [zero_def]

@[simp]
theorem Quant?.c_top : Quant?.c ⊤ = Set.univ := by simp [top_def]

theorem Quant?.zero_mem_c_iff {q : Quant?} : 0 ∈ q.c ↔ 0 ≤ q := by cases q <;> simp [c]; decide

theorem Quant?.one_mem_c_iff {q : Quant?} : 1 ∈ q.c ↔ 1 ≤ q := by cases q <;> simp [c] <;> decide

theorem Quant?.n_plus_two_mem_c_iff {q : Quant?} {n} : n + 2 ∈ q.c ↔ .copy ≤ q
  := by cases q <;> simp [c] <;> decide

theorem Quant?.two_mem_c_iff {q : Quant?} : 2 ∈ q.c ↔ .copy ≤ q := n_plus_two_mem_c_iff

theorem Quant?.c_mono {l r : Quant?} : l ≤ r → l.c ⊆ r.c := by induction l with
  | bot => simp
  | rest l => induction r with
  | bot =>
    simp only [le_bot_iff, c_coe, c_bot, Set.subset_empty_iff]
    intro h; cases h
  | rest r => simp only [coe_le_coe, c_coe]; apply EQuant.c_mono


instance Quant?.instAdd : Add Quant? where
  -- NOTE: while 1 + .del would be .copy under set semantics, the resulting operation would not
  -- be associative, and therefore would be hard to assign semantics to!
  add
  | (l : EQuant), (r : EQuant) => (l + r : EQuant)
  | _, _ => ⊥

@[simp]
theorem Quant?.add_bot {q : Quant?} : q + ⊥ = ⊥ := by cases q <;> rfl

@[simp]
theorem Quant?.bot_add {q : Quant?} : ⊥ + q = ⊥ := by cases q <;> rfl

theorem Quant?.coe_add {l r : EQuant} : (l + r : EQuant) = (l : Quant?) + (r : Quant?) := rfl

instance Quant?.instAddCommMonoid : AddCommMonoid Quant? where
  add
  | (l : EQuant), (r : EQuant) => (l + r : EQuant)
  | _, _ => ⊥
  add_assoc a b c := by
    induction a <;> induction b <;> induction c
    case rest.rest.rest => simp [<-coe_add, add_assoc]
    all_goals simp only [add_bot, bot_add]
  zero_add a := by induction a; rfl; simp [zero_def, <-coe_add]
  add_zero a := by induction a; rfl; simp [zero_def, <-coe_add]
  add_comm a b := by induction a <;> induction b <;> simp [<-coe_add, add_comm]
  nsmul
    | n, (q : EQuant) => (n • q : EQuant)
    | 0, ⊥ => 0
    | n + 1, ⊥ => ⊥
  nsmul_zero a := by induction a <;> rfl
  nsmul_succ n a := by induction a with
    | rest a => cases n using Nat.cases2 <;> cases a <;> rfl
    | bot => cases n <;> rfl

theorem Quant?.add_mono {l r l' r' : Quant?} (hl : l ≤ l') (hr : r ≤ r') : l + r ≤ l' + r' := by
  induction l with
  | bot => simp
  | rest => induction r with
  | bot => simp
  | rest => induction l' with
  | bot => simp at hl; simp [hl]
  | rest => induction r' with
  | bot => simp at hr; simp [hr]
  | rest =>
    simp only [coe_le_coe, ←coe_add] at *
    apply EQuant.add_mono <;> assumption

theorem Quant?.c_add {l r : Quant?} : (c l) + (c r) ⊆ c (l + r) := by
  induction l with
  | bot => simp
  | rest => induction r with
  | bot => simp
  | rest => simp [<-coe_add, EQuant.c_add]

inductive Polarity : Type
  | pos
  | neg
  deriving DecidableEq

instance Polarity.instFintype : Fintype Polarity where
  elems := {Polarity.pos, Polarity.neg}
  complete x := by cases x <;> simp

instance Polarity.instNeg : Neg Polarity where
  neg | .pos => .neg | .neg => .pos

@[simp]
theorem Polarity.neg_pos : -Polarity.pos = Polarity.neg := rfl

@[simp]
theorem Polarity.neg_neg : -Polarity.neg = Polarity.pos := rfl

@[simp]
theorem Polarity.neg_idem (p : Polarity) : -(-p) = p := by cases p <;> rfl

instance Polarity.instMul : Mul Polarity where
  mul | .pos, p => p | .neg, p => -p

@[simp]
theorem Polarity.pos_mul : Polarity.pos * p = p := by cases p <;> rfl

@[simp]
theorem Polarity.neg_mul : Polarity.neg * p = -p := by cases p <;> rfl

@[simp]
theorem Polarity.mul_pos : p * Polarity.pos = p := by cases p <;> rfl

@[simp]
theorem Polarity.mul_neg : p * Polarity.neg = -p := by cases p <;> rfl

@[simp]
theorem Polarity.mul_neg_self (p : Polarity) : p * -p = Polarity.neg := by cases p <;> rfl

@[simp]
theorem Polarity.neg_self_mul (p : Polarity) : -p * p = Polarity.neg := by cases p <;> rfl

@[simp]
theorem Polarity.neg_mul_neg (p : Polarity) : -p * -p = Polarity.pos := by cases p <;> rfl

@[simp]
theorem Polarity.self_mul_self (p : Polarity) : p * p = Polarity.pos := by cases p <;> rfl

instance Polarity.instCommMonoid : CommMonoid Polarity where
  one := Polarity.pos
  one_mul p := by cases p <;> rfl
  mul_one p := by cases p <;> rfl
  mul_assoc p q r := by cases p <;> cases q <;> cases r <;> rfl
  mul_comm p q := by cases p <;> cases q <;> rfl

def Polarities := Bool × Bool

instance Polarities.instDecidableEq : DecidableEq Polarities
  := (inferInstance : DecidableEq (Bool × Bool))

instance Polarities.instLattice : Lattice Polarities
  := (inferInstance : Lattice (Bool × Bool))

instance Polarities.instBoundedOrder : BoundedOrder Polarities
  := (inferInstance : BoundedOrder (Bool × Bool))

@[match_pattern]
def Polarities.pos : Polarities := (true, false)

@[match_pattern]
def Polarities.neg : Polarities := (false, true)

instance Polarities.coePolarity : Coe Polarity Polarities
  := ⟨λp => match p with | Polarity.pos => Polarities.pos | Polarity.neg => Polarities.neg⟩

instance Polarities.instFintype : Fintype Polarities := (inferInstance : Fintype (Bool × Bool))

@[elab_as_elim, cases_eliminator]
def Polarities.casesOn {motive : Polarities → Sort _}
  (top : motive ⊤)
  (pos : motive Polarities.pos)
  (neg : motive Polarities.neg)
  (bot : motive ⊥)
  : ∀(p : Polarities), motive p
  | ⊤ => top
  | .pos => pos
  | .neg => neg
  | ⊥ => bot

instance Polarities.instNeg : Neg Polarities where
  neg p := (p.2, p.1)

@[simp]
theorem Polarities.neg_top : -(⊤ : Polarities) = ⊤ := rfl

@[simp]
theorem Polarities.neg_bot : -(⊥ : Polarities) = ⊥ := rfl

@[simp]
theorem Polarities.neg_pos : -Polarities.pos = Polarities.neg := rfl

@[simp]
theorem Polarities.neg_neg : -Polarities.neg = Polarities.pos := rfl

@[simp]
theorem Polarities.neg_idem (p : Polarities) : -(-p) = p := by cases p <;> rfl

@[simp]
theorem Polarities.neg_inf (p q : Polarities) : -(p ⊓ q) = -p ⊓ -q := by cases p <;> cases q <;> rfl

@[simp]
theorem Polarities.neg_sup (p q : Polarities) : -(p ⊔ q) = -p ⊔ -q := by cases p <;> cases q <;> rfl

instance Polarities.instHNot : HNot Polarities where
  hnot p := (¬p.1, ¬p.2)

@[simp]
theorem Polarities.hnot_top : ￢(⊤ : Polarities) = ⊥ := rfl

@[simp]
theorem Polarities.hnot_bot : ￢(⊥ : Polarities) = ⊤ := rfl

@[simp]
theorem Polarities.hnot_pos : ￢Polarities.pos = Polarities.neg := rfl

@[simp]
theorem Polarities.hnot_neg : ￢Polarities.neg = Polarities.pos := rfl

instance Polarities.instMembership : Membership Polarity Polarities where
  mem p | .pos => p.1 | .neg => p.2

theorem Polarities.pos_mem_iff {p : Polarities} : Polarity.pos ∈ p ↔ p.1 = true
  := by cases p <;> rfl

theorem Polarities.neg_mem_iff {p : Polarities} : Polarity.neg ∈ p ↔ p.2 = true
  := by cases p <;> rfl

instance Polarities.decidableMembership {ps : Polarities} : DecidablePred (· ∈ ps)
  := λ | .pos => (inferInstance : Decidable (ps.1 = true))
       | .neg => (inferInstance : Decidable (ps.2 = true))

theorem Polarities.eta_mem (p : Polarities) : p = ((.pos ∈ p : Bool), (.neg ∈ p : Bool))
  := by cases p <;> decide

theorem Polarities.ext_mem {p q : Polarities} (h : ∀r, r ∈ p ↔ r ∈ q) : p = q := by
  rw [p.eta_mem, q.eta_mem]
  simp [h]

theorem Polarities.ext_mem_iff {p q : Polarities} : (∀r, r ∈ p ↔ r ∈ q) ↔ p = q
  := ⟨ext_mem, λh => by simp [h]⟩

instance Polarities.instDecidableLE : DecidableRel (· ≤ · : Polarities → Polarities → Prop)
  := (inferInstance : DecidableRel (· ≤ · : Bool × Bool → Bool × Bool → Prop))

@[simp]
theorem Polarities.neg_le_iff (p q : Polarities) : -p ≤ -q ↔ p ≤ q
  := by cases p <;> cases q <;> decide

-- TODO: mem is an isomorphism

def PQuant : Type := Quant × Quant

instance PQuant.instMax : Max PQuant := (inferInstance : Max (Quant × Quant))

instance PQuant.instBooleanAlgebra : BooleanAlgebra PQuant
  := (inferInstance : BooleanAlgebra (Quant × Quant))

instance PQuant.instDecidableEq : DecidableEq PQuant
  := (inferInstance : DecidableEq (Quant × Quant))

instance PQuant.instDecidableRel : DecidableRel (· ≤ · : PQuant → PQuant → Prop)
  := (inferInstance : DecidableRel (· ≤ · : Quant × Quant → Quant × Quant → Prop))

instance PQuant.instCoe : Coe Quant PQuant := ⟨λq => (q, q)⟩

instance PQuant.instOne : One PQuant := ⟨(1 : Quant)⟩

theorem PQuant.coe_mono {l r : Quant} : l ≤ r → (l : PQuant) ≤ (r : PQuant) := λh => ⟨h, h⟩

theorem PQuant.coe_le_coe {l r : Quant} : (l : PQuant) ≤ (r : PQuant) ↔ l ≤ r := by simp

def PQuant.dup : PQuant := ⟨Quant.copy, 1⟩

def PQuant.fuse : PQuant := ⟨1, Quant.copy⟩

def PQuant.rem : PQuant := ⟨Quant.del, 1⟩

def PQuant.add : PQuant := ⟨1, Quant.del⟩

def PQuant.copy : PQuant := Quant.copy

def PQuant.del : PQuant := Quant.del

@[simp]
theorem PQuant.coe_top : ((⊤ : Quant) : PQuant) = ⊤ := rfl

@[simp]
theorem PQuant.coe_bot : ((⊥ : Quant) : PQuant) = ⊥ := rfl

@[simp]
theorem PQuant.coe_one : ((1 : Quant) : PQuant) = 1 := rfl

@[simp]
theorem PQuant.coe_del : (Quant.del : PQuant) = PQuant.del := rfl

@[simp]
theorem PQuant.coe_copy : (Quant.copy : PQuant) = PQuant.copy := rfl

-- TODO: coercion is a lattice embedding

abbrev PQuant.pos (q : PQuant) : Quant := q.1

abbrev PQuant.neg (q : PQuant) : Quant := q.2

def PQuant.pq (q : PQuant) : Polarity → Quant | .pos => q.pos | .neg => q.neg

def PQuant.qp (pq : PQuant) (q : Quant) : Polarities := (q ≤ pq.pos, q ≤ pq.neg)

@[simp]
theorem PQuant.qp_one (pq : PQuant) : pq.qp 1 = ⊤ := rfl

@[simp]
theorem PQuant.qp_bot (pq : PQuant) : pq.qp ⊥ = ⊤ := rfl

theorem PQuant.qp_anti_quant (pq : PQuant) {q q' : Quant} : q ≤ q' → pq.qp q' ≤ pq.qp q := by
  cases pq with | mk l r => cases l <;> cases r <;> cases q <;> cases q' <;> decide

theorem PQuant.qp_mono_pquant {pq pq' : PQuant} (q : Quant) : pq ≤ pq' → pq.qp q ≤ pq'.qp q
  := by cases pq with | mk l r => cases pq' with | mk l' r' =>
    cases l <;> cases r <;> cases l' <;> cases r' <;> cases q <;> decide

def PQuant.dc (q : PQuant) : Set (Polarity × DupCap) := {d | d.2 ∈ (q.pq d.1).dc}

-- TODO: pq and dc are lattice isomorphisms

def PQuant.q (q : PQuant) : Quant := q.1 ⊓ q.2

@[simp]
theorem PQuant.q_coe (q : Quant) : PQuant.q q = q := by cases q <;> rfl

theorem PQuant.q_le : (q : PQuant)  → q.q ≤ q | ⟨l, r⟩ => by cases l <;> cases r <;> decide

def PQuant.c (q : PQuant) : Set ℕ := q.q.c

@[simp]
theorem PQuant.c_coe (q : Quant) : PQuant.c q = q.c := by simp [c]

@[simp]
theorem PQuant.dup_le_copy : PQuant.dup ≤ PQuant.copy := by decide

@[simp]
theorem PQuant.fuse_le_copy : PQuant.fuse ≤ PQuant.copy := by decide

@[simp]
theorem PQuant.dup_sup_fuse : PQuant.dup ⊔ PQuant.fuse = PQuant.copy := by decide

@[simp]
theorem PQuant.fuse_sup_dup : PQuant.fuse ⊔ PQuant.dup = PQuant.copy := by decide

@[simp]
theorem PQuant.rem_le_del : PQuant.rem ≤ PQuant.del := by decide

@[simp]
theorem PQuant.add_le_del : PQuant.add ≤ PQuant.del := by decide

@[simp]
theorem PQuant.rem_sup_add : PQuant.rem ⊔ PQuant.add = PQuant.del := by decide

@[simp]
theorem PQuant.add_sup_rem : PQuant.add ⊔ PQuant.rem = PQuant.del := by decide

instance PQuant.instFintype : Fintype PQuant := (inferInstance : Fintype (Quant × Quant))

class Polar (ε : Type u) [LE ε] [Bot ε] : Sort _ where
  polarity : ε → ε → Polarities
  neg_polarity : ∀l r, -polarity l r = polarity r l
  bot_polarity : ∀e, polarity ⊥ e = ⊤
  polarity_anti_right : ∀l lo hi, lo ≤ hi → polarity l hi ≤ polarity l lo

open Polar

theorem Polar.polarity_anti_left {ε} [LE ε] [Bot ε] [Polar ε] (r lo hi : ε) (h : hi ≤ lo)
  : polarity lo r ≤ polarity hi r := by
  rw [<-neg_polarity r lo, <-neg_polarity r hi, Polarities.neg_le_iff]
  apply polarity_anti_right _ _ _ h

instance Unit.instPolar : Polar Unit where
  polarity _ _ := ⊤
  neg_polarity _ _ := rfl
  bot_polarity _ := rfl
  polarity_anti_right := by intros; rfl

instance Quant.instPolar : Polar Quant where
  polarity _ _ := ⊤
  neg_polarity _ _ := rfl
  bot_polarity _ := rfl
  polarity_anti_right := by intros; rfl

instance PQuant.instPolar : Polar PQuant where
  polarity _ _ := ⊤
  neg_polarity _ _ := rfl
  bot_polarity _ := rfl
  polarity_anti_right := by intros; rfl

instance WithTop.instPolar {ε} [PartialOrder ε] [OrderBot ε] [DecidableEq ε] [Polar ε]
  : Polar (WithTop ε) where
  polarity
  | ⊤, e | e, ⊤ => if e = ⊥ then ⊤ else ⊥
  | (l : ε), (r : ε) => polarity l r
  neg_polarity l r := by cases l with
    | top => cases r <;> simp only <;> split <;> simp
    | coe => cases r <;> simp only [neg_polarity]; split <;> simp
  bot_polarity e := by cases e with
    | top => simp only; split; rfl; case isFalse h => exact (h rfl).elim
    | coe => simp only [bot_polarity]
  polarity_anti_right r lo hi h := by
    cases r <;> cases lo <;> cases hi <;> simp at h
    <;> simp only [polarity_anti_right, *]
    <;> split
    <;> simp
    <;> case isTrue h => cases h
      <;> simp [bot_polarity] at * <;> cases h <;> intro c <;> exact (c rfl).elim

class HasQuant (τ : Type u) where
  quant : τ → Quant

class HasPQuant (τ : Type u) where
  pquant : τ → PQuant

open HasPQuant

instance HasPQuant.hasQuant {τ : Type u} [HasPQuant τ] : HasQuant τ where
  quant a := (pquant a).q

class OrderedPQuant (τ : Type u) [LE τ] [Bot τ] extends HasPQuant τ where
  pquant_bot : pquant (⊥ : τ) = ⊤
  pquant_anti : ∀lo hi : τ, lo ≤ hi → pquant hi ≤ pquant lo

def EQuant.subst_polarity
  (q : EQuant)
  {ε} [LE ε] [Bot ε] [HasPQuant ε] [Polar ε] (before after : ε) : Polarities
  := match q with
  | 0 => (pquant before).qp .del
  | (q : Quant) => (pquant before).qp q ⊓ polarity before after

@[simp]
theorem EQuant.subst_polarity_zero
  {ε} [LE ε] [Bot ε] [HasPQuant ε] [Polar ε] (before after : ε)
  : EQuant.subst_polarity 0 before after = (pquant before).qp .del
  := rfl

@[simp]
theorem EQuant.subst_polarity_coe
  {ε} [LE ε] [Bot ε] [HasPQuant ε] [Polar ε] (q : Quant) (before after : ε)
  : EQuant.subst_polarity q before after = (pquant before).qp q ⊓ polarity before after
  := rfl

@[simp]
theorem EQuant.subst_polarity_one
  {ε} [LE ε] [Bot ε] [HasPQuant ε] [Polar ε] (before after : ε)
  : EQuant.subst_polarity 1 before after = polarity before after
  := by simp [EQuant.subst_polarity]

@[simp]
theorem EQuant.subst_polarity_copy
  {ε} [LE ε] [Bot ε] [HasPQuant ε] [Polar ε] (before after : ε)
  : EQuant.subst_polarity .copy before after = (pquant before).qp .copy ⊓ polarity before after
  := by simp [EQuant.subst_polarity]

@[simp]
theorem EQuant.subst_polarity_del
  {ε} [LE ε] [Bot ε] [HasPQuant ε] [Polar ε] (before after : ε)
  : EQuant.subst_polarity .del before after = (pquant before).qp .del ⊓ polarity before after
  := by simp [EQuant.subst_polarity]

@[simp]
theorem EQuant.subst_polarity_top
  {ε} [LE ε] [Bot ε] [HasPQuant ε] [Polar ε] (before after : ε)
  : EQuant.subst_polarity ⊤ before after = (pquant before).qp ⊤ ⊓ polarity before after
  := by simp [EQuant.subst_polarity]

theorem EQuant.subst_polarity_anti_quant
  {q q' : EQuant} (h : q ≤ q')
  {ε} [LE ε] [Bot ε] [HasPQuant ε] [Polar ε] (before after : ε)
  : EQuant.subst_polarity q' before after ≤ EQuant.subst_polarity q before after
  := by cases h using EQuant.le.casesLE_all
    <;> simp
    <;> apply inf_le_of_left_le
    <;> apply PQuant.qp_anti_quant
    <;> decide

theorem EQuant.subst_polarity_anti_before
  {q : EQuant} {ε} [LE ε] [Bot ε] [OrderedPQuant ε] [Polar ε]
  {before before'} (h : before ≤ before') (after : ε)
  : EQuant.subst_polarity q before' after ≤ EQuant.subst_polarity q before after
  := by cases q using EQuant.casesZero with
  | zero =>
    simp only [subst_polarity_zero]
    apply PQuant.qp_mono_pquant
    apply OrderedPQuant.pquant_anti _ _ h
  | rest q =>
    simp only [subst_polarity_coe]
    apply inf_le_inf
    apply PQuant.qp_mono_pquant
    apply OrderedPQuant.pquant_anti _ _ h
    apply Polar.polarity_anti_left _ _ _ h

theorem EQuant.subst_polarity_anti_after
  {q : EQuant} {ε} [LE ε] [Bot ε] [OrderedPQuant ε] [Polar ε]
  (before : ε) {after after'} (h : after ≤ after')
  : EQuant.subst_polarity q before after' ≤ EQuant.subst_polarity q before after
  := by cases q using EQuant.casesZero with
  | zero => simp
  | rest q => simp; apply inf_le_of_right_le; apply Polar.polarity_anti_right _ _ _ h
