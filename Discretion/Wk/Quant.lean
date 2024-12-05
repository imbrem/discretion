import Mathlib.Order.CompleteBooleanAlgebra
import Mathlib.Data.Fintype.Order
import Mathlib.Data.Fintype.Prod

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

instance Quant.instBooleanAlgebra : BooleanAlgebra Quant
  := (inferInstance : BooleanAlgebra (Bool × Bool))

theorem Quant.is_copy_le {q : Quant} (h : q.is_copy) : .copy ≤ q := ⟨by simp [h], by simp⟩

theorem Quant.is_del_le {q : Quant} (h : q.is_del) : .del ≤ q := ⟨by simp, by simp [h]⟩

instance Quant.instDecidableEq : DecidableEq Quant
  := (inferInstance : DecidableEq (Bool × Bool))

def Quant.dc (q : Quant) : Set DupCap | .copy => q.is_copy | .del => q.is_del

theorem Quant.copy_mem_dc {q : Quant} : .copy ∈ q.dc ↔ q.is_copy := Iff.rfl

theorem Quant.del_mem_dc {q : Quant} : .del ∈ q.dc ↔ q.is_del := Iff.rfl

@[simp]
theorem Quant.dc_copy : copy.dc = {DupCap.copy}
  := by ext c; cases c <;> simp [copy_mem_dc, del_mem_dc]

@[simp]
theorem Quant.dc_del : del.dc = {DupCap.del} := by ext c; cases c <;> simp [copy_mem_dc, del_mem_dc]

instance Quant.instTop : Top Quant where top := ⟨true, true⟩

instance Quant.instBot : Bot Quant where bot := ⟨false, false⟩

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
  (bot : motive ⊥)
  : ∀(q : Quant), motive q
  | ⊤ => top
  | Quant.copy => copy
  | Quant.del => del
  | ⊥ => bot

def Quant.casesOn_le {motive : ∀(q q' : Quant), q ≤ q' → Sort _}
  (top : ∀q, motive q ⊤ (by simp))
  (copy : motive .copy .copy (by rfl))
  (del : motive .del .del (by rfl))
  (bot_copy : motive ⊥ .copy (by simp))
  (bot_del : motive ⊥ .del (by simp))
  (bot : motive ⊥ ⊥ (by simp))
  (q q') (h : q ≤ q') : motive q q' h
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
  {q q'} (h : q ≤ q') : @motive q q' h
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
  elems := {⊥, copy, del, ⊤}
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

def Quant.c (q : Quant) : Set ℕ := { n | n = 1 ∨ (q.is_del ∧ n = 0) ∨ (q.is_copy ∧ n > 1) }

@[simp]
theorem Quant.c_top : c ⊤ = Set.univ := by ext n; simp only [c, Top.top, true_and, gt_iff_lt,
  Set.mem_setOf_eq, Set.mem_univ, iff_true]; omega

@[simp]
theorem Quant.c_copy : c copy = Set.Ici 1 := by ext n; simp [Quant.c, Nat.le_iff_lt_or_eq]; tauto

@[simp]
theorem Quant.c_del : c del = {0, 1} := by ext n; simp [Quant.c, or_comm]

@[simp]
theorem Quant.c_bot : c ⊥ = {1} := by ext n; simp [Quant.c]

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

theorem Quant.c_def' {q : Quant} : q.c = {1} ∪ ⋃d ∈ q.dc, d.c := by cases q <;> simp

@[simp]
theorem Quant.zero_in_c_iff {q : Quant} : 0 ∈ q.c ↔ q.is_del := by simp [Quant.c]

@[simp]
theorem Quant.one_in_c {q : Quant} : 1 ∈ q.c := by simp [Quant.c]

@[simp]
theorem Quant.n_plus_two_in_c_iff {q : Quant} {n} : n + 2 ∈ q.c ↔ q.is_copy := by simp [Quant.c]

theorem Quant.two_in_c_iff {q : Quant} : 2 ∈ q.c ↔ q.is_copy := by simp

instance Quant.instMonoid : Monoid Quant where
  mul
  | .del, q => q
  | q, .del => q
  | ⊤, _ => ⊤
  | _, ⊤ => ⊤
  | _, _ => .copy
  one := .del
  mul_assoc a b c := by cases a <;> cases b <;> cases c <;> rfl
  one_mul a := by cases a <;> rfl
  mul_one a := by cases a <;> rfl

@[simp]
theorem Quant.mul_del {q : Quant} : .del * q = q := by cases q <;> rfl

@[simp]
theorem Quant.del_mul {q : Quant} : q * .del = q := by cases q <;> rfl

@[simp]
theorem Quant.mul_top {q : Quant} : q * ⊤ = ⊤ := by cases q <;> rfl

@[simp]
theorem Quant.top_mul {q : Quant} : ⊤ * q = ⊤ := by cases q <;> rfl

@[simp]
theorem Quant.copy_mul_copy : Quant.copy * .copy = .copy := rfl

@[simp]
theorem Quant.copy_mul_bot : Quant.copy * ⊥ = .copy := rfl

@[simp]
theorem Quant.bot_mul_copy : ⊥ * Quant.copy = .copy := rfl

@[simp]
theorem Quant.bot_mul_bot : ⊥ * ⊥ = Quant.copy := rfl

@[simp]
theorem Quant.le_mul_self {q : Quant} : q ≤ q * q := by cases q <;> simp

inductive Polarity : Type
  | pos
  | neg
  deriving DecidableEq

instance Polarity.instFinType : Fintype Polarity where
  elems := {Polarity.pos, Polarity.neg}
  complete x := by cases x <;> simp

def PQuant : Type := Quant × Quant

instance PQuant.instBooleanAlgebra : BooleanAlgebra PQuant
  := (inferInstance : BooleanAlgebra (Quant × Quant))

def PQuant.split : PQuant := ⟨Quant.copy, ⊥⟩

def PQuant.fuse : PQuant := ⟨⊥, Quant.copy⟩

def PQuant.rem : PQuant := ⟨Quant.del, ⊥⟩

def PQuant.add : PQuant := ⟨⊥, Quant.del⟩

def PQuant.copy : PQuant := ⟨Quant.copy, Quant.copy⟩

def PQuant.del : PQuant := ⟨Quant.del, Quant.del⟩

abbrev PQuant.pos (q : PQuant) : Quant := q.1

abbrev PQuant.neg (q : PQuant) : Quant := q.2

def PQuant.pq (q : PQuant) : Polarity → Quant | .pos => q.pos | .neg => q.neg

def PQuant.dc (q : PQuant) : Set (Polarity × DupCap) := {d | d.2 ∈ (q.pq d.1).dc}

-- TODO: pq and dc are lattice isomorphisms

def PQuant.q (q : PQuant) : Quant := q.1 ⊓ q.2

def PQuant.c (q : PQuant) : Set ℕ := q.q.c

@[simp]
theorem PQuant.split_le_copy : PQuant.split ≤ PQuant.copy := by simp [split, copy, LE.le]

@[simp]
theorem PQuant.fuse_le_copy : PQuant.fuse ≤ PQuant.copy := by simp [fuse, copy, LE.le]

@[simp]
theorem PQuant.split_sup_fuse : PQuant.split ⊔ PQuant.fuse = PQuant.copy := by
  simp [split, fuse, copy, max, SemilatticeSup.sup, Quant.copy, Bot.bot]

@[simp]
theorem PQuant.fuse_sup_split : PQuant.fuse ⊔ PQuant.split = PQuant.copy := by
  simp [split, fuse, copy, max, SemilatticeSup.sup, Quant.copy, Bot.bot]

@[simp]
theorem PQuant.rem_le_del : PQuant.rem ≤ PQuant.del := by simp [rem, del, LE.le]

@[simp]
theorem PQuant.add_le_del : PQuant.add ≤ PQuant.del := by simp [add, del, LE.le]

@[simp]
theorem PQuant.rem_sup_add : PQuant.rem ⊔ PQuant.add = PQuant.del := by
  simp [rem, add, del, max, SemilatticeSup.sup, Quant.del, Bot.bot]

@[simp]
theorem PQuant.add_sup_rem : PQuant.add ⊔ PQuant.rem = PQuant.del := by
  simp [rem, add, del, max, SemilatticeSup.sup, Quant.del, Bot.bot]

instance PQuant.instFintype : Fintype PQuant := (inferInstance : Fintype (Quant × Quant))
