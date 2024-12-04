import Mathlib.CategoryTheory.Monoidal.Free.Basic
import Mathlib.Order.CompleteBooleanAlgebra
import Mathlib.Data.Fintype.Order

import Discretion.Vector.Basic

open Mathlib

open CategoryTheory.MonoidalCategory

namespace SEC

local notation "Ty" => CategoryTheory.FreeMonoidalCategory

local notation "tyOf" => CategoryTheory.FreeMonoidalCategory.of

def Ctx (τ : Type _) := List τ

@[match_pattern]
def Ctx.nil {τ} : Ctx τ := []

@[match_pattern]
def Ctx.cons {τ} (Γ : Ctx τ) (A : τ) : Ctx τ := A :: Γ

infixr:67 " ;; " => Ctx.cons

inductive Nat.Split : ℕ → ℕ → ℕ → Type where
  | nil : Split 0 0 0
  | both {n m k} (ρ : Split n m k) : Split (n + 1) (m + 1) (k + 1)
  | left {n m k} (ρ : Split n m k) : Split (n + 1) (m + 1) k
  | right {n m k} (ρ : Split n m k) : Split (n + 1) m (k + 1)
  | skip {n m k} (ρ : Split n m k) : Split (n + 1) m k

def Nat.Wk (n m : ℕ) := Nat.Split n 0 m

-- TODO: and friends... but also, just a Wk pair might work? might even be cleaner?

inductive Ctx.Split {τ} : Ctx τ → Ctx τ → Ctx τ → Type where
  | nil : Split [] [] []
  | both (ρ : Split Γ Δ Ξ) (A) : Split (Γ ;; A) (Δ ;; A) (Ξ ;; A)
  | left (ρ : Split Γ Δ Ξ) (A) : Split (Γ ;; A) (Δ ;; A) Ξ
  | right (ρ : Split Γ Δ Ξ) (A) : Split (Γ ;; A) Δ (Ξ ;; A)
  | skip (ρ : Split Γ Δ Ξ) (A) : Split (Γ ;; A) Δ Ξ

theorem Ctx.Split.length_left_le {τ} {Γ Δ Ξ : Ctx τ}
  (ρ : Γ.Split Δ Ξ) : Δ.length ≤ Γ.length := by
  induction ρ <;> simp only [cons, List.length_cons, List.length_nil] <;> omega

theorem Ctx.Split.length_right_le {τ} {Γ Δ Ξ : Ctx τ}
  (ρ : Γ.Split Δ Ξ) : Ξ.length ≤ Γ.length := by
  induction ρ <;> simp only [cons, List.length_cons, List.length_nil] <;> omega

def Ctx.Wk {τ} (Γ : Ctx τ) (Δ : Ctx τ) := Ctx.Split Γ [] Δ

@[match_pattern]
def Ctx.Wk.nil : Ctx.Wk (τ := τ) [] [] := Ctx.Split.nil

@[match_pattern]
def Ctx.Wk.skip (ρ : Γ.Wk Δ) (A) : Ctx.Wk (Γ ;; A) Δ := Ctx.Split.skip ρ A

@[match_pattern]
def Ctx.Wk.cons (ρ : Γ.Wk Δ) (A) : Ctx.Wk (Γ ;; A) (Δ ;; A) := Ctx.Split.right ρ A

@[elab_as_elim, induction_eliminator]
def Ctx.Wk.inductionOn {τ}
  {motive : ∀{Γ Δ}, Ctx.Wk Γ Δ → Sort _}
  (nil : motive Ctx.Wk.nil)
  (skip : ∀(Γ Δ : Ctx τ) (ρ : Γ.Wk Δ) (A), motive ρ → motive (Ctx.Wk.skip ρ A))
  (cons : ∀(Γ Δ : Ctx τ) (ρ : Γ.Wk Δ) (A), motive ρ → motive (Ctx.Wk.cons ρ A))
  {Γ Δ : Ctx τ} : ∀ρ : Γ.Wk Δ, motive ρ
  | .nil => nil
  | .skip ρ a => skip _ _ ρ a (inductionOn nil skip cons ρ)
  | .cons ρ a => cons _ _ ρ a (inductionOn nil skip cons ρ)

inductive DupCap : Type
  | copy
  | del
  deriving DecidableEq

instance DupCap.instFintype : Fintype DupCap where
  elems := {DupCap.copy, DupCap.del}
  complete x := by cases x <;> simp

def Quant := Bool × Bool

-- instance Quant.instPartialOrder : PartialOrder Quant where
--   le q₁ q₂ := q₁.is_copy ≤ q₂.is_copy ∧ q₁.is_del ≤ q₂.is_del
--   le_refl q := ⟨Bool.le_refl _, Bool.le_refl _⟩
--   le_trans q₁ q₂ q₃ h₁₂ h₂₃ := ⟨h₁₂.1.trans h₂₃.1, h₁₂.2.trans h₂₃.2⟩
--   -- TODO: kernel declaration has metavariables when we pattern match on h, h'
--   le_antisymm q₁ q₂ h h' := by cases h; cases h'; ext <;> apply le_antisymm <;> assumption

-- theorem le_mk_iff {c d c' d' : Bool} : Quant.mk c d ≤ Quant.mk c' d' ↔ c ≤ c' ∧ d ≤ d' := Iff.rfl

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

instance Quant.instBooleanAlgebra : BooleanAlgebra Quant
  := (inferInstance : BooleanAlgebra (Bool × Bool))

instance Quant.instDecidableEq : DecidableEq Quant
  := (inferInstance : DecidableEq (Bool × Bool))

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

instance Quant.instFintype : Fintype Quant where
  elems := {⊥, copy, del, ⊤}
  complete x := by cases x <;> simp

-- TODO: dc is a boolean algebra isomorphism

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

def PQuant.copy : PQuant := ⟨Quant.copy, Quant.copy⟩

def PQuant.del : PQuant := ⟨Quant.del, Quant.del⟩

abbrev PQuant.pos (q : PQuant) : Quant := q.1

abbrev PQuant.neg (q : PQuant) : Quant := q.2

def PQuant.pq (q : PQuant) : Polarity → Quant | .pos => q.pos | .neg => q.neg

def PQuant.dc (q : PQuant) : Set (Polarity × DupCap) := {d | d.2 ∈ (q.pq d.1).dc}

def PQuant.q (q : PQuant) : Quant := q.1 ⊓ q.2

def PQuant.c (q : PQuant) : Set ℕ := q.q.c

-- TODO: dc/q/c are monotone, join/meet preserving, etc

inductive Ctx.Split.WQ {τ}
  : ∀{Γ Δ Ξ : Ctx τ}, Γ.Split Δ Ξ
    → Vector' Quant Γ.length
    → Vector' Quant Δ.length
    → Vector' Quant Ξ.length → Prop
  | nil : WQ Split.nil Vector'.nil Vector'.nil Vector'.nil
  | both {ρ : Split Γ Δ Ξ} (h : WQ ρ qΓ qΔ qΞ) (A) (q q' q'')
    : q.is_copy → q ≥ q' → q ≥ q'' → WQ (Split.both ρ A) (qΓ.cons q) (qΔ.cons q') (qΞ.cons q'')
  | left {ρ : Split Γ Δ Ξ} (h : WQ ρ qΓ qΔ qΞ) (A) (q q')
    : q ≥ q' → WQ (Split.left ρ A) (qΓ.cons q) (qΔ.cons q') qΞ
  | right {ρ : Split Γ Δ Ξ} (h : WQ ρ qΓ qΔ qΞ) (A) (q q')
    : q ≥ q' → WQ (Split.right ρ A) (qΓ.cons q) qΔ (qΞ.cons q')
  | skip {ρ : Split Γ Δ Ξ} (h : WQ ρ qΓ qΔ qΞ) (A) (q)
    : q.is_del → WQ (Split.skip ρ A) (qΓ.cons q) qΔ qΞ

theorem Ctx.Split.WQ.le_congr
  {τ} {Γ Δ Ξ : Ctx τ} {ρ : Γ.Split Δ Ξ} {qΓ qΔ qΞ} {qΓ' qΔ' qΞ'}
  (h : WQ ρ qΓ qΔ qΞ) (hΓ : qΓ ≤ qΓ') (hΔ : qΔ' ≤ qΔ) (hΞ : qΞ' ≤ qΞ)
  : WQ ρ qΓ' qΔ' qΞ' := by
  induction h with
  | nil => cases qΓ'; cases qΔ'; cases qΞ'; constructor
  | both _ _ _ _ _ hd hxy hxz I =>
    cases hΓ; cases hΔ; cases hΞ
    constructor
    apply I <;> assumption
    apply Quant.is_copy_mono _ hd
    assumption
    apply le_trans _ (le_trans hxy _) <;> assumption
    apply le_trans _ (le_trans hxz _) <;> assumption
  | left _ _ _ _ hxy I =>
    cases hΓ; cases hΔ;
    constructor
    apply I <;> assumption
    apply le_trans _ (le_trans hxy _) <;> assumption
  | right _ _ _ _ hxy I =>
    cases hΓ; cases hΞ;
    constructor
    apply I <;> assumption
    apply le_trans _ (le_trans hxy _) <;> assumption
  | skip _ _ _ hd I =>
    cases hΓ
    constructor
    apply I <;> assumption
    apply Quant.is_del_mono _ hd
    assumption

inductive Ctx.Split.Q {τ}
  : ∀{Γ Δ Ξ : Ctx τ}, Γ.Split Δ Ξ
    → Vector' Quant Γ.length
    → Vector' Quant Δ.length
    → Vector' Quant Ξ.length → Prop
  | nil : Q Split.nil Vector'.nil Vector'.nil Vector'.nil
  | both {ρ : Split Γ Δ Ξ} (h : Q ρ qΓ qΔ qΞ) (A) (q)
    : q.is_copy → Q (Split.both ρ A) (qΓ.cons q) (qΔ.cons q) (qΞ.cons q)
  | left {ρ : Split Γ Δ Ξ} (h : Q ρ qΓ qΔ qΞ) (A) (q)
    : Q (Split.left ρ A) (qΓ.cons q) (qΔ.cons q) qΞ
  | right {ρ : Split Γ Δ Ξ} (h : Q ρ qΓ qΔ qΞ) (A) (q)
    : Q (Split.right ρ A) (qΓ.cons q) qΔ (qΞ.cons q)
  | skip {ρ : Split Γ Δ Ξ} (h : Q ρ qΓ qΔ qΞ) (A) (q)
    : q.is_del → Q (Split.skip ρ A) (qΓ.cons q) qΔ qΞ

theorem Ctx.Split.Q.toWQ {τ} {Γ Δ Ξ : Ctx τ} {ρ : Γ.Split Δ Ξ}
  {qΓ qΔ qΞ} (h : Q ρ qΓ qΔ qΞ) : WQ ρ qΓ qΔ qΞ := by induction h <;> constructor <;> simp [*]

inductive Ctx.Split.WV {τ} {ε} [LE ε]
  : ∀{Γ Δ Ξ : Ctx τ}, Γ.Split Δ Ξ
    → Vector' ε Γ.length
    → Vector' ε Δ.length
    → Vector' ε Ξ.length → Prop
  | nil : WV Split.nil Vector'.nil Vector'.nil Vector'.nil
  | both {ρ : Split Γ Δ Ξ} (h : WV ρ qΓ qΔ qΞ) (A) (q q' q'')
    : q ≤ q' → q' ≤ q'' → WV (Split.both ρ A) (qΓ.cons q) (qΔ.cons q') (qΞ.cons q'')
  | left {ρ : Split Γ Δ Ξ} (h : WV ρ qΓ qΔ qΞ) (A) (q q')
    : q ≤ q' → WV (Split.left ρ A) (qΓ.cons q) (qΔ.cons q') qΞ
  | right {ρ : Split Γ Δ Ξ} (h : WV ρ qΓ qΔ qΞ) (A) (q q')
    : q ≤ q' → WV (Split.right ρ A) (qΓ.cons q) qΔ (qΞ.cons q')
  | skip {ρ : Split Γ Δ Ξ} (h : WV ρ qΓ qΔ qΞ) (A) (q)
    : WV (Split.skip ρ A) (qΓ.cons q) qΔ qΞ

def Ctx.Split.leftV {τ ε} {Γ Δ Ξ : Ctx τ}
  : Γ.Split Δ Ξ → Vector' ε Γ.length → Vector' ε Δ.length
  | .nil, .nil => .nil
  | .both ρ _, .cons a v
  | .left ρ _, .cons a v => (ρ.leftV v).cons a
  | .right ρ _, .cons a v
  | .skip ρ _, .cons a v => ρ.leftV v

def Ctx.Split.rightV {τ ε} {Γ Δ Ξ : Ctx τ}
  : Γ.Split Δ Ξ → Vector' ε Γ.length → Vector' ε Ξ.length
  | .nil, .nil => .nil
  | .both ρ _, .cons a v
  | .right ρ _, .cons a v => (ρ.rightV v).cons a
  | .left ρ _, .cons a v
  | .skip ρ _, .cons a v => ρ.rightV v

inductive Ctx.Split.V {τ} {ε}
  : ∀{Γ Δ Ξ : Ctx τ}, Γ.Split Δ Ξ
    → Vector' ε Γ.length
    → Vector' ε Δ.length
    → Vector' ε Ξ.length → Prop
  | nil : V Split.nil Vector'.nil Vector'.nil Vector'.nil
  | both {ρ : Split Γ Δ Ξ} (h : V ρ qΓ qΔ qΞ) (A) (q)
    : V (Split.both ρ A) (qΓ.cons q) (qΔ.cons q) (qΞ.cons q)
  | left {ρ : Split Γ Δ Ξ} (h : V ρ qΓ qΔ qΞ) (A) (q)
    : V (Split.left ρ A) (qΓ.cons q) (qΔ.cons q) qΞ
  | right {ρ : Split Γ Δ Ξ} (h : V ρ qΓ qΔ qΞ) (A) (q)
    : V (Split.right ρ A) (qΓ.cons q) qΔ (qΞ.cons q)
  | skip {ρ : Split Γ Δ Ξ} (h : V ρ qΓ qΔ qΞ) (A) (q)
    : V (Split.skip ρ A) (qΓ.cons q) qΔ qΞ

theorem Ctx.Split.V.toWV {τ ε} [Preorder ε] {Γ Δ Ξ : Ctx τ} {ρ : Γ.Split Δ Ξ}
  {qΓ qΔ qΞ} (h : V (ε := ε) ρ qΓ qΔ qΞ) : WV ρ qΓ qΔ qΞ
  := by induction h <;> constructor <;> simp [*]
