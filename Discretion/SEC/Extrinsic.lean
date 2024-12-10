import Mathlib.CategoryTheory.Monoidal.Free.Basic
import Discretion.Wk.List

import Discretion.SEC.Signature
import Discretion.SEC.Untyped

open CategoryTheory

open CategoryTheory.MonoidalCategory

namespace SEC

open FreeSignature

namespace Term

variable {τ} [FreeSignature τ]

inductive Wf : List (Ty τ) → Term τ → (outParam (Ty τ)) → Prop
  | var {Γ i A} (hΓ : i < Γ.length) : Γ[i] = A → Wf Γ (.var i) A
  | op {Γ f a A B} (hA : f.src = A) (hB : f.trg = B) : Wf Γ a A → Wf Γ (.op f a) B
  | let₁ {Γ a b A B} : Wf Γ a A → Wf (A::Γ) b B → Wf Γ (.let₁ a b) B
  | unit {Γ} : Wf Γ .unit (𝟙_ _)
  | pair {Γ a b A B} : Wf Γ a A → Wf Γ b B → Wf Γ (.pair a b) (A ⊗ B)
  | let₂ {Γ a c A B C} : Wf Γ a (A ⊗ B) → Wf (B::A::Γ) c C → Wf Γ (.let₂ a c) C

-- attribute [class] Wf

-- attribute [instance] var unit

-- instance Wf.op_f (Γ f a A B) [hf : Untyped.IsFn f A B] [ha : Wf Γ a A]
--   : Wf (τ := τ) Γ (.op f a) B := .op hf.src_eq hf.trg_eq ha

-- instance Wf.pair_f (Γ) (a b) (A B) [ha : Wf Γ a A] [hb : Wf Γ b B]
--   : Wf (τ := τ) Γ (.pair a b) (A ⊗ B) := .pair ha hb

def inferTy (Γ : List (Ty τ)) : Term τ → Ty τ
  | .var i => if h : i < Γ.length then Γ[i] else .unit
  | .op f a => f.trg
  | .let₁ a b => b.inferTy ((a.inferTy Γ)::Γ)
  | .pair a b => a.inferTy Γ ⊗ b.inferTy Γ
  | .let₂ a b => match a.inferTy Γ with
    | .tensor A B => b.inferTy (B::A::Γ)
    | _ => .unit
  | _ => .unit

theorem Wf.inferTy_eq {Γ} {t : Term τ} {A} (hA : Wf Γ t A)
  : t.inferTy Γ = A := by induction hA <;> simp [inferTy, *]

theorem Wf.unique {Γ} {t : Term τ} {A B}
  (hA : Wf Γ t A) (hB : Wf Γ t B) : A = B := by rw [<-hA.inferTy_eq, <-hB.inferTy_eq]

def Wf.invalid {Γ A} (h : Wf (τ := τ) Γ .invalid A) {α} : α := by cases h

def inferLeft (Γ : List (Ty τ)) (a : Term τ) : Ty τ := match a.inferTy Γ with
  | .tensor A _ => A
  | _ => .unit

def inferRight (Γ : List (Ty τ)) (a : Term τ) : Ty τ := match a.inferTy Γ with
  | .tensor _ B => B
  | _ => .unit

@[simp]
theorem Wf.var_lt_length {Γ i A} (h : Wf (τ := τ) Γ (.var i) A)
  : i < Γ.length := by cases h; assumption

@[simp]
theorem Wf.var_getElem_eq {Γ i A} (h : Wf (τ := τ) Γ (.var i) A)
  : Γ[i]'h.var_lt_length = A := by cases h; assumption

theorem Wf.op_src_eq {Γ f a B} (h : Wf (τ := τ) Γ (.op f a) B)
  : f.src = a.inferTy Γ := by cases h with | op h _ ha => convert h; rw [ha.inferTy_eq]

theorem Wf.op_trg_eq {Γ f a B} (h : Wf (τ := τ) Γ (.op f a) B)
  : f.trg = B := by cases h with | op _ h _ => exact h

theorem Wf.op_arg {Γ f a B} (h : Wf (τ := τ) Γ (.op f a) B)
  : Wf Γ a f.src := by cases h with | op h _ ha => exact h ▸ ha

theorem Wf.unit_ty_eq {Γ} (h : Wf (τ := τ) Γ .unit A) : A = .unit := by cases h; rfl

theorem Wf.pair_ty_eq {Γ a b C} (h : Wf (τ := τ) Γ (.pair a b) C)
  : C = a.inferTy Γ ⊗ b.inferTy Γ
  := by cases h with | pair ha hb => rw [ha.inferTy_eq, hb.inferTy_eq]

theorem Wf.pair_left {Γ a b A B} (h : Wf (τ := τ) Γ (.pair a b) (A ⊗ B))
  : Wf Γ a A := by cases h; assumption

theorem Wf.pair_right {Γ a b A B} (h : Wf (τ := τ) Γ (.pair a b) (A ⊗ B))
  : Wf Γ b B := by cases h; assumption

theorem Wf.pair_left' {Γ a b C} (h : Wf (τ := τ) Γ (.pair a b) C) : Wf Γ a (a.inferTy Γ)
  := (h.pair_ty_eq ▸ h).pair_left

theorem Wf.pair_right' {Γ a b C} (h : Wf (τ := τ) Γ (.pair a b) C) : Wf Γ b (b.inferTy Γ)
  := (h.pair_ty_eq ▸ h).pair_right

theorem Wf.let₁_bind {Γ a b B} (h : Wf (τ := τ) Γ (.let₁ a b) B)
  : Wf Γ a (a.inferTy Γ) := by cases h with | let₁ ha hb => convert ha; rw [ha.inferTy_eq]

theorem Wf.let₁_expr {Γ a b B} (h : Wf (τ := τ) Γ (.let₁ a b) B)
  : Wf (a.inferTy Γ::Γ) b B := by cases h with | let₁ ha hb => convert hb; rw [ha.inferTy_eq]

theorem Wf.let₂_bind {Γ a c C} (h : Wf (τ := τ) Γ (.let₂ a c) C)
  : Wf Γ a (a.inferLeft Γ ⊗ a.inferRight Γ) := by
  cases h with | let₂ ha hb =>
    simp only [inferLeft, inferRight]
    split
    case h_1 t => rw [ha.inferTy_eq] at t; cases t; exact ha
    case h_2 t => exact (t _ _ ha.inferTy_eq).elim

theorem Wf.let₂_expr {Γ a c C} (h : Wf (τ := τ) Γ (.let₂ a c) C)
  : Wf (a.inferRight Γ::a.inferLeft Γ::Γ) c C := by
  cases h with | let₂ ha hb =>
    simp only [inferLeft, inferRight]
    split
    case h_1 t => rw [ha.inferTy_eq] at t; cases t; exact hb
    case h_2 t => exact (t _ _ ha.inferTy_eq).elim

-- TODO: set as default eliminator?
@[elab_as_elim]
def Wf.induction' {motive : ∀ {Γ t A}, Wf (τ := τ) Γ t A → Sort u}
  (var : ∀ {Γ i A} (hΓ : i < Γ.length) (hA : Γ[i] = A), motive (.var hΓ hA))
  (op : ∀ {Γ} {f : Untyped.Inst τ} {a A B} (hA : f.src = A) (hB : f.trg = B) (ha : Wf Γ a A),
    motive ha → motive (.op hA hB ha))
  (let₁ : ∀ {Γ a b A B} (ha : Wf Γ a A) (hb : Wf (A::Γ) b B),
    motive ha → motive hb → motive (.let₁ ha hb))
  (unit : ∀ {Γ}, motive (Γ := Γ) .unit)
  (pair : ∀ {Γ a b A B} (ha : Wf Γ a A) (hb : Wf Γ b B),
    motive ha → motive hb → motive (.pair ha hb))
  (let₂ : ∀ {Γ a c A B C} (ha : Wf Γ a (A ⊗ B)) (hc : Wf (B::A::Γ) c C),
    motive ha → motive hc → motive (.let₂ ha hc))
  {Γ t A} (h : Wf Γ t A) : motive h := match t, A, h with
  | .var _, _, h => var h.var_lt_length h.var_getElem_eq
  | .op _ _, _, h => op rfl h.op_trg_eq h.op_arg (induction' var op let₁ unit pair let₂ h.op_arg)
  | .let₁ _ _, _, h => let₁ h.let₁_bind h.let₁_expr
    (induction' var op let₁ unit pair let₂ h.let₁_bind)
    (induction' var op let₁ unit pair let₂ h.let₁_expr)
  | .unit, .unit, _ => unit
  | .pair _ _, .tensor _ _, h => pair h.pair_left h.pair_right
    (induction' var op let₁ unit pair let₂ h.pair_left)
    (induction' var op let₁ unit pair let₂ h.pair_right)
  | .let₂ _ _, _, h => let₂ h.let₂_bind h.let₂_expr
    (induction' var op let₁ unit pair let₂ h.let₂_bind)
    (induction' var op let₁ unit pair let₂ h.let₂_expr)

@[elab_as_elim]
def Wf.cases' {motive : ∀ {Γ t A}, Wf (τ := τ) Γ t A → Sort u}
  (var : ∀ {Γ i A} (hΓ : i < Γ.length) (hA : Γ[i] = A), motive (.var hΓ hA))
  (op : ∀ {Γ} {f : Untyped.Inst τ} {a A B} (hA : f.src = A) (hB : f.trg = B) (ha : Wf Γ a A),
    motive (.op hA hB ha))
  (let₁ : ∀ {Γ a b A B} (ha : Wf Γ a A) (hb : Wf (A::Γ) b B),
    motive (.let₁ ha hb))
  (unit : ∀ {Γ}, motive (Γ := Γ) .unit)
  (pair : ∀ {Γ a b A B} (ha : Wf Γ a A) (hb : Wf Γ b B),
    motive (.pair ha hb))
  (let₂ : ∀ {Γ a c A B C} (ha : Wf Γ a (A ⊗ B)) (hc : Wf (B::A::Γ) c C),
    motive (.let₂ ha hc))
  {Γ t A} (h : Wf Γ t A) : motive h := match t, A, h with
  | .var _, _, h => var h.var_lt_length h.var_getElem_eq
  | .op _ _, _, h => op rfl h.op_trg_eq h.op_arg
  | .let₁ _ _, _, h => let₁ h.let₁_bind h.let₁_expr
  | .unit, .unit, _ => unit
  | .pair _ _, .tensor _ _, h => pair h.pair_left h.pair_right
  | .let₂ _ _, _, h => let₂ h.let₂_bind h.let₂_expr

theorem Wf.wk {Γ Δ} {ρ : ℕ → ℕ} (hρ : List.IsWk Γ Δ ρ) {t : Term τ} {A}
  (h : Wf Δ t A) : Wf Γ (t.wk ρ) A := by
  induction h generalizing Γ ρ with
  | var hi => have h := hρ.getElem_eq _ hi; constructor; rw [h]; assumption
  | _ => constructor <;> apply_assumption

theorem Wf.wk_f {Γ Δ} (ρ : ℕ → ℕ) [hρ : List.IsWk Γ Δ ρ] {t : Term τ} {A}
  (h : Wf Δ t A) : Wf Γ (t.wk ρ) A := h.wk hρ

theorem Wf.unwk {Γ Δ} {ρ : ℕ → ℕ} (hρ : List.IsWk Γ Δ ρ) {t : Term τ} {A}
  (h : Wf Γ (t.wk ρ) A) (ht : t.fvi ≤ Δ.length) : Wf Δ t A := by
  induction t generalizing Γ Δ ρ A <;> cases h
  case var hΓ ha => apply var; rw [<-hρ.getElem_eq _ ht, ha]
  all_goals {
    simp [fvi] at ht
    constructor
    all_goals {
      apply_assumption
      <;> (repeat apply λhρ => List.IsWk.lift (hρ := hρ))
      <;> first | assumption | ((try simp only [List.length_cons]); omega)
    }
  }

theorem Wf.unwk_f {Γ Δ} (ρ : ℕ → ℕ) [hρ : List.IsWk Γ Δ ρ] {t : Term τ} {A}
  (h : Wf Γ (t.wk ρ) A) (ht : t.fvi ≤ Δ.length) : Wf Δ t A := h.unwk hρ ht

theorem Wf.fvi {Γ} {t : Term τ} {A} (h : Wf Γ t A) : t.fvi ≤ Γ.length := by
  induction h <;> simp [Term.fvi] at * <;> omega

theorem Wf.unwk_b {Γ Δ} {ρ : ℕ → ℕ}
  (hρ : List.IsWk Γ Δ ρ) (hρ' : BoundedFrom Δ.length Γ.length ρ)
  {t : Term τ} {A} (h : Wf Γ (t.wk ρ) A) : Wf Δ t A := unwk_f ρ h (t.fvi_bounded_from_f ρ h.fvi)

theorem Wf.unwk_bf {Γ Δ} (ρ : ℕ → ℕ)
  [hρ : List.IsWk Γ Δ ρ] [hρ' : BoundedFrom Δ.length Γ.length ρ]
  {t : Term τ} {A} (h : Wf Γ (t.wk ρ) A) : Wf Δ t A := h.unwk_b hρ hρ'

theorem Wf.wk_iff {Γ Δ} {ρ : ℕ → ℕ}
  (hρ : List.IsWk Γ Δ ρ) (hρ' : BoundedFrom Δ.length Γ.length ρ)
  (t : Term τ) (A) : Wf Γ (t.wk ρ) A ↔ Wf Δ t A := ⟨λh => h.unwk_b hρ hρ', λh => h.wk hρ⟩

theorem Wf.wk_iff_f {Γ Δ} (ρ : ℕ → ℕ)
  [hρ : List.IsWk Γ Δ ρ] [hρ' : BoundedFrom Δ.length Γ.length ρ]
  (t : Term τ) (A) : Wf Γ (t.wk ρ) A ↔ Wf Δ t A := wk_iff hρ hρ' t A

theorem Wf.wk0 {Γ} {t : Term τ} {A B}
  (h : Wf Γ t A) : Wf (B::Γ) (wk0 t) A := h.wk_f .succ

theorem Wf.unwk0 {Γ} {t : Term τ} {A B}
  (h : Wf (B::Γ) (wk0 t) A) : Wf Γ t A := h.unwk_bf .succ

theorem Wf.wk0_iff {Γ} {t : Term τ} {A B}
  : Wf (B::Γ) (wk0 t) A ↔ Wf Γ t A := wk_iff_f .succ t A

theorem Wf.wk1 {Γ} {t : Term τ} {A B C}
  (h : Wf (C::Γ) t A) : Wf (C::B::Γ) (wk1 t) A := h.wk_f (Nat.liftWk .succ)

theorem Wf.unwk1 {Γ} {t : Term τ} {A B C}
  (h : Wf (C::B::Γ) (wk1 t) A) : Wf (C::Γ) t A := h.unwk_bf (Nat.liftWk .succ)

theorem Wf.wk1_iff {Γ} {t : Term τ} {A B C}
  : Wf (C::B::Γ) (wk1 t) A ↔ Wf (C::Γ) t A := wk_iff_f (Nat.liftWk .succ) t A

-- TODO: make this a class?
-- TODO: "strict Wf" where everything past Δ.length is .invalid?
def Subst.Wf (Γ : List (Ty τ)) (σ : Subst τ) (Δ : List (Ty τ)) : Prop
  := ∀i, (h : i < Δ.length) → Term.Wf Γ (σ i) (Δ[i])

theorem Subst.Wf.of_eq_on {Γ σ σ' Δ}
  (hσ' : (Set.Iio Δ.length).EqOn σ σ') (hσ : Subst.Wf (τ := τ) Γ σ (Δ)) : Subst.Wf Γ σ' Δ
  := λi h => hσ' h ▸ hσ i h

theorem Subst.Wf.eq_on_iff {Γ σ σ' Δ}
  (hσ' : (Set.Iio Δ.length).EqOn σ σ') : Subst.Wf (τ := τ) Γ σ Δ ↔ Subst.Wf Γ σ' Δ
  := ⟨λh => h.of_eq_on hσ', λh => h.of_eq_on hσ'.symm⟩

@[simp]
theorem Subst.Wf.nil {Γ} : Subst.Wf (τ := τ) Γ σ [] := by simp [Subst.Wf]

theorem Subst.Wf.head {Γ σ Δ A} (h : Subst.Wf (τ := τ) Γ σ (A::Δ)) : Term.Wf Γ (σ 0) A
  := h 0 (by simp)

theorem Subst.Wf.tail {Γ σ Δ A} (h : Subst.Wf (τ := τ) Γ σ (A::Δ)) : Subst.Wf Γ (σ ∘ .succ) Δ
  := λi hi => h i.succ (by simp [hi])

theorem Subst.Wf.cons {Γ a A σ Δ} (ha : Term.Wf Γ a A) (hσ : Subst.Wf Γ σ Δ)
  : Subst.Wf (τ := τ) Γ (σ.cons a) (A::Δ) := λi hi => by
  cases i with
  | zero => exact ha
  | succ i => exact hσ i (by convert hi using 0; simp)

theorem Subst.Wf.cons' {Γ σ Δ A} (ha : Term.Wf Γ (σ 0) A) (hσ : Subst.Wf Γ σ.tail Δ)
  : Subst.Wf (τ := τ) Γ σ (A::Δ) := by convert cons ha hσ using 1; funext n; cases n <;> rfl

theorem Subst.Wf.cons_iff {Γ σ Δ A}
  : Subst.Wf (τ := τ) Γ σ (A::Δ) ↔ Term.Wf Γ (σ 0) A ∧ Subst.Wf Γ σ.tail Δ :=
  ⟨λh => ⟨h.head, h.tail⟩, λ⟨h, h'⟩ => h'.cons' h⟩

theorem Subst.Wf.lift {Γ σ Δ} (h : Subst.Wf (τ := τ) Γ σ Δ) : Subst.Wf (A::Γ) (σ.lift) (A::Δ)
  := λi hi => by cases i with
  | zero => constructor <;> simp
  | succ i => simp [(h i (by convert hi using 0; simp)).wk0]

theorem Subst.Wf.lift' {Γ σ Δ A B} (h : Subst.Wf (τ := τ) Γ σ Δ) (he : A = B)
  : Subst.Wf (A::Γ) (σ.lift) (B::Δ) := he ▸ h.lift

theorem Subst.Wf.lift_head {Γ} {σ : Subst τ} {Δ} (h : Subst.Wf (A::Γ) (σ.lift) (B::Δ))
  : A = B := by cases h 0 (by simp); assumption

theorem Subst.Wf.lift_tail {Γ σ Δ} (h : Subst.Wf (A::Γ) (σ.lift) (B::Δ)) : Subst.Wf (τ := τ) Γ σ Δ
  := λi hi => (h (i + 1) (Nat.succ_lt_succ hi)).unwk0

theorem Subst.Wf.lift_iff {Γ σ Δ}
  : Subst.Wf (A::Γ) (σ.lift) (B::Δ) ↔ A = B ∧ Subst.Wf (τ := τ) Γ σ Δ
  := ⟨λh => ⟨h.lift_head, h.lift_tail⟩, λ⟨he, h⟩ => h.lift' he⟩

theorem Subst.Wf.wkIn {Γ' Γ Δ} {ρ : ℕ → ℕ} (hρ : List.IsWk Γ' Γ ρ) {σ : Subst τ}
  (h : Subst.Wf Γ σ Δ) : Subst.Wf Γ' (σ.wkIn ρ) Δ := λi hi => (h i hi).wk hρ

theorem Subst.Wf.wkIn_f {Γ' Γ Δ} (ρ : ℕ → ℕ) [hρ : List.IsWk Γ' Γ ρ] {σ : Subst τ}
  (h : Subst.Wf Γ σ Δ) : Subst.Wf Γ' (σ.wkIn ρ) Δ := h.wkIn hρ

theorem Subst.Wf.wkOut {Γ Δ Δ'} {ρ : ℕ → ℕ} (hρ : List.IsWk Δ Δ' ρ) {σ : Subst τ}
  (h : Subst.Wf Γ σ Δ) : Subst.Wf Γ (σ.wkOut ρ) Δ'
  := λi hi => hρ.getElem_eq i hi ▸ h (ρ i) (hρ.bounded_on i hi)

theorem Subst.Wf.wkOut_f {Γ Δ Δ'} (ρ : ℕ → ℕ) [hρ : List.IsWk Δ Δ' ρ] {σ : Subst τ}
  (h : Subst.Wf Γ σ Δ) : Subst.Wf Γ (σ.wkOut ρ) Δ' := h.wkOut hρ

theorem Wf.subst {Γ σ Δ} (hσ : Subst.Wf Γ σ Δ) {t : Term τ} {A}
  (h : Term.Wf Δ t A) : Term.Wf Γ (t.subst σ) A := by induction h generalizing σ Γ with
  | var hi hA => cases hA; exact hσ _ hi
  | _ => constructor <;> apply_assumption <;> simp [Subst.Wf.lift_iff, *]

inductive LSubst.Wf : List (Ty τ) → LSubst τ → List (Ty τ) → Prop
  | nil {Γ} : LSubst.Wf Γ [] []
  | cons {Γ σ Δ A} (ha : Term.Wf Γ a A) (hσ : LSubst.Wf Γ σ Δ)
    : LSubst.Wf Γ (a::σ) (A::Δ)

theorem LSubst.Wf.head {Γ σ Δ A} (h : LSubst.Wf Γ (a::σ) (A::Δ)) : Term.Wf (τ := τ) Γ a A
  := by cases h; assumption

theorem LSubst.Wf.tail {Γ σ Δ A} (h : LSubst.Wf Γ (a::σ) (A::Δ)) : LSubst.Wf (τ := τ) Γ σ Δ
  := by cases h; assumption

theorem LSubst.Wf.cons_iff {Γ σ Δ A}
  : LSubst.Wf Γ (a::σ) (A::Δ) ↔ Term.Wf (τ := τ) Γ a A ∧ LSubst.Wf Γ σ Δ
  := ⟨λh => ⟨h.head, h.tail⟩, λ⟨h, h'⟩ => h'.cons h⟩

theorem LSubst.Wf.wkIn {Γ' Γ Δ} {ρ : ℕ → ℕ} (hρ : List.IsWk Γ' Γ ρ) {σ : LSubst τ}
  (hσ : LSubst.Wf Γ σ Δ) : LSubst.Wf Γ' (σ.wkIn ρ) Δ := by
  induction hσ with
  | nil => exact LSubst.Wf.nil
  | cons ha hσ Iσ => exact LSubst.Wf.cons (ha.wk hρ) (Iσ hρ)

theorem LSubst.Wf.wkIn_f {Γ' Γ Δ} (ρ : ℕ → ℕ) [hρ : List.IsWk Γ' Γ ρ] {σ : LSubst τ}
  (hσ : LSubst.Wf Γ σ Δ) : LSubst.Wf Γ' (σ.wkIn ρ) Δ := hσ.wkIn hρ

theorem LSubst.Wf.unwk0 {A Γ} {σ : LSubst τ} {Δ} (h : LSubst.Wf (τ := τ) (A::Γ) (σ.wkIn .succ) Δ)
  : LSubst.Wf Γ σ Δ := by induction σ generalizing Γ Δ with
  | nil => cases h; constructor
  | cons a σ Iσ => cases h; constructor; apply Term.Wf.unwk0; assumption; apply Iσ; assumption

theorem LSubst.Wf.lift {Γ σ Δ} (h : LSubst.Wf Γ σ Δ) : LSubst.Wf (τ := τ) (A::Γ) σ.lift (A::Δ)
  := (h.wkIn_f .succ).cons (.var (by simp) rfl)

theorem LSubst.Wf.lift_head {Γ} {σ : LSubst τ} {Δ A} (hσ : LSubst.Wf (A::Γ) σ.lift (B::Δ))
  : A = B := by cases hσ with | cons ha _ => cases ha; assumption

theorem LSubst.Wf.lift_tail {Γ σ Δ} (h : LSubst.Wf (τ := τ) (A::Γ) σ.lift (B::Δ))
  : LSubst.Wf Γ σ Δ := by
  induction σ generalizing A B Γ Δ with
  | nil => cases h with | cons _ h => cases h; constructor
  | cons a σ Iσ => cases h with | cons ha h => exact h.unwk0

theorem LSubst.Wf.lift_iff {Γ σ Δ}
  : LSubst.Wf (τ := τ) (A::Γ) σ.lift (B::Δ) ↔ A = B ∧ LSubst.Wf Γ σ Δ
  := ⟨λh => ⟨h.lift_head, h.lift_tail⟩, λ⟨he, h⟩ => he ▸ h.lift⟩

theorem LSubst.Wf.length {Γ σ Δ} (h : LSubst.Wf (τ := τ) Γ σ Δ) : σ.length = Δ.length := by
  induction h <;> simp [*]

theorem LSubst.Wf.var {Γ σ Δ} (hσ : LSubst.Wf (τ := τ) Γ σ Δ) : Subst.Wf Γ σ.var Δ := by
  induction hσ with
  | nil => simp
  | cons ha hσ Iσ => simp [LSubst.var_cons, Subst.Wf.cons_iff, Subst.cons, *]

theorem Wf.lsubst {Γ σ Δ} (hσ : LSubst.Wf Γ σ Δ) {t : Term τ} {A}
  (h : Term.Wf Δ t A) : Term.Wf Γ (t.lsubst σ) A := by rw [<-subst_var]; exact Wf.subst hσ.var h

theorem Subst.Wf.lsubst_of_var {Γ} {σ : LSubst τ} {Δ}
  (h : Subst.Wf (τ := τ) Γ σ.var Δ) : LSubst.Wf Γ (σ.take Δ.length) Δ := by
  induction σ generalizing Δ with
  | nil => cases Δ with
    | nil => exact LSubst.Wf.nil
    | cons => exact (h 0 (by simp)).invalid
  | cons a σ Iσ => cases Δ with
    | nil => exact LSubst.Wf.nil
    | cons =>
      constructor
      convert h 0 (by simp)
      simp [LSubst.var]
      apply Iσ
      intro i hi
      convert h (i + 1) (by simp [hi]) using 1
      simp [LSubst.var]

theorem Subst.Wf.length_le_of_var {Γ} {σ : LSubst τ} {Δ}
  (h : Subst.Wf (τ := τ) Γ σ.var Δ) : Δ.length ≤ σ.length := by
  induction σ generalizing Δ with
  | nil => cases Δ with
    | nil => rfl
    | cons => exact (h 0 (by simp)).invalid
  | cons a σ Iσ => cases Δ with
    | nil => simp
    | cons =>
      simp only [LSubst.var_cons, List.length_cons, Nat.add_le_add_iff_right] at *
      exact Iσ h.tail

theorem LSubst.Wf.iff_var {Γ σ Δ}
  : LSubst.Wf (τ := τ) Γ σ Δ ↔ σ.length = Δ.length ∧ Subst.Wf Γ σ.var Δ
  := ⟨λh => ⟨h.length, h.var⟩, λ⟨h, h'⟩ => by convert h'.lsubst_of_var; simp [h]⟩

-- TODO: Subst.Wf iff LSubst.Wf ofFn
