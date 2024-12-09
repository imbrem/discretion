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

inductive Wf : List (Ty τ) → Term τ → Ty τ → Prop
  | var {Γ i A} (hΓ : i < Γ.length) : Γ[i] = A → Wf Γ (.var i) A
  | op {Γ f a A B} (hA : f.src = A) (hB : f.trg = B) : Wf Γ a A → Wf Γ (.op f a) B
  | let₁ {Γ a b A B} : Wf Γ a A → Wf (A::Γ) b B → Wf Γ (.let₁ a b) B
  | unit {Γ} : Wf Γ .unit (𝟙_ _)
  | pair {Γ a b A B} : Wf Γ a A → Wf Γ b B → Wf Γ (.pair a b) (A ⊗ B)
  | let₂ {Γ a c A B C} : Wf Γ a (A ⊗ B) → Wf (B::A::Γ) c C → Wf Γ (.let₂ a c) C

def inferTy (Γ : List (Ty τ)) : Term τ → Ty τ
  | .var i => if h : i < Γ.length then Γ[i] else .unit
  | .op f a => f.trg
  | .let₁ a b => b.inferTy ((a.inferTy Γ)::Γ)
  | .unit => .unit
  | .pair a b => a.inferTy Γ ⊗ b.inferTy Γ
  | .let₂ a b => match a.inferTy Γ with
    | .tensor A B => b.inferTy (B::A::Γ)
    | _ => .unit

theorem Wf.inferTy_eq {τ} [FreeSignature τ] {Γ} {t : Term τ} {A} (hA : Wf Γ t A)
  : t.inferTy Γ = A := by induction hA <;> simp [inferTy, *]

theorem Wf.unique {τ} [FreeSignature τ] {Γ} {t : Term τ} {A B}
  (hA : Wf Γ t A) (hB : Wf Γ t B) : A = B := by rw [<-hA.inferTy_eq, <-hB.inferTy_eq]

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

theorem Wf.wk {τ} [FreeSignature τ] {Γ Δ} {ρ : ℕ → ℕ} (h : Γ.IsWk Δ ρ) {t : Term τ} {A}
  (h : Wf Δ t A) : Wf Γ (t.wk ρ) A := by
  induction h generalizing Γ ρ with
  | var hi => have h := h _ hi; constructor; rw [h.2]; assumption
  | _ => constructor <;> apply_assumption <;> simp [List.IsWk.lift_iff, *]

-- TODO: this only works for ρ injective...
-- theorem Wf.unwk  {τ} [FreeSignature τ] {Γ Δ} {ρ : ℕ → ℕ} (h : Γ.IsWk Δ ρ) {t : Term τ} {A}
--   (h : Wf Γ (t.wk ρ) A) : Wf Δ t A := by
--   induction t generalizing Γ Δ ρ A <;> cases h
--   case var hΓ ha => sorry
--   all_goals (constructor <;> apply_assumption <;> assumption)

theorem Wf.wk0 {τ} [FreeSignature τ] {Γ} {t : Term τ} {A B}
  (h : Wf Γ t A) : Wf (B::Γ) (wk0 t) A := h.wk (by simp)

def Subst.Wf (Γ : List (Ty τ)) (σ : Subst τ) (Δ : List (Ty τ)) : Prop
  := ∀i, (h : i < Δ.length) → Term.Wf Γ (σ i) (Δ[i])

@[simp]
theorem Subst.Wf.nil {Γ} : Subst.Wf (τ := τ) Γ σ [] := by simp [Subst.Wf]

theorem Subst.Wf.head {Γ σ Δ A} (h : Subst.Wf (τ := τ) Γ σ (A::Δ)) : Term.Wf Γ (σ 0) A
  := h 0 (by simp)

theorem Subst.Wf.tail {Γ σ Δ A} (h : Subst.Wf (τ := τ) Γ σ (A::Δ)) : Subst.Wf Γ (σ ∘ .succ) Δ
  := λi hi => h i.succ (by simp [hi])

theorem Subst.Wf.cons {Γ a A σ Δ} (ha : Term.Wf Γ a A) (hσ : Subst.Wf Γ σ Δ)
  : Subst.Wf (τ := τ) Γ (λn => Nat.casesOn n a σ) (A::Δ) := λi hi => by
  cases i with
  | zero => exact ha
  | succ i => exact hσ i (by convert hi using 0; simp)

theorem Subst.Wf.cons' {Γ σ Δ A} (ha : Term.Wf Γ (σ 0) A) (hσ : Subst.Wf Γ (σ ∘ .succ) Δ)
  : Subst.Wf (τ := τ) Γ σ (A::Δ) := by convert cons ha hσ using 1; funext n; cases n <;> rfl

theorem Subst.Wf.cons_iff {Γ σ Δ A}
  : Subst.Wf (τ := τ) Γ σ (A::Δ) ↔ Term.Wf Γ (σ 0) A ∧ Subst.Wf Γ (σ ∘ .succ) Δ :=
  ⟨λh => ⟨h.head, h.tail⟩, λ⟨h, h'⟩ => h'.cons' h⟩

theorem Subst.Wf.lift {Γ σ Δ} (h : Subst.Wf (τ := τ) Γ σ Δ) : Subst.Wf (A::Γ) (σ.lift) (A::Δ)
  := λi hi => by cases i with
  | zero => constructor <;> simp
  | succ i => simp [(h i (by convert hi using 0; simp)).wk0]

-- theorem Subst.Wf.lift_tail {Γ σ Δ} (h : Subst.Wf (A::Γ) (σ.lift) (A::Δ)) : Subst.Wf (τ := τ) Γ σ Δ
--   := λi hi => sorry

inductive LSubst.Wf : List (Ty τ) → LSubst τ → List (Ty τ) → Prop
  | nil {Γ} : LSubst.Wf Γ [] []
  | cons {Γ σ Δ A} (ha : Term.Wf Γ a A) (hσ : LSubst.Wf Γ σ Δ)
    : LSubst.Wf Γ (a::σ) (A::Δ)

-- TODO: LSubst.Wf iff Subst.Wf var

-- TODO: Subst.Wf iff LSubst.Wf ofFn
