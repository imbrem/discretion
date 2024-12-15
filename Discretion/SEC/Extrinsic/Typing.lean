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

theorem Wf.wk {Γ Δ} {ρ : ℕ → ℕ} (hρ : List.IsRen Γ Δ ρ) {t : Term τ} {A}
  (h : Wf Δ t A) : Wf Γ (t.wk ρ) A := by
  induction h generalizing Γ ρ with
  | var hi => have h := hρ.getElem_eq _ hi; constructor; rw [h]; assumption
  | _ => constructor <;> apply_assumption

theorem Wf.wk_f {Γ Δ} (ρ : ℕ → ℕ) [hρ : List.IsRen Γ Δ ρ] {t : Term τ} {A}
  (h : Wf Δ t A) : Wf Γ (t.wk ρ) A := h.wk hρ

theorem Wf.unwk {Γ Δ} {ρ : ℕ → ℕ} (hρ : List.IsRen Γ Δ ρ) {t : Term τ} {A}
  (h : Wf Γ (t.wk ρ) A) (ht : t.fvi ≤ Δ.length) : Wf Δ t A := by
  induction t generalizing Γ Δ ρ A <;> cases h
  case var hΓ ha => apply var; rw [<-hρ.getElem_eq _ ht, ha]
  all_goals {
    simp [fvi] at ht
    constructor
    all_goals {
      apply_assumption
      <;> (repeat apply λhρ => List.IsRen.lift (hρ := hρ))
      <;> first | assumption | ((try simp only [List.length_cons]); omega)
    }
  }

theorem Wf.unwk_f {Γ Δ} (ρ : ℕ → ℕ) [hρ : List.IsRen Γ Δ ρ] {t : Term τ} {A}
  (h : Wf Γ (t.wk ρ) A) (ht : t.fvi ≤ Δ.length) : Wf Δ t A := h.unwk hρ ht

theorem Wf.fvi {Γ} {t : Term τ} {A} (h : Wf Γ t A) : t.fvi ≤ Γ.length := by
  induction h <;> simp [Term.fvi] at * <;> omega

theorem Wf.unwk_b {Γ Δ} {ρ : ℕ → ℕ}
  (hρ : List.IsRen Γ Δ ρ) (hρ' : BoundedFrom Δ.length Γ.length ρ)
  {t : Term τ} {A} (h : Wf Γ (t.wk ρ) A) : Wf Δ t A := unwk_f ρ h (t.fvi_bounded_from_f ρ h.fvi)

theorem Wf.unwk_bf {Γ Δ} (ρ : ℕ → ℕ)
  [hρ : List.IsRen Γ Δ ρ] [hρ' : BoundedFrom Δ.length Γ.length ρ]
  {t : Term τ} {A} (h : Wf Γ (t.wk ρ) A) : Wf Δ t A := h.unwk_b hρ hρ'

theorem Wf.wk_iff {Γ Δ} {ρ : ℕ → ℕ}
  (hρ : List.IsRen Γ Δ ρ) (hρ' : BoundedFrom Δ.length Γ.length ρ)
  (t : Term τ) (A) : Wf Γ (t.wk ρ) A ↔ Wf Δ t A := ⟨λh => h.unwk_b hρ hρ', λh => h.wk hρ⟩

theorem Wf.wk_iff_f {Γ Δ} (ρ : ℕ → ℕ)
  [hρ : List.IsRen Γ Δ ρ] [hρ' : BoundedFrom Δ.length Γ.length ρ]
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

inductive WfqD : (Γ : List (Ty τ)) → Vector' EQuant Γ.length → Term τ → Ty τ → Type _
  | var {Γ qs i A} : Γ.QVar qs i A → WfqD Γ qs (.var i) A
  | op {Γ qs f a A B} (hA : f.src = A) (hB : f.trg = B) : WfqD Γ qs a A → WfqD Γ qs (.op f a) B
  | let₁ {Γ} {ql qr qs : Vector' EQuant Γ.length} {a b A B}
    : ql + qr ≤ qs → WfqD Γ ql a A → WfqD (A::Γ) (qr.cons (quant A)) b B → WfqD Γ qs (.let₁ a b) B
  | unit {Γ qs} : 0 ≤ qs → WfqD Γ qs .unit (𝟙_ _)
  | pair {Γ} {ql qr qs : Vector' EQuant Γ.length} {a b A B}
    : ql + qr ≤ qs → WfqD Γ ql a A → WfqD Γ qr b B → WfqD Γ qs (.pair a b) (A ⊗ B)
  | let₂ {Γ} {ql qr qs : Vector' EQuant Γ.length} {a c A B C}
    : ql + qr ≤ qs
    → WfqD Γ ql a (A ⊗ B)
    → WfqD (B::A::Γ) ((qr.cons ↑(quant A)).cons ↑(quant B)) c C
    → WfqD Γ qs (.let₂ a c) C

open BoundedOn

def WfqD.wk {Γ Δ qΓ qΔ} {ρ : ℕ → ℕ} (hρ : List.IsQRen qΓ qΔ ρ) {t : Term τ} {A}
  (h : WfqD Δ qΔ t A) : WfqD Γ qΓ (t.wk ρ) A := match h with
  | .var h => .var (h.wk hρ)
  | .op hA hB h => .op hA hB (h.wk hρ)
  | .let₁ hq ha hb =>
    .let₁
      (le_pvSum_of_le_sum _ _ ρ _ _ _ _ hq hρ.quant_le_sum)
      (ha.wk (List.IsQRen.of_pvSum _ _ _))
      (hb.wk ((List.IsQRen.of_pvSum _ _ _).lift _ _))
  | .unit h => .unit (hρ.le_zero _ _ _ h)
  | .pair hq ha hb =>
    .pair
      (le_pvSum_of_le_sum _ _ ρ _ _ _ _ hq hρ.quant_le_sum)
      (ha.wk (List.IsQRen.of_pvSum _ _ _))
      (hb.wk (List.IsQRen.of_pvSum _ _ _))
  | let₂ hq ha hb =>
    .let₂
      (le_pvSum_of_le_sum _ _ ρ _ _ _ _ hq hρ.quant_le_sum)
      (ha.wk (List.IsQRen.of_pvSum _ _ _))
      (hb.wk (((List.IsQRen.of_pvSum _ _ _).lift _ _).lift _ _))

-- TODO: inductive version with better defeq?
def WfqD.mono {Γ qΓ qΓ'} (hqΓ : qΓ ≤ qΓ') (h : WfqD (τ := τ) Γ qΓ a A) : WfqD Γ qΓ' a A
  := by convert h.wk (List.IsQRen.id_of_le hqΓ); simp [Term.wk_id]

inductive Wfq : (Γ : List (Ty τ)) → Vector' EQuant Γ.length → Term τ → Ty τ → Prop
  | var {Γ qs i A} : Γ.QVar qs i A → Wfq Γ qs (.var i) A
  | op {Γ qs f a A B} (hA : f.src = A) (hB : f.trg = B) : Wfq Γ qs a A → Wfq Γ qs (.op f a) B
  | let₁ {Γ} {ql qr qs : Vector' EQuant Γ.length} {a b A B}
    : ql + qr ≤ qs → Wfq Γ ql a A → Wfq (A::Γ) (qr.cons (quant A)) b B → Wfq Γ qs (.let₁ a b) B
  | unit {Γ qs} : 0 ≤ qs → Wfq Γ qs .unit (𝟙_ _)
  | pair {Γ} {ql qr qs : Vector' EQuant Γ.length} {a b A B}
    : ql + qr ≤ qs → Wfq Γ ql a A → Wfq Γ qr b B → Wfq Γ qs (.pair a b) (A ⊗ B)
  | let₂ {Γ} {ql qr qs : Vector' EQuant Γ.length} {a c A B C}
    : ql + qr ≤ qs
    → Wfq Γ ql a (A ⊗ B)
    → Wfq (B::A::Γ) ((qr.cons ↑(quant A)).cons ↑(quant B)) c C
    → Wfq Γ qs (.let₂ a c) C

theorem Wfq.var_iff {Γ qs i A}
  : Wfq (τ := τ) Γ qs (.var i) A ↔ Γ.QVar qs i A := ⟨λ | .var h => h, .var⟩

theorem Wfq.op_iff {Γ qs f a B}
  : Wfq (τ := τ) Γ qs (.op f a) B ↔ f.trg = B ∧ Wfq Γ qs a f.src := ⟨
    λ| .op hA hB ha => by cases hA; exact ⟨hB, ha⟩,
    λ ⟨hB, ha⟩ => .op rfl hB ha
  ⟩

theorem Wfq.let₁_iff {Γ qs a b B}
  : Wfq (τ := τ) Γ qs (.let₁ a b) B
  ↔ ∃ql qr A, ql + qr ≤ qs ∧ Wfq Γ ql a A ∧ Wfq (A::Γ) (qr.cons (quant A)) b B := ⟨
    λ| .let₁ h ha hb => ⟨_, _, _, h, ha, hb⟩,
    λ⟨_, _, _, h, ha, hb⟩ => .let₁ h ha hb
  ⟩

theorem Wfq.unit_iff {Γ qs A}
  : Wfq (τ := τ) Γ qs .unit A ↔ 0 ≤ qs ∧ A = (𝟙_ _)
  := ⟨λ| .unit h => ⟨h, rfl⟩, λ⟨h, h'⟩ => h' ▸ .unit h⟩

theorem Wfq.pair_iff {Γ qs a b C}
  : Wfq (τ := τ) Γ qs (.pair a b) C
  ↔ ∃ql qr A B, ql + qr ≤ qs ∧ Wfq Γ ql a A ∧ Wfq Γ qr b B ∧ C = A ⊗ B := ⟨
    λ| .pair h ha hb => ⟨_, _, _, _, h, ha, hb, rfl⟩,
    λ⟨_, _, _, _, h, ha, hb, hC⟩ => hC ▸ .pair h ha hb
  ⟩

theorem Wfq.let₂_iff {Γ qs a c C}
  : Wfq (τ := τ) Γ qs (.let₂ a c) C
  ↔ ∃ql qr A B, ql + qr ≤ qs ∧ Wfq Γ ql a (A ⊗ B)
    ∧ Wfq (B::A::Γ) ((qr.cons ↑(quant A)).cons ↑(quant B)) c C := ⟨
    λ| .let₂ h ha hb => ⟨_, _, _, _, h, ha, hb⟩,
    λ⟨_, _, _, _, h, ha, hb⟩ => .let₂ h ha hb
  ⟩

-- Nonempty WfqD ↔ Wfq

inductive WqD : (Γ : List (Ty τ)) → Vector' EQuant Γ.length → Term τ → Sort _
  | var {Γ qs i} (hi : i < Γ.length) : qs.Var i → WqD Γ qs (.var i)
  | op {Γ qs f a} : WqD Γ qs a → WqD Γ qs (.op f a)
  | let₁ {Γ} {ql qr qs : Vector' EQuant Γ.length} {a b}
    : ql + qr ≤ qs → WqD Γ ql a
      → WqD ((inferTy Γ a)::Γ) (qr.cons (quant (inferTy Γ a))) b
      → WqD Γ qs (.let₁ a b)
  | unit {Γ qs} : 0 ≤ qs → WqD Γ qs .unit
  | pair {Γ} {ql qr qs : Vector' EQuant Γ.length} {a b}
    : ql + qr ≤ qs → WqD Γ ql a → WqD Γ qr b → WqD Γ qs (.pair a b)
  | let₂ {Γ} {ql qr qs : Vector' EQuant Γ.length} {a c}
    : ql + qr ≤ qs
    → WqD Γ ql a
    → WqD ((inferLeft Γ a)::(inferRight Γ a)::Γ)
          ((qr.cons ↑(quant (inferRight Γ a))).cons ↑(quant (inferLeft Γ a)))
          c
    → WqD Γ qs (.let₂ a c)


-- TODO: WfqD → Wf

-- TODO: WfqD ↪ WqD

-- TODO: { WqD | Wf } ↪ WfqD ==> { WqD | Wf } ≅ WfqD

inductive WfqM : (Γ : List (Ty τ)) → Vector' EQuant Γ.length → Term τ → Ty τ → Prop
  | var {Γ qs i A} (hi : i < Γ.length)
    : Γ[i] = A ∧ qs = Vector'.oneHot ⟨i, hi⟩ 1 → WfqM Γ qs (.var i) A
  | op {Γ qs f a A B} (hA : f.src = A) (hB : f.trg = B) : WfqM Γ qs a A → WfqM Γ qs (.op f a) B
  | let₁ {Γ} {qs qs' : Vector' EQuant Γ.length} {qA a b A B}
    : WfqM Γ qs a A → qA = ↑(quant A)
    → WfqM (A::Γ) (qs'.cons qA) b B → WfqM Γ (qs + qs') (.let₁ a b) B
  | unit {Γ qs} : qs = 0 → WfqM Γ qs .unit (𝟙_ _)
  | pair {Γ} {qs qs' : Vector' EQuant Γ.length} {a b A B}
    : WfqM Γ qs a A → WfqM Γ qs' b B → WfqM Γ (qs + qs') (.pair a b) (A ⊗ B)
  | let₂ {Γ} {qs qs' : Vector' EQuant Γ.length} {qA qB a c A B C} : WfqM Γ qs a (A ⊗ B)
    → qA = ↑(quant A) → qB = ↑(quant B)
    → WfqM (B::A::Γ) ((qs.cons qA).cons qB) c C
    → WfqM Γ (qs + qs') (.let₂ a c) C

-- TODO: WfqM has a unique quantity q

-- TODO: Nonempty (WfqD qs) iff Wfq qs iff WfqM qs' and qs' ≤ qs

-- TODO: Wfq ==> Wf (and therefore WfqM, WfqD, etc...)

-- TODO: Wq/WqM using inferTy; WqM iff Wq and

section Effect

variable {ε} [EffectSignature τ ε] [PartialOrder ε]

inductive WeL : (Γ : List ε) → Term τ → ε → Prop
  | var {Γ i e} (hi : i < Γ.length) : Γ[i] ≤ e → WeL Γ (.var i) e
  | op {Γ f a e} : f.eff ≤ e → WeL Γ a e → WeL Γ (.op f a) e
  | let₁ {Γ a b e} : WeL Γ a e → WeL (e::Γ) b e → WeL Γ (.let₁ a b) e
  | unit {Γ} : WeL Γ .unit e
  | pair {Γ a b e} : WeL Γ a e → WeL Γ b e → WeL Γ (.pair a b) e
  | let₂ {Γ a c e} : WeL Γ a e → WeL (e::e::Γ) c e → WeL Γ (.let₂ a c) e

end Effect
