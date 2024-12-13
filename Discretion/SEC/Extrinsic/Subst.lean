import Discretion.SEC.Extrinsic.Typing

namespace SEC

open FreeSignature

namespace Term

variable {τ} [FreeSignature τ]

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

theorem Subst.Wf.wkIn {Γ' Γ Δ} {ρ : ℕ → ℕ} (hρ : List.IsRen Γ' Γ ρ) {σ : Subst τ}
  (h : Subst.Wf Γ σ Δ) : Subst.Wf Γ' (σ.wkIn ρ) Δ := λi hi => (h i hi).wk hρ

theorem Subst.Wf.wkIn_f {Γ' Γ Δ} (ρ : ℕ → ℕ) [hρ : List.IsRen Γ' Γ ρ] {σ : Subst τ}
  (h : Subst.Wf Γ σ Δ) : Subst.Wf Γ' (σ.wkIn ρ) Δ := h.wkIn hρ

theorem Subst.Wf.wkOut {Γ Δ Δ'} {ρ : ℕ → ℕ} (hρ : List.IsRen Δ Δ' ρ) {σ : Subst τ}
  (h : Subst.Wf Γ σ Δ) : Subst.Wf Γ (σ.wkOut ρ) Δ'
  := λi hi => hρ.getElem_eq i hi ▸ h (ρ i) (hρ.bounded_on i hi)

theorem Subst.Wf.wkOut_f {Γ Δ Δ'} (ρ : ℕ → ℕ) [hρ : List.IsRen Δ Δ' ρ] {σ : Subst τ}
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

theorem LSubst.Wf.wkIn {Γ' Γ Δ} {ρ : ℕ → ℕ} (hρ : List.IsRen Γ' Γ ρ) {σ : LSubst τ}
  (hσ : LSubst.Wf Γ σ Δ) : LSubst.Wf Γ' (σ.wkIn ρ) Δ := by
  induction hσ with
  | nil => exact LSubst.Wf.nil
  | cons ha hσ Iσ => exact LSubst.Wf.cons (ha.wk hρ) (Iσ hρ)

theorem LSubst.Wf.wkIn_f {Γ' Γ Δ} (ρ : ℕ → ℕ) [hρ : List.IsRen Γ' Γ ρ] {σ : LSubst τ}
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
