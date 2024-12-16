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
      exact h 0 (by simp)
      apply Iσ
      intro i hi
      exact h (i + 1) (by simp [hi])

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

inductive LSubst.WfqD
  : (Γ : List (Ty τ)) → Vector' EQuant Γ.length
    → LSubst τ → (Δ : List (Ty τ)) → Vector' EQuant Δ.length → Type _
  | nil {Γ qs} : 0 ≤ qs → LSubst.WfqD Γ qs [] [] .nil
  | cons {Γ qa qΓ qaΓ σ Δ qΔ qaΔ A}
    (hq : qa + qΓ ≤ qaΓ)
    (hqa : ∀i, qaΔ ≤ qa.get i)
    (ha : 1 ≤ qaΔ → Term.WfqD Γ qa a A)
    (hσ : LSubst.WfqD Γ qΓ σ Δ qΔ)
    : LSubst.WfqD Γ qaΓ (a::σ) (A::Δ) (qΔ.cons qaΔ)

def LSubst.WfqD.mono
  {Γ qΓ qΓ' Δ qΔ qΔ'} (hqΓ : qΓ ≤ qΓ') (hqΔ : qΔ' ≤ qΔ) {σ} (hσ : WfqD (τ := τ) Γ qΓ σ Δ qΔ)
  : WfqD (τ := τ) Γ qΓ' σ Δ qΔ' := match Δ, qΔ, qΔ', hqΔ, hσ with
  | [], .nil, .nil, _, .nil h => .nil (le_trans h hqΓ)
  | _::_, _, .cons _ _, h, .cons hq hqa ha hσ =>
    .cons (le_trans hq hqΓ)
          (λi => le_trans h.head (hqa i))
          (λh' => ha (le_trans h' h.head))
          (hσ.mono (le_refl _) h.tail)

theorem LSubst.WfqD.zero_le
  {Γ qΓ σ Δ qΔ} (hσ : LSubst.WfqD (τ := τ) Γ qΓ σ Δ qΔ) (hΔ : 0 ≤ qΔ) : 0 ≤ qΓ
  := by induction hσ with
  | nil => assumption
  | cons hq hqa _ _ I =>
    apply le_trans _ hq
    convert le_trans (add_le_add_left (I hΔ.tail) (0 : Vector' EQuant _)) _
    simp
    apply add_le_add_right
    exact Vector'.le_of_get_le (λi => by convert (le_trans hΔ.head (hqa i)); simp)

def LSubst.WfqD.var
  {Γ qΓ σ Δ qΔ} (hσ : WfqD (τ := τ) Γ qΓ σ Δ qΔ)
  {A} (hA : Δ.QVar qΔ i A) : Term.WfqD Γ qΓ (σ.var i) A
  := match i, hσ with
  | _, .nil _ => by have h := hA.is_lt; simp at h
  | 0, .cons hq _ ha hσ => hA.ty_eq ▸ (ha hA.use).mono
    (by convert le_trans (add_le_add_left (hσ.zero_le hA.zero_tail) _) hq; simp)
  | i + 1, .cons (qa := qa) (qΓ := qΓ') hq hqa _ hσ => (hσ.var (i := i) hA.succ_tail).mono
    (by
      have hz : 0 ≤ qa := Vector'.le_of_get_le (λi =>
        le_trans (by convert hA.select (0 : Fin (_ + 1)) (by simp); simp) (hqa i))
      convert le_trans (add_le_add_right hz qΓ') hq; simp
    )

structure LSubst.WfqD.Split (Γ : List (Ty τ)) (qΓ) (σ) (Δ) (qΔl qΔr) where
  (qΓl qΓr : Vector' EQuant Γ.length)
  (hσl : WfqD Γ qΓl σ Δ qΔl)
  (hσr : WfqD Γ qΓr σ Δ qΔr)
  (hlr : qΓl + qΓr ≤ qΓ)

-- def LSubst.WfqD.split {Γ qΓ σ Δ qΔl qΔr qΔ} (hqs : qΔl + qΔr ≤ qΔ) (hσ : WfqD (τ := τ) Γ qΓ σ Δ qΔ)
--   : Split Γ qΓ σ Δ qΔl qΔr := match Δ, qΔl, qΔr, qΔ, hσ with
--   | [], .nil, .nil, .nil, .nil hΓ => ⟨0, 0, .nil (le_refl _), .nil (le_refl _), by convert hΓ; simp⟩
--   | _::_, .cons ql qΔl, .cons qr qΔr, .cons qhΔ qΔ, .cons (qΓ := qΓt) (qa := qa) hq hqa ha hσ =>
--     let st := hσ.split hqs.tail;
--     match ql, qr with
--     | 0, 0 => ⟨st.qΓl, st.qΓr,
--         .cons (qa := 0) (by simp) (by simp) (λh => by simp at h) st.hσl,
--         .cons (qa := 0) (by simp) (by simp) (λh => by simp at h) st.hσr,
--         by
--           have ha : 0 ≤ qa :=
--             Vector'.le_of_get_le (λi => le_trans (by convert hqs.head; simp) (hqa i))
--           apply le_trans st.hlr
--           convert le_trans (add_le_add_right ha qΓt) hq
--           simp
--       ⟩
--     | (ql : Quant), 0 => ⟨qa + st.qΓl, st.qΓr,
--         .cons (qa := qa) (by simp)
--           (λi => le_trans hqs.head (hqa i))
--           (λh => ha (le_trans (by simp) hqs.head)) st.hσl,
--         .cons (qa := 0) (by simp) (by simp) (λh => by simp at h) st.hσr,
--         by
--           rw [add_assoc]
--           apply le_trans _ hq
--           apply add_le_add_left
--           exact st.hlr
--       ⟩
--     | 0, (qr : Quant) => ⟨st.qΓl, qa + st.qΓr,
--         .cons (qa := 0) (by simp) (by simp) (λh => by simp at h) st.hσl,
--         .cons (qa := qa) (by simp)
--           (λi => le_trans hqs.head (hqa i))
--           (λh => ha (le_trans (by simp) hqs.head))
--           st.hσr,
--         by
--           rw [add_comm, add_assoc, add_comm (a := st.qΓr)]
--           apply le_trans _ hq
--           apply add_le_add_left
--           exact st.hlr
--       ⟩
--     | (ql : Quant), (qr : Quant) =>
--       have hqlr : ql + qr ≤ qhΔ := hqs.head;
--       have hqa2 : qa + qa = qa := Vector'.get_injective (by
--         ext i; rw [Vector'.get_add_apply]; apply EQuant.add_idem_of_add_coe_le;
--         exact le_trans hqlr (hqa i)
--       );
--       have hqhΔ : qhΔ + qhΔ = qhΔ := EQuant.add_idem_of_add_coe_le hqlr;
--       ⟨qa + st.qΓl, qa + st.qΓr,
--         .cons (qa := qa) (by simp) sorry sorry st.hσl,
--         .cons (qa := qa) (by simp) sorry sorry st.hσr,
--         by
--           rw [add_assoc, add_comm (a := st.qΓl), <-add_assoc, <-add_assoc, hqa2, add_assoc]
--           apply le_trans _ hq
--           apply add_le_add_left
--           rw [add_comm]
--           exact st.hlr
--       ⟩

-- -- theorem LSubst.WfqD.split_le {Γ ql qr qΓ σ Δ qΔ} (hq : ql + qr ≤ qΓ) (hσ : WfqD (τ := τ) Γ qΓ σ Δ qΔ)
-- --   : (hσ.split hq).1 + (hσ.split hq).2.1 ≤ qΔ
-- --   := sorry

-- def WfqD.lsubst {Γ qΓ σ Δ qΔ} (hσ : LSubst.WfqD (τ := τ) Γ qΓ σ Δ qΔ) {a A}
--   : WfqD Δ qΔ a A → WfqD Γ qΓ (a.lsubst σ) A
--   | .var h => (hσ.var h)
--   | .op hA hB ha => .op hA hB (ha.lsubst hσ)
--   | .let₁ hq ha hb =>
--     sorry
--   | .unit h => .unit (hσ.zero_le h)
--   | .pair hq ha hb => sorry
--   | .let₂ hq ha hb => sorry
