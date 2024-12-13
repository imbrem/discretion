import Discretion.SEC.Extrinsic.Typing
import Discretion.PER.Basic

open CategoryTheory

open CategoryTheory.MonoidalCategory

namespace SEC

open FreeSignature

namespace Term

variable {τ} [FreeSignature τ]

inductive Congr (P : (Γ : List (Ty τ)) → Vector' EQuant Γ.length → Ty τ → Term τ → Term τ → Prop)
  : (Γ : List (Ty τ)) → Vector' EQuant Γ.length → Ty τ → Term τ → Term τ → Prop
  | refl {Γ qs a A} : WfqD Γ qs a A → Congr P Γ qs A a a
  | op {Γ qs f a a' A B} (hA : f.src = A) (hB : f.trg = B) : Congr P Γ qs A a a'
    → Congr P Γ qs B (.op f a) (.op f a')
  | let₁ {Γ ql qr qs a a' b b' A B} :
    ql + qr ≤ qs → Congr P Γ ql A a a' → Congr P (A::Γ) (qr.cons (quant A)) B b b'
    → Congr P Γ qs B (.let₁ a b) (.let₁ a' b')
  | pair {Γ ql qr qs a b a' b' A B} :
    ql + qr ≤ qs → Congr P Γ ql A a a' → Congr P Γ qr B b b'
    → Congr P Γ qs (A ⊗ B) (.pair a b) (.pair a' b')
  | let₂ {Γ ql qr qs a a' c c' A B C} :
    ql + qr ≤ qs → Congr P Γ ql (A ⊗ B) a a'
    → Congr P (B::A::Γ) ((qr.cons ↑(quant A)).cons ↑(quant B)) C c c'
    → Congr P Γ qs C (.let₂ a c) (.let₂ a' c')
  | rel {Γ qs a a' A} : P Γ qs A a a' → Congr P Γ qs A a a'
  | trans {Γ qs a₁ a₂ a₃ A} : Congr P Γ qs A a₁ a₂ → Congr P Γ qs A a₂ a₃ → Congr P Γ qs A a₁ a₃

instance Congr.instIsTrans
  {P : (Γ : List (Ty τ)) → Vector' EQuant Γ.length → Ty τ → Term τ → Term τ → Prop}
  : IsTrans (Term τ) (Congr P Γ qs A) where
  trans _ _ _ := Congr.trans

theorem Congr.increasing {P} : P ≤ Congr (τ := τ) P := λ _ _ _ _ _ => .rel

theorem Congr.mono {P Q} (h : P ≤ Q) : Congr (τ := τ) P ≤ Congr Q := by
  intro _ _ _ _ _ h'
  induction h' with
  | trans => apply trans <;> assumption
  | rel => apply rel; apply h; assumption
  | _ => constructor <;> assumption

theorem Congr.flatten {P Γ qs a a' A} (h : Congr (τ := τ) (Congr P) Γ qs A a a')
  : Congr P Γ qs A a a' := by
  induction h with
  | trans => apply trans <;> assumption
  | rel => assumption
  | _ => constructor <;> assumption

theorem Congr.flatten_iff {P Γ qs a a' A}
  : Congr (τ := τ) (Congr P) Γ qs A a a' ↔ Congr P Γ qs A a a'
  := ⟨flatten, rel⟩

theorem Congr.flatten_eq {P} : Congr (τ := τ) (Congr P) = Congr P := by ext; exact flatten_iff

inductive Rw : Term τ → Term τ → Prop
  | let₂_β : Rw (.let₂ (.pair a b) c) (.let₁ a (.let₁ (wk0 b) c))
  | let₂_η : Rw (.let₂ a (.pair (.var 1) (.var 0))) c
  | let₂_bind : Rw (.let₂ a c) (.let₁ a (.let₂ (.var 0) (wk2 c)))
  | let₁_let₁ : Rw (.let₁ (.let₁ a b) c) (.let₁ a (.let₁ b (wk1 c)))
  | let₁_let₂ : Rw (.let₁ (.let₂ a c) d) (.let₂ a (.let₁ c (wk1 (wk1 d))))

-- theorem Rw.wf_iff {a b : Term τ} (h : Rw a b) : a.Wfq Γ qs A ↔ b.Wfq Γ qs A := by
--   cases h with
--   | let₂_β =>
--     simp only [Wfq.let₂_iff, Wfq.let₁_iff]
--     sorry
--   | let₂_η => sorry
--   | let₂_bind => sorry
--   | let₁_let₁ => sorry
--   | let₁_let₂ => sorry

inductive QRw
  : (Γ : List (Ty τ)) → Vector' EQuant Γ.length → Term τ → Term τ → Prop
  | let₂_β {Γ qa qb qr qs a b c A B C} :
    qa + qb + qr ≤ qs → WfqD Γ qa a A → WfqD Γ qb b B → WfqD Γ qr c C →
    QRw Γ qs (.let₂ (.pair a b) c) (.let₁ a (.let₁ (wk0 b) c))
  | let₂_η {Γ qs a A B} : WfqD Γ qs a (A ⊗ B) →
    QRw Γ qs (.let₂ a (.pair (.var 1) (.var 0))) c
  | let₂_bind {Γ qa qc qs a c A B C} :
    qa + qc ≤ qs
    → WfqD Γ qa a (A ⊗ B)
    → WfqD (B::A::Γ) ((qc.cons ↑(quant A)).cons ↑(quant B)) c C
    → QRw Γ qs (.let₂ a c) (.let₁ a (.let₂ (.var 0) (wk2 c)))
  | let₁_let₁ {Γ qa qb qc qs a b c A B C} :
    qa + qb + qc ≤ qs → WfqD Γ qa a A
    → WfqD (A::Γ) (qb.cons (quant A)) b B → WfqD (B::Γ) (qc.cons (quant B)) c C
    → QRw Γ qs (.let₁ (.let₁ a b) c) (.let₁ a (.let₁ b (wk1 c)))
  | let₁_let₂ {Γ qa qc qd qs a c d A B C D} :
    qa + qc + qd ≤ qs → WfqD Γ qa a (A ⊗ B)
    → WfqD (B::A::Γ) ((qc.cons ↑(quant A)).cons ↑(quant B)) c C
    → WfqD (C::Γ) (qd.cons (quant C)) d D
    → QRw Γ qs (.let₁ (.let₂ a c) d) (.let₂ a (.let₁ c (wk1 (wk1 d))))
