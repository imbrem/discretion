import Discretion.SEC.Extrinsic.Typing
import Discretion.PER.Basic

open CategoryTheory

open CategoryTheory.MonoidalCategory

namespace SEC

open FreeSignature

namespace Term

variable {τ} [FreeSignature τ]

inductive Congr (P : List (Ty τ) → Ty τ → Term τ → Term τ → Prop)
  : List (Ty τ) → Ty τ → Term τ → Term τ → Prop
  | refl {Γ qs a A} : WfqD Γ qs a A → Congr P Γ A a a
  | op {Γ f a a' A B} (hA : f.src = A) (hB : f.trg = B) : Congr P Γ A a a'
    → Congr P Γ B (.op f a) (.op f a')
  | let₁ {Γ a a' b b' A B} : Congr P Γ A a a' → Congr P (A::Γ) B b b'
    → Congr P Γ B (.let₁ a b) (.let₁ a' b')
  | pair {Γ a b a' b' A B} : Congr P Γ A a a' → Congr P Γ B b b'
    → Congr P Γ (A ⊗ B) (.pair a b) (.pair a' b')
  | let₂ {Γ a a' c c' A B C} : Congr P Γ (A ⊗ B) a a'
    → Congr P (B::A::Γ) C c c' → Congr P Γ C (.let₂ a c) (.let₂ a' c')
  | symm {Γ a a' A} : Congr P Γ A a a' → Congr P Γ A a' a
  | trans {Γ a₁ a₂ a₃ A} : Congr P Γ A a₁ a₂ → Congr P Γ A a₂ a₃ → Congr P Γ A a₁ a₃
  | rel {Γ a a' A} : P Γ A a a' → Congr P Γ A a a'

instance Congr.instIsPER {P : List (Ty τ) → Ty τ → Term τ → Term τ → Prop}
  : IsPER (Term τ) (Congr P Γ A) where
  symm _ _ := Congr.symm
  trans _ _ _ := Congr.trans

theorem Congr.increasing {P} : P ≤ Congr (τ := τ) P := λ _ _ _ _ => .rel

theorem Congr.mono {P Q} (h : P ≤ Q) : Congr (τ := τ) P ≤ Congr Q := by
  intro _ _ _ _ h'
  induction h' with
  | trans => apply trans <;> assumption
  | rel => apply rel; apply h; assumption
  | _ => constructor <;> assumption

theorem Congr.flatten {P Γ a a' A} (h : Congr (τ := τ) (Congr P) Γ A a a') : Congr P Γ A a a' := by
  induction h with
  | trans => apply trans <;> assumption
  | rel => assumption
  | _ => constructor <;> assumption

theorem Congr.flatten_iff {P Γ a a' A} : Congr (τ := τ) (Congr P) Γ A a a' ↔ Congr P Γ A a a'
  := ⟨flatten, rel⟩

theorem Congr.flatten_eq {P} : Congr (τ := τ) (Congr P) = Congr P := by ext; exact flatten_iff
