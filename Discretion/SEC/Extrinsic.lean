import Mathlib.CategoryTheory.Monoidal.Free.Basic
import Discretion.Wk.List

import Discretion.SEC.Signature
import Discretion.SEC.Untyped

open CategoryTheory.MonoidalCategory

namespace SEC

open FreeSignature

namespace Term

inductive HasTy {τ : Type _} [FreeSignature τ] : List (Ty τ) → Term τ → Ty τ → Prop
  | var {Γ i A} (h : i < Γ.length) : Γ[i] = A → HasTy Γ (.var i) A
  | op {Γ f a A B} (hA : f.src = A) (hB : f.trg = B) : HasTy Γ a A → HasTy Γ (.op f a) B
  | let₁ {Γ a b A B} : HasTy Γ a A → HasTy (A::Γ) b B → HasTy Γ (.let₁ a b) B
  | unit {Γ} : HasTy Γ .unit (𝟙_ _)
  | pair {Γ a b A B} : HasTy Γ a A → HasTy Γ b B → HasTy Γ (.pair a b) (A ⊗ B)
  | let₂ {Γ a c A B C} : HasTy Γ a (A ⊗ B) → HasTy (B::A::Γ) c C → HasTy Γ (.let₂ a c) C

theorem HasTy.unique {τ} [FreeSignature τ] {Γ} {t : Term τ} {A B}
  (hA : HasTy Γ t A) (hB : HasTy Γ t B) : A = B := by
  induction hA generalizing B <;> cases hB <;> subst_vars <;> congr <;> apply_assumption
  case let₁ X Y ha hb I1 I2 Z ha' hb' => cases I1 ha'; exact hb'
  case let₂ X Y Z ha hc I1 I2 W T ha' hc' => cases I1 ha'; exact hc'
  all_goals assumption
