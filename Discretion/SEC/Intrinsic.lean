import Mathlib.CategoryTheory.Monoidal.Free.Basic
import Discretion.Wk.List

import Discretion.SEC.Signature
import Discretion.SEC.Untyped

open CategoryTheory.MonoidalCategory

namespace SEC

open FreeSignature

namespace Intrinsic

inductive Term (τ : Type _) [FreeSignature τ] : List (Ty τ) → Ty τ → Type _
  | var {Γ A} : Γ.Wk [A] → Term τ Γ A
  | op {Γ A B} : Inst A B → Term τ Γ A → Term τ Γ B
  | let₁ {Γ A B} : Term τ Γ A → Term τ (A::Γ) B → Term τ Γ B
  | unit {Γ} : Term τ Γ (𝟙_ _)
  | pair {Γ A B} : Term τ Γ A → Term τ Γ B → Term τ Γ (A ⊗ B)
  | let₂ {Γ A B C} : Term τ Γ (A ⊗ B) → Term τ (A::B::Γ) C → Term τ Γ C

def Term.erase {τ} [FreeSignature τ] {Γ A} : Term τ Γ A → SEC.Term τ
  | .var ρ => .var (ρ.ix 0)
  | .op f t => .op f.erase t.erase
  | .let₁ t u => .let₁ t.erase u.erase
  | .unit => .unit
  | .pair t u => .pair t.erase u.erase
  | .let₂ t u => .let₂ t.erase u.erase

-- TODO: erase is faithful
