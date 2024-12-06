import Mathlib.CategoryTheory.Monoidal.Free.Basic
import Discretion.Wk.List

import Discretion.SEC.Signature
import Discretion.SEC.Untyped

open CategoryTheory.MonoidalCategory

namespace SEC

open FreeSignature

namespace Split

inductive Term (τ : Type _) [FreeSignature τ] : List (Ty τ) → Ty τ → Type _
  | var {Γ A} : Γ.Wk [A] → Term τ Γ A
  | op {Γ A B} : Inst A B → Term τ Γ A → Term τ Γ B
  | let₁ {Γ A B} : Γ.Split Δ Ξ → Term τ Δ A → Term τ (A::Ξ) B → Term τ Γ B
  | unit {Γ} : Term τ Γ (𝟙_ _)
  | pair {Γ A B} : Γ.Split Δ Ξ → Term τ Δ A → Term τ Ξ B → Term τ Γ (A ⊗ B)
  | let₂ {Γ A B C} : Γ.Split Δ Ξ → Term τ Δ (A ⊗ B) → Term τ (A::B::Ξ) C → Term τ Γ C

def Term.erase {τ} [FreeSignature τ] {Γ A} : Term τ Γ A → Untyped τ
  | .var ρ => .var (ρ.ix 0)
  | .op f t => .op f.erase t.erase
  | .let₁ ρ t u => .let₁ (t.erase.wk ρ.lwk.ix) (u.erase.wk ρ.rwk.ix)
  | .unit => .unit
  | .pair ρ t u => .pair (t.erase.wk ρ.lwk.ix) (u.erase.wk ρ.rwk.ix)
  | .let₂ ρ t u => .let₂ (t.erase.wk ρ.lwk.ix) (u.erase.wk ρ.rwk.ix)

end Split

end SEC
