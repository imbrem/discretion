import Mathlib.CategoryTheory.Monoidal.Free.Basic
import Discretion.Wk.List

open CategoryTheory.MonoidalCategory

namespace SEC.Intrinsic

local notation "Ty" => CategoryTheory.FreeMonoidalCategory

local notation "tyOf" => CategoryTheory.FreeMonoidalCategory.of

-- TODO: parametrize by type v?
class FreeSignature (τ : Type u) where
  quant : Ty τ → Quant
  quant_mono : ∀{A B}, quant A ⊓ quant B ≤ quant (A ⊗ B)
  inst : Ty τ → Ty τ → Type

inductive Term (τ : Type _) [FreeSignature τ]
  : (Γ : List (Ty τ)) → Vector' Quant Γ.length → Ty τ → Type _
  | var {Γ qs A} : Γ.QWk [A] qs → Term τ Γ qs A
