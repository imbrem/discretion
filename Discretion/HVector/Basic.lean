import Mathlib.Logic.Function.Defs
import Mathlib.Data.List.Basic

import Discretion.Vector.Basic

inductive HVector {α : Type u} (f : α → Type v) : List α → Type _
  | nil : HVector f []
  | cons {a Γ} : f a → HVector f Γ → HVector f (a :: Γ)

inductive HVector' {α : Type u} (f : α → Type v) : ∀{n}, Vector' α n → Type _
  | nil : HVector' f .nil
  | cons {a Γ} : f a → HVector' f Γ → HVector' f (Γ.cons a)
