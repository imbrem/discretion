import Discretion.Wk.Fun

namespace STLC

class Syntax (α : Type _) where
  arity : α → ℕ
  binders : (a : α) → Fin (arity a) → ℕ

open Syntax

inductive Term (α : Type _) [Syntax α] where
  | var : Nat → Term α
  | tm : (a : α) → (Fin (arity a) → Term α) → Term α

open Term

variable [Syntax α]

def fv : Term α → Nat
  | var n => n + 1
  | tm a ts => Fin.max (λi => fv (ts i) - binders a i)
