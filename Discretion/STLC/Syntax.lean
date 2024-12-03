import Discretion.Wk.Fin
import Discretion.Wk.Multiset

namespace STLC

class Syntax (α : Type _) where
  arity : α → ℕ
  binders : (a : α) → Fin (arity a) → ℕ

open Syntax

inductive Term (α : Type _) [Syntax α] where
  | var : Nat → Term α
  | tm : (a : α) → (Fin (arity a) → Term α) → Term α

namespace Term

variable [Syntax α]

def fv : Term α → Multiset ℕ
  | var n => {n}
  | tm a ts => Finset.sum Finset.univ (λi => (fv (ts i)).liftnFv (binders a i))

def fvi : Term α → ℕ
  | var n => n + 1
  | tm a ts => Fin.max (λi => fvi (ts i) - binders a i)

def fvc (k : ℕ) : Term α → ℕ
  | var n => if k = n then 1 else 0
  | tm a ts => Finset.sum Finset.univ (λi => fvc (k + binders a i) (ts i))

-- theorem fvi_zero_iff_fv_zero (t : Term α) : t.fvi = 0 ↔ t.fv = 0 :=
--   by induction t with
--   | var => simp [fvi, fv]
--   | tm a ts I =>
--     simp only [fvi, fv, Fin.max_nat_eq_zero_iff]
--     sorry

end Term
