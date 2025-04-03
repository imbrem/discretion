import Discretion.Ctx.Ren.Nat

namespace Nat

inductive Wk : Nat → Nat → Type
  | nil : Wk 0 0
  | step {n m} : Wk n m -> Wk (n + 1) m
  | lift {n m} : Wk n m -> Wk (n + 1) (m + 1)

namespace Wk

def one : (n : ℕ) → Wk n n | 0 => .nil | n + 1 => .lift (one n)

def zero : (n : ℕ) → Wk n 0 | 0 => .nil | n + 1 => .step (zero n)

def pave {n m} : Wk n m → Wk (n + 1) (m + 1)
  | .nil => .lift .nil
  | .step ρ => .step ρ.pave
  | .lift ρ => .lift ρ.pave

theorem pave_nil : pave .nil = .lift .nil := rfl

theorem pave_step {n m} (ρ : Wk n m) : pave (.step ρ) = .step ρ.pave := rfl

theorem pave_lift {n m} (ρ : Wk n m) : pave (.lift ρ) = .lift ρ.pave := rfl
