import Mathlib.Order.Basic

section Bot

variable [Bot ε]

def Nat.liftBot (εs : ℕ → ε) : ℕ → ε
  | 0 => ⊥
  | n + 1 => εs n

def Nat.liftnBot (n : ℕ) (εs : ℕ → ε) : ℕ → ε
  := λm => if m < n then ⊥ else εs (m - n)

@[simp]
theorem Nat.liftnBot_zero : Nat.liftnBot 0 = @id (ℕ → ε) := rfl

theorem Nat.liftnBot_zero_apply (εs : ℕ → ε) : Nat.liftnBot 0 εs = εs := rfl

-- theorem Nat.liftnBot_one : Nat.liftnBot 1 = @Nat.liftBot ε _ := sorry

end Bot

section Top

variable [Top ε]

def Nat.liftTop (εs : ℕ → ε) : ℕ → ε
  | 0 => ⊤
  | n + 1 => εs n

def Nat.liftnTop (n : ℕ) (εs : ℕ → ε) : ℕ → ε
  := λm => if m < n then ⊤ else εs (m - n)

@[simp]
theorem Nat.liftnTop_zero : Nat.liftnTop 0 = @id (ℕ → ε) := rfl

theorem Nat.liftnTop_zero_apply (εs : ℕ → ε) : Nat.liftnTop 0 εs = εs := rfl

end Top
