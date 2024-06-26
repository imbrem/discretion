import Mathlib.Order.Basic
import Mathlib.Order.Monotone.Basic

import Discretion.Wk.Nat

section Bot

variable [Bot ε]

def Nat.liftBot (εs : ℕ → ε) : ℕ → ε
  | 0 => ⊥
  | n + 1 => εs n

theorem Nat.liftBot_mono [PartialOrder ε] : Monotone (@Nat.liftBot ε _) :=
  λ_ _ h k => match k with | 0 => le_refl _ | n + 1 => h n

theorem Nat.liftBot_zero : Nat.liftBot εs 0 = (⊥ : ε) := rfl

theorem Nat.liftBot_liftWk (εs : ℕ → ε) (ρ) (k)
  : Nat.liftBot εs (Nat.liftWk ρ k) = Nat.liftBot (εs ∘ ρ) k
  := by cases k <;> rfl

theorem Nat.liftBot_comp_liftWk (εs : ℕ → ε) (ρ)
  : Nat.liftBot εs ∘ Nat.liftWk ρ = Nat.liftBot (εs ∘ ρ)
  := funext (Nat.liftBot_liftWk εs ρ)

theorem Nat.liftBot_succ (εs : ℕ → ε)
  : (Nat.liftBot εs (n + 1)) = εs n
  := rfl

@[simp]
theorem Nat.liftBot_comp_succ (εs : ℕ → ε)
  : Nat.liftBot εs ∘ Nat.succ = εs
  := rfl

def Nat.liftnBot (n : ℕ) (εs : ℕ → ε) : ℕ → ε
  := λm => if m < n then ⊥ else εs (m - n)

theorem Nat.liftnBot_liftnWk (n : ℕ) (εs : ℕ → ε) (ρ) (k)
  : Nat.liftnBot n εs (Nat.liftnWk n ρ k) = Nat.liftnBot n (εs ∘ ρ) k
  := by simp only [Nat.liftnWk, Nat.liftnBot]; split <;> simp

theorem Nat.liftnBot_comp_liftnWk (n : ℕ) (εs : ℕ → ε)
  : Nat.liftnBot n εs ∘ Nat.liftnWk n ρ = Nat.liftnBot n (εs ∘ ρ)
  := funext (Nat.liftnBot_liftnWk n εs ρ)

theorem Nat.liftnBot_add (n : ℕ) (εs : ℕ → ε) (i)
  : Nat.liftnBot n εs (i + n) = εs i
  := by simp [liftnBot]

@[simp]
theorem Nat.liftnBot_comp_add (n : ℕ) (εs : ℕ → ε)
  : Nat.liftnBot n εs ∘ (· + n) = εs
  := funext (Nat.liftnBot_add n εs)

theorem Nat.liftnBot_mono [PartialOrder ε] (n : ℕ) : Monotone (@Nat.liftnBot ε _ n) :=
  λ_ _ h k => by if h' : k < n then simp [liftnBot, h'] else simp [liftnBot, h', h (k - n)]

@[simp]
theorem Nat.liftnBot_zero : Nat.liftnBot 0 = @id (ℕ → ε) := rfl

theorem Nat.liftnBot_zero_apply (εs : ℕ → ε) : Nat.liftnBot 0 εs = εs := rfl

theorem Nat.liftnBot_succ_apply (n : ℕ) (εs : ℕ → ε) : Nat.liftnBot (n + 1) εs
  = (Nat.liftnBot n (Nat.liftBot εs)) := by
  ext k
  cases k with
  | zero => simp [Nat.liftBot, Nat.liftnBot]
  | succ k =>
    simp only [liftnBot, Nat.add_lt_add_iff_right, reduceSubDiff, liftBot]
    split
    case isTrue h =>
      have h' := Nat.succ_le_of_lt h
      split
      case isTrue h'' =>
        rfl
      case isFalse h'' =>
        have h'' := Nat.le_of_not_lt h''
        cases le_antisymm h' h''
        simp
    case isFalse h =>
      rw [ite_cond_eq_false]
      rw [Nat.add_comm k 1]
      rw [Nat.add_sub_assoc]
      rw [Nat.add_comm]
      exact Nat.le_of_not_lt h
      simp only [eq_iff_iff, iff_false, not_lt]
      exact Nat.le_succ_of_le (Nat.le_of_not_lt h)

theorem Nat.liftnBot_succ (n : ℕ)
  : Nat.liftnBot (n + 1) = Nat.liftnBot n ∘ (@Nat.liftBot ε _)
  := funext (Nat.liftnBot_succ_apply n)

theorem Nat.liftnBot_iterate (n : ℕ)
  : Nat.liftnBot n = Nat.iterate (@Nat.liftBot ε _) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ]
    rw [<-ih]
    rw [Nat.liftnBot_succ]

theorem Nat.liftnBot_succ' (n : ℕ)
  : Nat.liftnBot (n + 1) = (@Nat.liftBot ε _) ∘ Nat.liftnBot n := by
  simp only [Nat.liftnBot_iterate, Function.iterate_succ']

theorem Nat.liftnBot_succ_apply' (n : ℕ) (εs : ℕ → ε) : Nat.liftnBot (n + 1) εs
  = (Nat.liftBot (Nat.liftnBot n εs)) := by
  rw [Nat.liftnBot_succ']
  rfl

theorem Nat.liftnBot_one : Nat.liftnBot 1 = @Nat.liftBot ε _ := by simp [Nat.liftnBot_succ]

theorem Nat.liftnBot_two : Nat.liftnBot 2 = (@Nat.liftBot ε _) ∘ Nat.liftBot := by
  simp [Nat.liftnBot_succ, Nat.liftnBot_one]

theorem Nat.liftnBot_two_apply (εs : ℕ → ε) : Nat.liftnBot 2 εs = Nat.liftBot (Nat.liftBot εs) := by
  simp [Nat.liftnBot_two]

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
