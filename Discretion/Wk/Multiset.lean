import Discretion.Wk.Fun
import Mathlib.Data.Multiset.Basic

/-- Compute the free variable set of a term under `n` binders -/
def Multiset.liftnFv (n : ℕ) (s : Multiset ℕ) := (s.filter (· ≥ n)).map (· - n)

@[simp]
theorem Multiset.liftnFv_zero : Multiset.liftnFv 0 = id := by ext s i; simp [liftnFv]

@[simp]
theorem Multiset.liftnFv_of_add (n : ℕ) (s t : Multiset ℕ)
  : (s + t).liftnFv n = s.liftnFv n + t.liftnFv n := by simp [liftnFv]

/-- Compute the free variable set of a term under a binder -/
abbrev Multiset.liftFv := Multiset.liftnFv 1

theorem Multiset.liftFv_of_add (s t : Multiset ℕ)
  : (s + t).liftFv = s.liftFv + t.liftFv := by simp

theorem Multiset.liftnFv_one : Multiset.liftnFv 1 = Multiset.liftFv := rfl

theorem Multiset.liftnFv_succ (n) (s : Multiset ℕ) : s.liftnFv n.succ = s.liftFv.liftnFv n := by
  ext i
  simp only [liftnFv, liftFv, count_map, filter_filter, <-countP_eq_card_filter, countP_map]
  congr
  ext a
  simp only [Nat.succ_eq_add_one, ge_iff_le]
  rw [Nat.add_comm n 1, Nat.sub_add_eq, and_assoc, and_congr_right_iff]
  intro hi; cases hi; cases a <;> simp_arith

theorem Multiset.liftnFv_add (n m) (s : Multiset ℕ)
  : s.liftnFv (n + m) = (s.liftnFv m).liftnFv n := by induction m generalizing s with
  | zero => simp
  | succ m I => rw [<-Nat.add_assoc, liftnFv_succ, I, liftnFv_succ]

theorem Multiset.liftnFv_succ' (n) (s : Multiset ℕ) : s.liftnFv n.succ = (s.liftnFv n).liftFv := by
  rw [Nat.succ_eq_add_one, Nat.add_comm, liftnFv_add]

@[simp]
theorem Multiset.liftnFv_map_liftnWk (n) (s : Multiset ℕ) (ρ)
  : (s.map (Nat.liftnWk n ρ)).liftnFv n = (s.liftnFv n).map ρ := by
  ext i
  simp only [count_map, liftnFv, filter_filter, <-countP_eq_card_filter, countP_map]
  congr
  ext a
  simp only [Nat.liftnWk, ge_iff_le]
  split
  . simp_arith [*]
  . rename_i h
    simp [le_of_not_lt h]

@[simp]
theorem Multiset.liftFv_map_liftWk (s : Multiset ℕ) (ρ)
  : (s.map (Nat.liftWk ρ)).liftFv = s.liftFv.map ρ := by
  rw [<-Nat.liftnWk_one, <-liftnFv_one, liftnFv_map_liftnWk]
