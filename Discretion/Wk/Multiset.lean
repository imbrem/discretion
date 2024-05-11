import Discretion.Wk.Fun
import Mathlib.Data.Multiset.Basic

/-- Compute the free variable set of a term under `n` binders -/
def Multiset.liftnFv (n : ℕ) (s : Multiset ℕ) := (s.filter (· ≥ n)).map (· - n)

theorem Multiset.liftnFv_zero : Multiset.liftnFv 0 = id := by ext s i; simp [liftnFv]

abbrev Multiset.liftFv := Multiset.liftnFv 1

theorem Multiset.liftnFv_one : Multiset.liftnFv 1 = Multiset.liftFv := rfl

theorem Multiset.liftnFv_succ (n) (s : Multiset ℕ) : s.liftnFv n.succ = s.liftFv.liftnFv n := by
  ext i
  simp only [liftnFv, liftFv, count_map, filter_filter, <-countP_eq_card_filter, countP_map]
  congr
  ext a
  simp only [Nat.succ_eq_add_one, ge_iff_le]
  rw [Nat.add_comm n 1, Nat.sub_add_eq, and_assoc, and_congr_right_iff]
  intro hi; cases hi; cases a <;> simp_arith

-- TODO: liftnFv_succ'

-- TODO: liftnFv_add

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

theorem Multiset.liftFv_map_liftWk (s : Multiset ℕ) (ρ)
  : (s.map (Nat.liftWk ρ)).liftFv = s.liftFv.map ρ := by
  rw [<-Nat.liftnWk_one, <-liftnFv_one, liftnFv_map_liftnWk]
