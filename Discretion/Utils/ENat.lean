-- TODO: can generalize this to any order in which maximal elements are not reachable by successor
import Mathlib.Data.ENat.Basic

instance : NeZero (⊤ : ℕ∞) := ⟨by decide⟩

instance {n : ℕ} [h : NeZero n] : NeZero (n : ℕ∞) := ⟨by convert h.out; simp⟩

instance {n : ℕ∞} : NeZero (n + 1) := ⟨by simp⟩

namespace ENat

theorem succ_lt_succ {n m : ℕ∞} (h : n < m) : n + 1 < m + 1 := by
  cases n with
  | top => simp at h
  | coe n => cases m with
    | top => exact ENat.coe_lt_top (n + 1)
    | coe => exact (Nat.cast_lt.mpr (Nat.succ_lt_succ (Nat.cast_lt.mp h)))

theorem lt_of_succ_lt_succ {n m : ℕ∞} (h : n + 1 < m + 1) : n < m := by
  cases n with
  | top => simp at h
  | coe n => cases m with
    | top => exact ENat.coe_lt_top n
    | coe m =>
      rw [Nat.cast_lt, <-Nat.succ_lt_succ_iff]
      convert h
      exact Nat.cast_lt.symm

theorem succ_lt_succ_iff {n m : ℕ∞} : n + 1 < m + 1 ↔ n < m
  := ⟨ENat.lt_of_succ_lt_succ, ENat.succ_lt_succ⟩

theorem lt_succ_of_lt {n m : ℕ∞} (h : n < m) : n < m + 1 := lt_of_lt_of_le h (by simp)
