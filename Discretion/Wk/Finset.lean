import Discretion.Wk.Nat
import Mathlib.Data.Finset.Basic

/-- Compute the free variable set of a term under `n` binders -/
def Finset.liftnFv (n : ℕ) (s : Finset ℕ) := (s.filter (n ≤ ·)).image (· - n)

@[simp]
theorem Finset.mem_liftnFv_iff (n : ℕ) (s : Finset ℕ) (k : ℕ)
  : k ∈ liftnFv n s ↔ k + n ∈ s := by
  simp only [liftnFv, mem_image, mem_filter]
  constructor
  intro ⟨a, ⟨ha, ha'⟩, hk⟩; cases hk; convert ha; simp [ha']
  intro hk; exists (k + n); simp [hk]

@[simp]
theorem Finset.liftnFv_zero : Finset.liftnFv 0 = id := by ext s i; simp

@[simp]
theorem Finset.liftnFv_empty (n : ℕ) : (∅ : Finset ℕ).liftnFv n = ∅ := by ext k; simp

@[simp]
theorem Finset.liftnFv_union (n : ℕ) (s t : Finset ℕ)
  : (s ∪ t).liftnFv n = s.liftnFv n ∪ t.liftnFv n := by ext k; simp

@[simp]
theorem Finset.liftnFv_inter (n : ℕ) (s t : Finset ℕ)
  : (s ∩ t).liftnFv n = s.liftnFv n ∩ t.liftnFv n := by ext k; simp

@[simp]
theorem Finset.liftnFv_succ_singleton_zero (n : ℕ)
  : liftnFv (n + 1) {0} = ∅ := by ext k; simp

@[simp]
theorem Finset.liftnFv_singleton_min (n : ℕ)
  : liftnFv n {n} = {0} := by ext k; simp

@[simp]
theorem Finset.liftnFv_insert_zero {s : Finset ℕ} {n}
  : (insert 0 s).liftnFv (n + 1) = s.liftnFv (n + 1) := by ext k; simp

@[simp]
theorem Finset.liftnFv_insert_n {s : Finset ℕ} {n}
  : (insert n s).liftnFv n = insert 0 (s.liftnFv n) := by ext k; simp

/-- Compute the free variable set of a term under a binder -/
abbrev Finset.liftFv := Finset.liftnFv 1

theorem Finset.mem_liftFv_iff (s : Finset ℕ) (k : ℕ)
  : k ∈ s.liftFv ↔ k + 1 ∈ s := by simp

theorem Finset.liftFv_empty : (∅ : Finset ℕ).liftFv = ∅ := by simp

theorem Finset.liftFv_union (s t : Finset ℕ) : (s ∪ t).liftFv = s.liftFv ∪ t.liftFv := by simp

theorem Finset.liftFv_inter (s t : Finset ℕ) : (s ∩ t).liftFv = s.liftFv ∩ t.liftFv := by simp

theorem Finset.liftFv_insert_zero {s : Finset ℕ} : (insert 0 s).liftFv = s.liftFv := by simp

@[simp]
theorem Finset.liftFv_insert_succ {s : Finset ℕ} : (insert (n + 1) s).liftFv = insert n s.liftFv
  := by ext k; simp
