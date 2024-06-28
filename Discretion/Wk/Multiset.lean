import Discretion.Wk.Nat
import Mathlib.Data.Multiset.Basic

/-- Compute the free variable set of a term under `n` binders -/
def Multiset.liftnFv (n : ℕ) (s : Multiset ℕ) := (s.filter (n ≤ ·)).map (· - n)

@[simp]
theorem Multiset.liftnFv_zero : Multiset.liftnFv 0 = id := by ext s i; simp [liftnFv]

@[simp]
theorem Multiset.liftnFv_of_add (n : ℕ) (s t : Multiset ℕ)
  : (s + t).liftnFv n = s.liftnFv n + t.liftnFv n := by simp [liftnFv]

theorem Multiset.mem_liftnFv_of_add_mem (n : ℕ) (s : Multiset ℕ) (k : ℕ)
    : k ∈ s.liftnFv n → k + n ∈ s := by
  simp only [liftnFv, mem_map, mem_filter, forall_exists_index, and_imp]
  intro x hx hn hk
  cases hk
  rw [Nat.sub_add_cancel hn]
  exact hx

theorem Multiset.add_mem_of_mem_liftnFv (n : ℕ) (s : Multiset ℕ) (k : ℕ) (h : k + n ∈ s)
    : k ∈ s.liftnFv n := by
  simp only [liftnFv, mem_map, mem_filter]
  exact ⟨k + n, ⟨h, by simp⟩, by simp⟩

theorem Multiset.mem_liftnFv (n : ℕ) (s : Multiset ℕ) (k : ℕ)
  : k ∈ liftnFv n s ↔ k + n ∈ s
  := ⟨mem_liftnFv_of_add_mem n s k, add_mem_of_mem_liftnFv n s k⟩

theorem Multiset.not_mem_liftnFv (n : ℕ) (s : Multiset ℕ) (k : ℕ)
  : k ∉ liftnFv n s ↔ k + n ∉ s
  := by simp [mem_liftnFv]

theorem Multiset.count_liftnFv (n : ℕ) (s : Multiset ℕ) (k : ℕ)
  : count k (liftnFv n s) = count (k + n) s := by
  simp only [
    liftnFv, count_map, count_filter, count, countP_map, filter_filter, countP_eq_card_filter,
    map_filter, card_map]
  congr
  funext i
  simp only [Function.comp_apply, eq_iff_iff]
  constructor
  intro ⟨h, h'⟩
  cases h
  simp [h']
  intro h
  cases h
  simp

theorem Multiset.liftnFv_mono {lo hi : Multiset ℕ} (n) (h : lo ≤ hi)
  : lo.liftnFv n ≤ hi.liftnFv n := map_le_map $ filter_le_filter _ h

/-- Compute the free variable set of a term under a binder -/
abbrev Multiset.liftFv := Multiset.liftnFv 1

theorem Multiset.count_liftFv (s : Multiset ℕ) (k : ℕ)
  : count k s.liftFv = count (k + 1) s := count_liftnFv 1 s k

theorem Multiset.mem_liftFv_of_succ_mem (s : Multiset ℕ) (k : ℕ)
    : k ∈ s.liftFv → k + 1 ∈ s := mem_liftnFv_of_add_mem 1 s k

theorem Multiset.succ_mem_of_mem_liftFv (s : Multiset ℕ) (k : ℕ)
    : k + 1 ∈ s → k ∈ s.liftFv := add_mem_of_mem_liftnFv 1 s k

theorem Multiset.mem_liftFv (s : Multiset ℕ) (k : ℕ)
  : k ∈ s.liftFv ↔ k + 1 ∈ s := mem_liftnFv 1 s k

theorem Multiset.not_mem_liftFv (s : Multiset ℕ) (k : ℕ)
  : k ∉ s.liftFv ↔ k + 1 ∉ s := not_mem_liftnFv 1 s k

theorem Multiset.liftFv_of_add (s t : Multiset ℕ)
  : (s + t).liftFv = s.liftFv + t.liftFv := by simp

theorem Multiset.liftnFv_one : Multiset.liftnFv 1 = Multiset.liftFv := rfl

theorem Multiset.liftnFv_succ (n) (s : Multiset ℕ) : s.liftnFv n.succ = s.liftFv.liftnFv n := by
  ext i
  simp only [liftnFv, liftFv, count_map, filter_filter, <-countP_eq_card_filter, countP_map]
  congr
  ext a
  simp only [Nat.succ_eq_add_one]
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
  simp only [Nat.liftnWk]
  split
  . simp_arith [*]
  . rename_i h
    simp [le_of_not_lt h]

@[simp]
theorem Multiset.liftFv_map_liftWk (s : Multiset ℕ) (ρ)
  : (s.map (Nat.liftWk ρ)).liftFv = s.liftFv.map ρ := by
  rw [<-Nat.liftnWk_one, <-liftnFv_one, liftnFv_map_liftnWk]

theorem Multiset.liftFv_mono {lo hi : Multiset ℕ} (h : lo ≤ hi)
  : lo.liftFv ≤ hi.liftFv := liftnFv_mono 1 h

-- TODO: liftnFv map add, liftFv map succ...
