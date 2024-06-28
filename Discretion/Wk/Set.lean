import Discretion.Wk.Nat
import Mathlib.Data.Set.Basic

/-- Compute the free variable set of a term under `n` binders -/
def Set.liftnFv (n : ℕ) (s : Set ℕ) := (· - n) '' (s ∩ Set.Ici n)

@[simp]
theorem Set.liftnFv_zero : Set.liftnFv 0 = id := by ext s i; simp [liftnFv]

@[simp]
theorem Set.liftnFv_of_union (n : ℕ) (s t : Set ℕ) : (s ∪ t).liftnFv n = s.liftnFv n ∪ t.liftnFv n
  := Set.ext λ_ => ⟨
    λ⟨k, ⟨hkst, hkn⟩, hkn'⟩ => hkst.elim (Or.inl ⟨k, ⟨·, hkn⟩, hkn'⟩) (Or.inr ⟨k, ⟨·, hkn⟩, hkn'⟩),
    λ
    | Or.inl ⟨k, ⟨hks, hkn⟩, hkn'⟩ => ⟨k, ⟨Or.inl hks, hkn⟩, hkn'⟩
    | Or.inr ⟨k, ⟨hkt, hkn⟩, hkn'⟩ => ⟨k, ⟨Or.inr hkt, hkn⟩, hkn'⟩
  ⟩

@[simp]
theorem Set.liftnFv_empty (n : ℕ) : (∅ : Set ℕ).liftnFv n = ∅ := by simp [liftnFv]

@[simp]
theorem Set.liftnFv_insert_lt {s : Set ℕ} {k n} (h : k < n) : (insert k s).liftnFv n = s.liftnFv n
  := by
  rw [liftnFv, insert_inter_of_not_mem]
  rfl
  simp [h]

theorem Set.liftnFv_insert_zero {s : Set ℕ} {n}
  : (insert 0 s).liftnFv (n + 1) = s.liftnFv (n + 1) := by simp

@[simp]
theorem Set.liftnFv_insert_le {s : Set ℕ} {k n} (h : n ≤ k)
  : (insert k s).liftnFv n = insert (k - n) (s.liftnFv n)
  := by
  rw [liftnFv, insert_inter_of_mem, image_insert_eq]
  rfl
  simp [h]

theorem Set.liftnFv_insert_n {s : Set ℕ} {n}
  : (insert n s).liftnFv n = insert 0 (s.liftnFv n)
  := by simp

theorem Set.mem_liftnFv_of_add_mem (n : ℕ) (s : Set ℕ) (k : ℕ)
    : k ∈ s.liftnFv n → k + n ∈ s := by
  simp only [liftnFv, forall_exists_index, and_imp]
  intro ⟨x, ⟨hx, hn⟩, hk⟩
  cases hk
  rw [Nat.sub_add_cancel hn]
  exact hx

theorem Set.add_mem_of_mem_liftnFv (n : ℕ) (s : Set ℕ) (k : ℕ) (h : k + n ∈ s)
    : k ∈ s.liftnFv n := ⟨k + n, ⟨h, by simp⟩, by simp⟩

theorem Set.mem_liftnFv (n : ℕ) (s : Set ℕ) (k : ℕ)
  : k ∈ liftnFv n s ↔ k + n ∈ s
  := ⟨mem_liftnFv_of_add_mem n s k, add_mem_of_mem_liftnFv n s k⟩

theorem Set.not_mem_liftnFv (n : ℕ) (s : Set ℕ) (k : ℕ)
  : k ∉ liftnFv n s ↔ k + n ∉ s
  := by simp [mem_liftnFv]

theorem Set.liftnFv_mono {lo hi : Set ℕ} (n) (h : lo ⊆ hi)
  : lo.liftnFv n ⊆ hi.liftnFv n := Set.image_mono (Set.inter_subset_inter_left _ h)

/-- Compute the free variable set of a term under a binder -/
abbrev Set.liftFv := Set.liftnFv 1

theorem Set.liftFv_mono {lo hi : Set ℕ} (h : lo ⊆ hi)
  : lo.liftFv ⊆ hi.liftFv := Set.image_mono (Set.inter_subset_inter_left _ h)

theorem Set.liftFv_insert_zero {s : Set ℕ}
  : (insert 0 s).liftFv = s.liftFv := by simp

theorem Set.liftFv_insert_succ {s : Set ℕ}
  : (insert (n + 1) s).liftFv = insert n s.liftFv
    := by simp

theorem Set.mem_liftFv_of_succ_mem (s : Set ℕ) (k : ℕ)
    : k ∈ s.liftFv → k + 1 ∈ s := mem_liftnFv_of_add_mem 1 s k

theorem Set.succ_mem_of_mem_liftFv (s : Set ℕ) (k : ℕ)
    : k + 1 ∈ s → k ∈ s.liftFv := add_mem_of_mem_liftnFv 1 s k

theorem Set.mem_liftFv (s : Set ℕ) (k : ℕ)
  : k ∈ s.liftFv ↔ k + 1 ∈ s := mem_liftnFv 1 s k

theorem Set.not_mem_liftFv (s : Set ℕ) (k : ℕ)
  : k ∉ s.liftFv ↔ k + 1 ∉ s := not_mem_liftnFv 1 s k

theorem Set.liftFv_of_union (s t : Set ℕ)
  : (s ∪ t).liftFv = s.liftFv ∪ t.liftFv := by simp

theorem Set.liftFv_empty : (∅ : Set ℕ).liftFv = ∅ := by simp

theorem Set.liftnFv_one : Set.liftnFv 1 = Set.liftFv := rfl

-- TODO: simplify proofs using above rewrite lemmas?

theorem Set.liftnFv_succ (n) (s : Set ℕ) : s.liftnFv n.succ = s.liftFv.liftnFv n := Set.ext λ_ => ⟨
  λ⟨k, ⟨hks, hkn⟩, hkn'⟩ => ⟨k - 1,
    ⟨⟨k, ⟨hks, le_trans (by simp) (Set.mem_Ici.mp hkn)⟩, rfl⟩, Nat.le_pred_of_lt hkn⟩,
    (by simp only [Nat.succ_eq_one_add, Nat.sub_add_eq] at hkn'; exact hkn')⟩,
  λ⟨k, ⟨⟨k', ⟨hk's, hk'n⟩, hk'⟩, hkn⟩, hkn'⟩ => by cases hk'; exact ⟨k',
    ⟨hk's, Set.mem_Ici.mpr (Nat.lt_of_le_pred hk'n hkn)⟩,
    by simp only [Nat.succ_eq_one_add, Nat.sub_add_eq]; exact hkn'⟩⟩

theorem Set.liftnFv_add (n m) (s : Set ℕ)
  : s.liftnFv (n + m) = (s.liftnFv m).liftnFv n := by induction m generalizing s with
  | zero => simp
  | succ m I => rw [<-Nat.add_assoc, liftnFv_succ, I, liftnFv_succ]

theorem Set.liftnFv_succ' (n) (s : Set ℕ) : s.liftnFv n.succ = (s.liftnFv n).liftFv := by
  rw [Nat.succ_eq_add_one, Nat.add_comm, liftnFv_add]

@[simp]
theorem Set.liftnFv_map_liftnWk (n) (s : Set ℕ) (ρ)
  : (Nat.liftnWk n ρ '' s).liftnFv n = ρ '' (s.liftnFv n) := Set.ext λi => ⟨
  λ⟨_, ⟨⟨k, hks, hρk⟩, hρkn⟩, hρkn'⟩ => by
    cases hρk
    have h : ¬k < n := if h : k < n
      then by simp [Nat.liftnWk, h, Nat.not_le_of_lt h] at hρkn
      else h
    exact ⟨k - n,
      ⟨k, ⟨hks, Nat.le_of_not_lt h⟩, rfl⟩,
      by simp [<-hρkn', Nat.liftnWk, h]⟩,
  λ⟨_, ⟨k, ⟨hks, hkn⟩, hk⟩, hρk⟩ => by
    cases hρk
    cases hk
    exact ⟨n.liftnWk ρ k, ⟨⟨k, hks, rfl⟩,
      by simp [Nat.liftnWk, Nat.not_lt_of_le hkn]⟩,
      by simp [Nat.liftnWk, Nat.not_lt_of_le hkn]⟩
  ⟩

@[simp]
theorem Set.liftFv_map_liftWk (s : Set ℕ) (ρ) : (Nat.liftWk ρ '' s).liftFv = ρ '' s.liftFv := by
  rw [<-Nat.liftnWk_one, <-liftnFv_one, liftnFv_map_liftnWk]

-- TODO: liftnFv map add, liftFv map succ...

-- TODO: liftnFv (and therefore liftFv) commute with multiset to set

-- TODO: liftnFv and friends for Finset, Sometime Later (TM)
