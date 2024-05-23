import Discretion.Wk.Fun
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

/-- Compute the free variable set of a term under a binder -/
abbrev Set.liftFv := Set.liftnFv 1

theorem Set.liftFv_of_union (s t : Set ℕ)
  : (s ∪ t).liftFv = s.liftFv ∪ t.liftFv := by simp

theorem Set.liftnFv_one : Set.liftnFv 1 = Set.liftFv := rfl

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

-- TODO: liftnFv (and therefore liftFv) commute with multiset to set

-- TODO: liftnFv and friends for Finset, Sometime Later (TM)
