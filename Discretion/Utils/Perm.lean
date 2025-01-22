import Mathlib.Data.Set.Function
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card

def Fin.numMissedBefore (ρ : Fin n → Fin m) : ℕ → ℕ
  | 0 => 0
  | k + 1 => (if ∃i : Fin n, ρ i = k then 0 else 1) + numMissedBefore ρ k

@[simp]
theorem Fin.numMissedBefore_zero (ρ : Fin n → Fin m)
  : numMissedBefore ρ 0 = 0 := rfl

theorem Fin.numMissedBefore_le_numMissedBefore_succ (ρ : Fin n → Fin m) (k : ℕ)
  : numMissedBefore ρ k ≤ numMissedBefore ρ (k + 1) := by simp [numMissedBefore]

theorem Fin.numMissedBefore_mono (ρ : Fin n → Fin m) : Monotone (numMissedBefore ρ) := by
  intro i j hij
  induction hij with
  | refl => rfl
  | step _ I => exact I.trans (numMissedBefore_le_numMissedBefore_succ ρ _)

theorem Fin.numMissedBefore_le_succ (ρ : Fin n → Fin m) (k : ℕ)
  : numMissedBefore ρ (k + 1) ≤ numMissedBefore ρ k + 1
  := by simp only [numMissedBefore]; split <;> simp_arith

def Fin.numMissed (ρ : Fin n → Fin m) : ℕ := numMissedBefore ρ m

@[simp]
theorem Fin.numMissed_to_zero (ρ : Fin n → Fin 0)
  : numMissed ρ = 0 := by simp [numMissed]

@[simp]
theorem Fin.numMissedBefore_from_zero (ρ : Fin 0 → Fin m)
  : numMissedBefore ρ k = k := by induction k with
  | zero => rfl
  | succ k I => simp [numMissedBefore, Nat.add_comm, I]

@[simp]
theorem Fin.numMissed_from_zero (ρ : Fin 0 → Fin m)
  : numMissed ρ = m := numMissedBefore_from_zero ρ

def Fin.numHitBefore (ρ : Fin n → Fin m) : ℕ → ℕ
  | 0 => 0
  | k + 1 => (if ∃i : Fin n, ρ i = k then 1 else 0) + numHitBefore ρ k

def Fin.numHit (ρ : Fin n → Fin m) : ℕ := numHitBefore ρ m

theorem Fin.numMissedBefore_add_numHitBefore (ρ : Fin n → Fin m) (k : ℕ)
  : numMissedBefore ρ k + numHitBefore ρ k = k := by
  induction k with
  | zero => simp [numMissedBefore, numHitBefore]
  | succ n I =>
    simp only [numMissedBefore, numHitBefore]
    split <;> simp_arith [I]

theorem Fin.total_sub_numMissedBefore (ρ : Fin n → Fin m) (k : ℕ)
  : k - numMissedBefore ρ k = numHitBefore ρ k := by
  conv =>
    lhs
    lhs
    rw [<-Fin.numMissedBefore_add_numHitBefore ρ k]
  simp

theorem Fin.total_sub_numHitBefore (ρ : Fin n → Fin m) (k : ℕ)
  : k - numHitBefore ρ k = numMissedBefore ρ k := by
  conv =>
    lhs
    lhs
    rw [<-Fin.numMissedBefore_add_numHitBefore ρ k]
  simp

theorem Fin.numMissedBefore_eq_total_sub_numHitBefore (ρ : Fin n → Fin m) (k : ℕ)
  : numMissedBefore ρ k = k - numHitBefore ρ k := by
  rw [total_sub_numHitBefore ρ k]

theorem Fin.numHitBefore_eq_total_sub_numMissedBefore (ρ : Fin n → Fin m) (k : ℕ)
  : numHitBefore ρ k = k - numMissedBefore ρ k := by
  rw [total_sub_numMissedBefore ρ k]

theorem Fin.numMissed_add_numHit (ρ : Fin n → Fin m)
  : numMissed ρ + numHit ρ = m := numMissedBefore_add_numHitBefore ρ m

theorem Fin.total_sub_numMissed (ρ : Fin n → Fin m)
  : m - numMissed ρ = numHit ρ := total_sub_numMissedBefore ρ m

theorem Fin.total_sub_numHit (ρ : Fin n → Fin m)
  : m - numHit ρ = numMissed ρ := total_sub_numHitBefore ρ m

theorem Fin.numMissed_eq_total_sub_numHit (ρ : Fin n → Fin m)
  : numMissed ρ = m - numHit ρ := numMissedBefore_eq_total_sub_numHitBefore ρ m

theorem Fin.numHit_eq_total_sub_numMissed (ρ : Fin n → Fin m)
  : numHit ρ = m - numMissed ρ := numHitBefore_eq_total_sub_numMissedBefore ρ m

theorem Fin.numMissed_le_total (ρ : Fin n → Fin m)
  : numMissed ρ ≤ m := by
  rw [numMissed_eq_total_sub_numHit ρ]
  apply Nat.sub_le

theorem Fin.numHit_le_total (ρ : Fin n → Fin m)
  : numHit ρ ≤ m := by
  rw [numHit_eq_total_sub_numMissed ρ]
  apply Nat.sub_le

theorem Fin.numMissedBefore_surjective {ρ : Fin n → Fin m} (hρ : Function.Surjective ρ) (k : ℕ)
  : numMissedBefore ρ k = k - m := by induction k with
  | zero => simp [numMissedBefore]
  | succ k I =>
    simp only [numMissedBefore, I]
    if h : k < m then
      rw [ite_cond_eq_true]
      rw [Nat.sub_eq_zero_of_le h, Nat.sub_eq_zero_of_le (Nat.le_of_lt h)]
      rw [eq_iff_iff, iff_true]
      have ⟨i, hi⟩ := hρ ⟨k, h⟩
      exact ⟨i, val_eq_of_eq hi⟩
    else
      rw [ite_cond_eq_false, Nat.one_add, Nat.succ_sub (Nat.le_of_not_lt h)]
      rw [eq_iff_iff, iff_false]
      intro ⟨i, hi⟩
      cases hi
      exact h (ρ i).prop

theorem Fin.numMissed_surjective {ρ : Fin n → Fin m} (hρ : Function.Surjective ρ)
  : numMissed ρ = 0 := by simp [numMissed, numMissedBefore_surjective hρ]

theorem Fin.numHit_surjective {ρ : Fin n → Fin m} (hρ : Function.Surjective ρ)
  : numHit ρ = m := by simp [numHit_eq_total_sub_numMissed, numMissed_surjective hρ]

theorem Fin.numMissedBefore_cast_succ_below (ρ : Fin (n + 1) → Fin m) (k : ℕ) (hk : k ≤ ρ 0)
  : numMissedBefore (ρ ∘ Fin.succ) k = numMissedBefore ρ k
  := by induction k with
  | zero => rfl
  | succ k I =>
    simp only [numMissedBefore, I (Nat.le_of_succ_le hk)]
    apply congrFun
    apply congrArg
    congr 1
    simp only [Function.comp_apply, eq_iff_iff]
    exact ⟨
      λ⟨i, hi⟩ => ⟨i.succ, hi⟩,
      λ⟨i, hi⟩ => ⟨
        i.pred (λh => by cases h; cases hi; exact Nat.not_succ_le_self _ hk),
        by simp [hi]⟩⟩

theorem Fin.numMissedBefore_cast_succ_above (ρ : Fin (n + 1) → Fin m) (k : ℕ)
  (hρ : ∀⦃i⦄, ρ 0 = ρ i -> 0 = i) (hk : ρ 0 < k)
  : numMissedBefore (ρ ∘ Fin.succ) k = numMissedBefore ρ k + 1
  := by induction k with
  | zero => cases hk
  | succ k I =>
    simp only [numMissedBefore]
    if h : ρ 0 = k then
      cases h
      rw [numMissedBefore_cast_succ_below ρ _ (le_refl _), ite_cond_eq_false, ite_cond_eq_true]
      · simp_arith
      · rw [eq_iff_iff, iff_true]
        exact ⟨0, rfl⟩
      · simp only [Function.comp_apply, eq_iff_iff, iff_false, not_exists]
        intro i hi
        cases hρ (Fin.eq_of_val_eq hi.symm)
    else
      have he : (∃i, ρ i = k) ↔ ∃i : Fin n, ρ i.succ = k := ⟨
        λ⟨i, hi⟩ => ⟨i.pred (λhi' => by simp [<-hi, hi'] at h), by simp [hi]⟩,
        λ⟨i, hi⟩ => ⟨i.succ, hi⟩⟩
      simp_arith [he, I (Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hk) h)]

theorem Fin.numMissed_cast_succ (ρ : Fin (n + 1) → Fin m) (h : ∀⦃i⦄, ρ 0 = ρ i -> 0 = i)
  : numMissed (ρ ∘ Fin.succ) = numMissed ρ + 1
  := numMissedBefore_cast_succ_above ρ m h ((ρ 0).prop)

theorem Fin.numMissed_injective {ρ : Fin n → Fin m} (hρ : Function.Injective ρ)
  : numMissed ρ = m - n := by induction n with
  | zero => simp
  | succ n I =>
    have I := I (hρ.comp (Fin.succ_injective n))
    rw [numMissed_cast_succ] at I
    rw [Nat.sub_succ]
    exact (Nat.pred_eq_of_eq_succ I.symm).symm
    apply hρ

theorem Fin.le_of_injective {ρ : Fin n → Fin m} (hρ : Function.Injective ρ)
  : n ≤ m := by
  have h := Fintype.card_le_of_injective _ hρ;
  simp only [Fintype.card_fin] at h
  exact h

theorem Fin.le_of_surjective {ρ : Fin n → Fin m} (hρ : Function.Surjective ρ)
  : m ≤ n := by
  have h := Fintype.card_le_of_surjective _ hρ;
  simp only [Fintype.card_fin] at h
  exact h

theorem Fin.numHit_injective {ρ : Fin n → Fin m} (hρ : Function.Injective ρ)
  : numHit ρ = n := by
  rw [
    numHit_eq_total_sub_numMissed,
    numMissed_injective hρ,
    Nat.sub_sub_self (le_of_injective hρ)]

theorem Fin.numMissed_injective_add_source {ρ : Fin n → Fin m} (hρ : Function.Injective ρ)
    : numMissed ρ + n = m := by
  apply Eq.trans _ (numMissed_add_numHit ρ)
  rw [numHit_injective hρ]

def Fin.lastHitBefore (ρ : Fin n → Fin m) (k : ℕ) : ℕ → ℕ
  | 0 => Fin.numMissedBefore ρ k + n
  | a + 1 =>
    if ha : a < n then
      if ρ ⟨a, ha⟩ = k then a
      else lastHitBefore ρ k a
    else
      lastHitBefore ρ k a

@[simp]
theorem Fin.lastHitBefore_zero (ρ : Fin n → Fin m) (k : ℕ)
  : lastHitBefore ρ k 0 = numMissedBefore ρ k + n := rfl

theorem Fin.lastHitBefore_le_numMissedBefore_add_n (ρ : Fin n → Fin m) (k : ℕ) (i)
  : lastHitBefore ρ k i ≤ numMissedBefore ρ k + n := by induction i with
  | zero => simp
  | succ i I =>
    simp only [lastHitBefore]
    split
    case isTrue h =>
      split
      · exact (Nat.le_of_lt h).trans (Nat.le_add_left _ _)
      · exact I
    case _ => exact I

def Fin.lastHit (ρ : Fin n → Fin m) (k : ℕ) : ℕ
  := lastHitBefore ρ k n

theorem Fin.lastHit_le_numMissed_add_n (ρ : Fin n → Fin m) (k : ℕ) (hk : k ≤ m)
  : lastHit ρ k ≤ numMissed ρ + n := by
  rw [lastHit, numMissed]
  apply (lastHitBefore_le_numMissedBefore_add_n ρ k n).trans
  rw [Nat.add_le_add_iff_right]
  apply numMissedBefore_mono
  exact hk


theorem Fin.lastHitBefore_of_hit (ρ : Fin n → Fin m) (k : ℕ) (i : Fin n) (hi : ρ i = k)
  : lastHitBefore ρ k (↑i + 1) = i := by simp [lastHitBefore, hi]

theorem Fin.lastHitBefore_lt_of_hit (ρ : Fin n → Fin m) (k : ℕ) (i : Fin n) (hi : ρ i = k) (j : ℕ)
  (hj : i < j) : lastHitBefore ρ k j < n := by induction hj with
  | refl => simp [lastHitBefore_of_hit ρ k i hi]
  | step h I =>
    simp only [lastHitBefore]
    repeat first | assumption | split

theorem Fin.lastHit_lt_of_hit (ρ : Fin n → Fin m) (k : ℕ) (h : ∃i, ρ i = k) : lastHit ρ k < n :=
  have ⟨i, hi⟩ := h;
  lastHitBefore_lt_of_hit ρ k i hi n i.prop

theorem Fin.lastHitBefore_of_not_hit (ρ : Fin n → Fin m) (k : ℕ) (a : ℕ) (h : ¬∃i, ρ i = k)
  : lastHitBefore ρ k a = Fin.numMissedBefore ρ k + n := by
  induction a with
  | zero => rfl
  | succ n I =>
    simp only [lastHitBefore]
    split
    split
    case isTrue h' => exact (h ⟨_, h'⟩).elim
    assumption
    assumption

theorem Fin.lastHit_of_not_hit (ρ : Fin n → Fin m) (k : ℕ) (h : ¬∃i, ρ i = k)
  : lastHit ρ k = Fin.numMissedBefore ρ k + n := lastHitBefore_of_not_hit ρ k n h

theorem Fin.lastHit_lt_numMissed_add_src (ρ : Fin n → Fin m) (k : ℕ) (hk : k < m)
  : lastHit ρ k < numMissed ρ + n := by
  if h : ∃i, ρ i = k then
    exact Nat.lt_of_lt_of_le (lastHit_lt_of_hit ρ k h) (Nat.le_add_left _ _)
  else
    rw [lastHit_of_not_hit _ _ h, numMissed, Nat.add_lt_add_iff_right]
    apply Nat.lt_of_lt_of_le _ (numMissedBefore_mono ρ hk)
    simp [numMissedBefore, h]

theorem Fin.lastHit_lt_src_add_numMissed_add (ρ : Fin n → Fin m) (k : ℕ) (hk : k < m)
  : lastHit ρ k < n + numMissed ρ := by
  rw [Nat.add_comm]
  exact lastHit_lt_numMissed_add_src ρ k hk

def Fin.missedInv (ρ : Fin n → Fin m) (i : Fin m) : Fin (n + numMissed ρ)
  := ⟨lastHit ρ i, lastHit_lt_src_add_numMissed_add ρ i i.prop⟩

theorem Fin.lastHit_lt_target {ρ : Fin n → Fin m} (hρ : Function.Injective ρ) (k : ℕ) (hk : k < m)
  : lastHit ρ k < m := by
  have h := lastHit_lt_numMissed_add_src ρ k hk;
  rw [numMissed_injective_add_source hρ] at h
  exact h

def Fin.semiInv {ρ : Fin n → Fin m} (hρ : Function.Injective ρ) (i : Fin m) : Fin m
  := ⟨lastHit ρ i, lastHit_lt_target hρ i i.prop⟩

@[simp]
theorem Fin.cast_comp_missedInv {ρ : Fin n → Fin m} (hρ : Function.Injective ρ)
  : Fin.cast (by rw [Nat.add_comm, numMissed_injective_add_source hρ]) ∘ missedInv ρ = semiInv hρ
  := rfl

@[simp]
theorem Fin.cast_comp_semiInv {ρ : Fin n → Fin m} (hρ : Function.Injective ρ)
  : Fin.cast (by rw [Nat.add_comm, numMissed_injective_add_source hρ]) ∘ semiInv hρ = missedInv ρ
  := rfl

def Fin.missedBelow (ρ : Fin n → Fin m) (i : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 =>
    if ∃j, ρ j = k then
      missedBelow ρ i k
    else match i with
    | 0 => k
    | i + 1 => missedBelow ρ i k

theorem Fin.missedBelow_le (ρ : Fin n → Fin m) (i k : ℕ)
  : missedBelow ρ i k ≤ k := by induction k generalizing i with
  | zero => rfl
  | succ k I =>
    simp only [missedBelow]
    split
    exact (I i).trans (Nat.le_succ _)
    split
    exact Nat.le_succ _
    exact (I _).trans (Nat.le_succ _)

theorem Fin.missedBelow_le_of_le (ρ : Fin n → Fin m) (i k : ℕ) (h : k ≤ m)
  : missedBelow ρ i k ≤ m := (missedBelow_le ρ i k).trans h

theorem Fin.missedBelow_lt_of_ne (ρ : Fin n → Fin m) (i k : ℕ) (hk : k ≠ 0)
  : missedBelow ρ i k < k := by cases k with
  | zero => cases hk rfl
  | succ k =>
    simp only [missedBelow]
    split
    exact Nat.lt_of_le_of_lt (missedBelow_le ρ i k) (Nat.lt_succ_self _)
    split
    exact Nat.lt_succ_self _
    exact Nat.lt_of_le_of_lt (missedBelow_le ρ _ k) (Nat.lt_succ_self _)

theorem Fin.missedBelow_bounded (ρ : Fin n → Fin m) (i k : ℕ) (hi : i < numMissed ρ) (hk : k ≤ m)
  : missedBelow ρ i k < m := by induction k generalizing i with
  | zero =>
    apply Nat.lt_of_le_of_lt (Nat.zero_le i)
    apply Nat.lt_of_lt_of_le hi
    apply numMissed_le_total
  | succ k I =>
    simp only [missedBelow]
    split
    apply I
    exact hi
    exact Nat.le_of_succ_le hk
    split
    exact hk
    apply I
    exact Nat.lt_of_succ_lt hi
    exact Nat.le_of_succ_le hk

theorem Fin.missedBelow_not_hit
  (ρ : Fin n → Fin m) (i k : ℕ) (hi : i < numMissedBefore ρ k)
  : ¬∃j, ρ j = missedBelow ρ i k := by induction k generalizing i with
  | zero => cases hi
  | succ k I =>
    simp only [missedBelow]
    split
    case isTrue hj =>
      apply I
      simp only [numMissedBefore, hj, ↓reduceIte, zero_add] at hi
      exact hi
    case isFalse hj =>
      split
      exact hj
      apply I
      exact Nat.lt_of_succ_lt_succ <| Nat.lt_of_lt_of_le hi (numMissedBefore_le_succ ρ k)

def Fin.missed (ρ : Fin n → Fin m) (i : Fin (numMissed ρ)) : Fin m
  := ⟨missedBelow ρ i.rev m, missedBelow_bounded ρ i.rev m i.rev.prop (le_refl m)⟩

theorem Fin.missed_not_hit (ρ : Fin n → Fin m) (i : Fin (numMissed ρ))
  : ¬∃j, ρ j = (missed ρ i : ℕ) := missedBelow_not_hit ρ i.rev m i.rev.prop

-- theorem Fin.numMissedBefore_missedBelow (ρ : Fin n → Fin m) (i) (hi : i < numMissed ρ)
--   : numMissedBefore ρ (missedBelow ρ i k) = numMissedBefore ρ k - (i + 1) := by induction k with
--   | zero => simp [missedBelow]
--   | succ k I =>
--     simp only [numMissedBefore, missedBelow]
--     split
--     case isTrue h => simp [I]
--     case isFalse h =>
--     induction i with
--     | zero => simp
--     | succ i I2 =>
--       simp only
--       rw [Nat.add_comm 1]
--       simp only [Nat.reduceSubDiff]
--       have I2 := I2 (Nat.lt_of_succ_lt hi)
--       rw [<-I2]

-- theorem Fin.numMissedBefore_missedBelow' (ρ : Fin n → Fin m) (i : Fin (numMissed ρ))
--   : numMissedBefore ρ (missedBelow ρ i m) = i.rev
--   := by simp [numMissedBefore_missedBelow, numMissed]

-- theorem Fin.numMissedBefore_missed (ρ : Fin n → Fin m) (i : Fin (numMissed ρ))
--   : numMissedBefore ρ (missed ρ i) = i := by rw [missed, numMissedBefore_missedBelow', Fin.rev_rev]

-- theorem Fin.missedInv_missed (ρ : Fin n → Fin m) (i : Fin (numMissed ρ))
--   : missedInv ρ (missed ρ i) = i.natAdd n := by
--   simp only [missedInv, natAdd, mk.injEq]
--   rw [Nat.add_comm n, lastHit_of_not_hit, add_left_inj]
--   apply numMissedBefore_missed
--   apply missed_not_hit
