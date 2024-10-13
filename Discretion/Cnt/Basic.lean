import Mathlib.Data.ENat.Basic
import Mathlib.Data.Countable.Defs
import Mathlib.Data.Fintype.Basic

import Discretion.Utils.ENat

def Cnt (n : ℕ∞) := {i : ℕ // i < n}

def Fin.toCnt {n : ℕ} (i : Fin n) : Cnt n := ⟨i.val, by convert i.prop; simp⟩

def Cnt.toFin {n : ℕ} (i : Cnt n) : Fin n := ⟨i.val, by convert i.prop; simp⟩

theorem Cnt.toFin_toCnt {n : ℕ} (i : Cnt n) : i.toFin.toCnt = i :=
  by cases i; simp [Fin.toCnt, Cnt.toFin]

theorem Fin.toCnt_toFin {n : ℕ} (i : Fin n) : i.toCnt.toFin = i :=
  by cases i; simp [Fin.toCnt, Cnt.toFin]

def Cnt.ofNatFin {n : ℕ} [h : NeZero n] (a : ℕ) : Cnt n
  := ⟨a % n, by simp [Nat.mod_lt _ (Nat.pos_of_neZero _)]⟩

def Cnt.ofNatTop (a : ℕ) : Cnt ⊤ := ⟨a, by simp⟩

def Cnt.ofNat {n} [h : NeZero n] (a : ℕ) : Cnt n := match n, h with
  | ⊤, _ => ofNatTop a
  | (n : ℕ), h => ofNatFin (h := ⟨by convert h.out; simp⟩) a

instance [NeZero n] : OfNat (Cnt n) i where
  ofNat := Cnt.ofNat i

def Cnt.succ {n : ℕ∞} (i : Cnt n) : Cnt (n + 1) := ⟨
    i.val + 1, by match n with
      | ⊤ => exact ENat.coe_lt_top (i.val + 1)
      | (n : ℕ) => exact (Nat.cast_lt.mpr (Nat.succ_lt_succ (Nat.cast_lt.mp i.prop)))
  ⟩

def Cnt.castSucc {n : ℕ∞} (i : Cnt n) : Cnt (n + 1) := ⟨i.val, lt_of_lt_of_le i.prop (by simp)⟩

instance : Countable (Cnt n) where exists_injective_nat' := ⟨Subtype.val, Subtype.val_injective⟩

instance : DecidableEq (Cnt n) := (inferInstance : DecidableEq (Subtype _))

def List.cntRange (n : ℕ) : List (Cnt n)
  := List.pmap Subtype.mk (List.range n) (λ_ h => by convert h; simp)

def Cnt.elim0 (p : Cnt 0) : α := False.elim (by convert p.prop; simp)

@[simp]
theorem Cnt.mk_zero {n} : (⟨0, by simp⟩ : Cnt (n + 1)) = (0 : Cnt (n + 1)) :=
  match n with
  | ⊤ => rfl
  | (n : ℕ) => rfl

def Cnt.induction {n : ℕ∞} {motive : Cnt (n + 1) → Sort u}
  (zero : motive 0) (succ : ∀i : Cnt n, motive i.castSucc → motive i.succ)
  : (p : Cnt (n + 1)) → motive p
  | ⟨i, hi⟩ => go i hi
  where
  -- Use a curried function so that this is structurally recursive
  go : ∀ (i : Nat) (hi : i < n + 1), motive ⟨i, hi⟩
  | 0, hi => by rwa [Cnt.mk_zero]
  | i+1, hi => succ
    ⟨i, ENat.lt_of_succ_lt_succ hi⟩
    (go i (ENat.lt_succ_of_lt (ENat.lt_of_succ_lt_succ hi)))

def Cnt.cases {n : ℕ∞} {motive : Cnt (n + 1) → Sort u}
  (zero : motive 0) (succ : ∀i : Cnt n, motive i.succ) : (p : Cnt (n + 1)) → motive p
  := induction zero (λi _ => succ i)

instance Cnt.fintype (n : ℕ) : Fintype (Cnt n) where
  elems := (List.cntRange n).toFinset
  complete x := by
    simp [List.cntRange]
    cases x with
    | mk x hx => exact ⟨x, by convert hx; rw [Nat.cast_lt], rfl⟩
