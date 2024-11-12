import Mathlib.Data.Set.Finite
import Mathlib.Data.Sum.Order
import Mathlib.Order.Interval.Finset.Defs

import Discretion.Utils.Tuple

import Discretion.OrderOrder

def Fin.pocast {n m} (h : n = m) (p: PartialOrder (Fin n)) : PartialOrder (Fin m) where
  le a b := p.le (a.cast h.symm) (b.cast h.symm)
  lt a b := p.lt (a.cast h.symm) (b.cast h.symm)
  le_refl a := by cases h; exact le_refl a
  le_trans a b c := by cases h; exact le_trans
  le_antisymm a b := by cases h; exact le_antisymm
  lt_iff_le_not_le a b := by cases h; exact lt_iff_le_not_le

@[simp]
theorem Fin.pocast_rfl {n} {p : PartialOrder (Fin n)} : pocast rfl p = p := rfl

@[simp]
theorem Fin.pocast_pocast {n m k} {hnm : n = m} {hmk : m = k} {p : PartialOrder (Fin n)}
  : pocast hmk (pocast hnm p) = pocast (hnm.trans hmk) p
  := by cases hnm; cases hmk; rfl

@[simp]
theorem Fin.heq_pocast {n m} {h : n = m} {p: PartialOrder (Fin n)}
  : HEq (pocast h p) p := by cases h; rfl

@[simp]
theorem Fin.heq_pocast_pocast {n m m'} {h : n = m} {h' : n = m'} {p: PartialOrder (Fin n)}
  : HEq (pocast h p) (pocast h' p) := by cases h; cases h'; rfl

def Fin.poseq {n m} (p : PartialOrder (Fin n)) (q : PartialOrder (Fin m))
  : PartialOrder (Fin (n + m)) where
  le a b := a.addCases (λa => b.addCases (λb => p.le a b) ⊤) (λa => b.addCases ⊥ (λb => q.le a b))
  lt a b := a.addCases  (λa => b.addCases (λb => p.lt a b) ⊤) (λa => b.addCases ⊥ (λb => q.lt a b))
  le_refl a := a.addCases (λa => by simp) (λa => by simp)
  le_trans a b c := by
    cases a using Fin.addCases <;>
    cases b using Fin.addCases <;>
    cases c using Fin.addCases <;>
    simp <;>
    first | apply p.le_trans | apply q.le_trans
  lt_iff_le_not_le a b := by
    cases a using Fin.addCases <;>
    cases b using Fin.addCases <;>
    simp <;>
    first | apply p.lt_iff_le_not_le | apply q.lt_iff_le_not_le
  le_antisymm a b := by
    cases a using Fin.addCases <;>
    cases b using Fin.addCases <;>
    simp
    case left.left => apply p.le_antisymm
    case right.right =>
      simp only [Fin.ext_iff, Fin.coe_natAdd, add_right_inj]
      rw [<-Fin.ext_iff]
      apply q.le_antisymm

theorem Fin.poseq_instPartialOrder {n m} :
  poseq (n := n) (m := m) instPartialOrder instPartialOrder = instPartialOrder
  := PartialOrder.ext (λa b => by
    cases a using Fin.addCases <;>
    cases b using Fin.addCases <;>
    simp only [poseq] <;>
    (try simp only [Fin.le_def, Fin.lt_def]) <;>
    simp <;> omega
  )

theorem Fin.poseq_zero {n} {p : PartialOrder (Fin n)} : poseq (n := n) (m := 0) p q = p
  := PartialOrder.ext (λa b => by simp [poseq, addCases, castLT])

theorem Fin.zero_poseq {m} {q : PartialOrder (Fin m)}
  : poseq (n := 0) (m := m) p q = pocast (Nat.zero_add m).symm q
  := PartialOrder.ext (λa b => by simp [poseq, pocast, addCases])

theorem Fin.poseq_assoc {n m k}
  {p : PartialOrder (Fin n)} {q : PartialOrder (Fin m)} {r : PartialOrder (Fin k)}
  : poseq (poseq p q) r = pocast (Nat.add_assoc n m k).symm (poseq p (poseq q r))
  := PartialOrder.ext (λa b => by
    cases a using Fin.addCases3 <;>
    cases b using Fin.addCases3 <;>
    simp [
      poseq, pocast, cast_assoc_castAdd_castAdd, cast_assoc_castAdd_natAdd, cast_assoc_natAdd
    ]
  )

theorem Fin.poseq_assoc' {n m k}
  {p : PartialOrder (Fin n)} {q : PartialOrder (Fin m)} {r : PartialOrder (Fin k)}
  : poseq p (poseq q r) = pocast (Nat.add_assoc n m k) (poseq (poseq p q) r)
  := by rw [poseq_assoc]; rfl

-- TODO: poseq_mono

-- TODO: poseq_eq_bot_iff

def Fin.popar {n m} (p : PartialOrder (Fin n)) (q : PartialOrder (Fin m))
  : PartialOrder (Fin (n + m)) where
  le a b := a.addCases (λa => b.addCases (λb => p.le a b) ⊥) (λa => b.addCases ⊥ (λb => q.le a b))
  lt a b := a.addCases  (λa => b.addCases (λb => p.lt a b) ⊥) (λa => b.addCases ⊥ (λb => q.lt a b))
  le_refl a := a.addCases (λa => by simp) (λa => by simp)
  le_trans a b c := by
    cases a using Fin.addCases <;>
    cases b using Fin.addCases <;>
    cases c using Fin.addCases <;>
    simp <;>
    first | apply p.le_trans | apply q.le_trans
  lt_iff_le_not_le a b := by
    cases a using Fin.addCases <;>
    cases b using Fin.addCases <;>
    simp <;>
    first | apply p.lt_iff_le_not_le | apply q.lt_iff_le_not_le
  le_antisymm a b := by
    cases a using Fin.addCases <;>
    cases b using Fin.addCases <;>
    simp
    case left.left => apply p.le_antisymm
    case right.right =>
      simp only [Fin.ext_iff, Fin.coe_natAdd, add_right_inj]
      rw [<-Fin.ext_iff]
      apply q.le_antisymm

theorem Fin.popar_le_poseq {n m} {p : PartialOrder (Fin n)} {q : PartialOrder (Fin m)}
  : popar p q ≤ poseq p q := λa b => by
  cases a using Fin.addCases <;> cases b using Fin.addCases <;> simp [popar, poseq]

--TODO: if n ≠ 0 and m ≠ 0 then popar_ne_poseq. In fact, popar_eq_poseq ↔ (n = 0) ∧ (m = 0)

theorem Fin.popar_bot {n m} : popar (n := n) (m := m) ⊥ ⊥ = ⊥
  := PartialOrder.ext (λa b => by
    cases a using Fin.addCases <;>
    cases b using Fin.addCases <;>
    simp [popar, Fin.ext_iff] <;>
    omega
  )

theorem Fin.popar_zero {n} {p : PartialOrder (Fin n)} : popar (n := n) (m := 0) p q = p
  := PartialOrder.ext (λa b => by simp [popar, addCases, castLT])

theorem Fin.zero_popar {m} {q : PartialOrder (Fin m)}
  : popar (n := 0) (m := m) p q = pocast (Nat.zero_add m).symm q
  := PartialOrder.ext (λa b => by simp [popar, pocast, addCases])

theorem Fin.popar_assoc {n m k}
  {p : PartialOrder (Fin n)} {q : PartialOrder (Fin m)} {r : PartialOrder (Fin k)}
  : popar (popar p q) r = pocast (Nat.add_assoc n m k).symm (popar p (popar q r))
  := PartialOrder.ext (λa b => by
    cases a using Fin.addCases3 <;>
    cases b using Fin.addCases3 <;>
    simp [
      popar, pocast, cast_assoc_castAdd_castAdd, cast_assoc_castAdd_natAdd, cast_assoc_natAdd
    ]
  )

theorem Fin.popar_assoc' {n m k}
  {p : PartialOrder (Fin n)} {q : PartialOrder (Fin m)} {r : PartialOrder (Fin k)}
  : popar p (popar q r) = pocast (Nat.add_assoc n m k) (popar (popar p q) r)
  := by rw [popar_assoc]; rfl

--TODO: popar_mono

--TODO: popar_eq_bot_iff

def Fin.porseq {n m} (p : PartialOrder (Fin n)) (q : PartialOrder (Fin m))
  : PartialOrder (Fin (n + m)) where
  le a b := a.addCases (λa => b.addCases (λb => p.le a b) ⊥) (λa => b.addCases ⊤ (λb => q.le a b))
  lt a b := a.addCases  (λa => b.addCases (λb => p.lt a b) ⊥) (λa => b.addCases ⊤ (λb => q.lt a b))
  le_refl a := a.addCases (λa => by simp) (λa => by simp)
  le_trans a b c := by
    cases a using Fin.addCases <;>
    cases b using Fin.addCases <;>
    cases c using Fin.addCases <;>
    simp <;>
    first | apply p.le_trans | apply q.le_trans
  lt_iff_le_not_le a b := by
    cases a using Fin.addCases <;>
    cases b using Fin.addCases <;>
    simp <;>
    first | apply p.lt_iff_le_not_le | apply q.lt_iff_le_not_le
  le_antisymm a b := by
    cases a using Fin.addCases <;>
    cases b using Fin.addCases <;>
    simp
    case left.left => apply p.le_antisymm
    case right.right =>
      simp only [Fin.ext_iff, Fin.coe_natAdd, add_right_inj]
      rw [<-Fin.ext_iff]
      apply q.le_antisymm

theorem Fin.porseq_zero {n} {p : PartialOrder (Fin n)} : porseq (n := n) (m := 0) p q = p
  := PartialOrder.ext (λa b => by simp [porseq, addCases, castLT])

theorem Fin.zero_porseq {m} {q : PartialOrder (Fin m)}
  : porseq (n := 0) (m := m) p q = pocast (Nat.zero_add m).symm q
  := PartialOrder.ext (λa b => by simp [porseq, pocast, addCases])

-- def poseq1 {n} (p : PartialOrder (Fin n)) : PartialOrder (Fin (n + 1))
--   := sorry

-- theorem poseq1_instPartialOrder {n}
--   : partialOrderSeq1 (n := n) Fin.instPartialOrder = Fin.instPartialOrder
--   := sorry

-- def popar1 {n} (p : PartialOrder (Fin n)) : PartialOrder (Fin (n + 1))
--   := sorry

-- theorem popar1_bot {n}
--   : partialOrderPar1 (n := n) ⊥ = ⊥
--   := sorry

-- def Fin.poflatten (arity : Fin n → ℕ) (po : ∀i, PartialOrder (Fin (arity i)))
--   : PartialOrder (Fin (∑i, arity i)) where
--   le a b := sorry
--   lt a b := sorry
--   le_refl := sorry
--   le_trans := sorry
--   le_antisymm := sorry
--   lt_iff_le_not_le := sorry
