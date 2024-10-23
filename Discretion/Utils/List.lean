import Mathlib.Data.Set.Function
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Finset.Basic

theorem List.get_append_castLE (l r : List α) (i : Fin l.length)
  : (l ++ r).get (i.castLE (by simp)) = l.get i
  := by simp [Fin.castLE, Fin.cast, List.getElem_append]

theorem List.get_append_castAdd (l r : List α) (i : Fin l.length)
  : (l ++ r).get ((i.castAdd r.length).cast (by rw [List.length_append])) = l.get i
  := by simp [Fin.castAdd, Fin.cast, List.getElem_append]

theorem List.get_append_natAdd (l r : List α) (i : Fin r.length)
  : (l ++ r).get ((i.natAdd l.length).cast (by rw [List.length_append])) = r.get i
  := by simp [Fin.natAdd, List.getElem_append_right]

theorem List.get_append_addNat (l r : List α) (i : Fin r.length)
  : (l ++ r).get ((i.addNat l.length).cast (by rw [List.length_append, Nat.add_comm])) = r.get i
  := by simp [Fin.addNat, List.getElem_append_right]

theorem List.get_append_right_fin (l r : List α) (i : Fin (l ++ r).length) (h : l.length ≤ i)
  : (l ++ r).get i = r.get ((i.cast (by rw [List.length_append, Nat.add_comm])).subNat l.length h)
  := by rw [<-List.get_append_addNat l r]; simp

theorem List.getElem_append_left_fin (l r : List α) (i : Fin l.length)
  : (l ++ r)[i] = l[i]
  := by simp [Fin.castLE, Fin.cast, List.getElem_append]

theorem List.getElem_append_natAdd (l r : List α) (i : Fin r.length)
  : (l ++ r)[i.natAdd l.length] = r[i]
  := by simp [Fin.natAdd, List.getElem_append_right]

theorem List.getElem_append_addNat (l r : List α) (i : Fin r.length)
  : (l ++ r)[(i.addNat l.length).cast (by rw [Nat.add_comm])] = r[i]
  := by simp [Fin.addNat, List.getElem_append_right]

theorem List.getElem_append_add_left (l r : List α) (i : ℕ)
  (hi : i + l.length < (l ++ r).length)
  : (l ++ r)[i + l.length]
  = r[i]'(by
    simp only [length_append, Nat.add_comm l.length, Nat.add_lt_add_iff_right] at hi;
    exact hi)
  := by rw [List.getElem_append_right] <;> simp

theorem List.getElem_append_add_right (l r : List α) (i : ℕ)
  (hi : l.length + i < (l ++ r).length)
  : (l ++ r)[l.length + i]
  = r[i]'(by
    simp only [length_append, Nat.add_lt_add_iff_left] at hi;
    exact hi)
  := by simp [Nat.add_comm l.length, List.getElem_append_add_left]

theorem List.getElem_append_right_fin (l r : List α) (i : Fin (l ++ r).length) (h : l.length ≤ i)
  : (l ++ r)[i] = r[(i.cast (by rw [List.length_append, Nat.add_comm])).subNat l.length h]
  := by rw [<-List.getElem_append_addNat l r]; simp
