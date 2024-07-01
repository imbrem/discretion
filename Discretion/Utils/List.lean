import Mathlib.Data.Set.Function
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset
import Mathlib.Init.Data.Quot

theorem List.get_append_castLE (l r : List α) (i : Fin l.length)
  : (l ++ r).get (i.castLE (by simp)) = l.get i
  := by simp [Fin.castLE, Fin.cast, List.get_append]

theorem List.get_append_castAdd (l r : List α) (i : Fin l.length)
  : (l ++ r).get ((i.castAdd r.length).cast (by rw [List.length_append])) = l.get i
  := by simp [Fin.castAdd, Fin.cast, List.get_append]

theorem List.get_append_natAdd (l r : List α) (i : Fin r.length)
  : (l ++ r).get ((i.natAdd l.length).cast (by rw [List.length_append])) = r.get i
  := by simp [Fin.natAdd, List.get_append_right]

theorem List.get_append_addNat (l r : List α) (i : Fin r.length)
  : (l ++ r).get ((i.addNat l.length).cast (by rw [List.length_append, Nat.add_comm])) = r.get i
  := by simp [Fin.addNat, List.get_append_right]

theorem List.get_append_right_fin (l r : List α) (i : Fin (l ++ r).length) (h : l.length ≤ i)
  : (l ++ r).get i = r.get ((i.cast (by rw [List.length_append, Nat.add_comm])).subNat l.length h)
  := by rw [<-List.get_append_addNat l r]; simp
