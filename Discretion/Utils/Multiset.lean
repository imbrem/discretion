import Mathlib.Data.Set.Function
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open Classical in
theorem Finset.sum_nat_eq_zero (s : Finset α) (f : α → ℕ)
  : s.sum f = 0 ↔ ∀a ∈ s, f a = 0 := by induction s using Finset.induction with
    | empty => simp
    | insert a ha I => simp [sum_insert, I]

theorem Finset.sum_nat_univ_eq_zero [Fintype α] (f : α → ℕ)
  : Finset.univ.sum f = 0 ↔ ∀a, f a = 0 := by
  rw [Finset.sum_nat_eq_zero]
  simp

theorem Multiset.map_finsum (i : Finset ι) (f : ι → Multiset α) (g : α → β)
  : (i.sum f).map g = i.sum (Multiset.map g ∘ f)
  := by
  open Classical in induction i using Finset.induction with
  | empty => rfl
  | insert =>
    rw [Finset.sum_insert]
    simp [*]
    assumption

theorem Multiset.not_mem_sum_map (s : Multiset ι) (f : ι → Multiset α) (a : α)
  : a ∉ Multiset.sum (s.map f) ↔ (∀i ∈ s, a ∉ f i) := by
  induction s using Multiset.induction <;> simp [*]

theorem Multiset.mem_sum_map (s : Multiset ι) (f : ι → Multiset α) (a : α)
  : a ∈ Multiset.sum (s.map f) ↔ (∃i ∈ s, a ∈ f i) := by
  induction s using Multiset.induction <;> simp [*]

theorem Multiset.not_mem_finsum (s : Finset ι) (f : ι → Multiset α) (a : α)
  : a ∉ s.sum f ↔ (∀i ∈ s, a ∉ f i) := not_mem_sum_map s.val f a

theorem Multiset.mem_finsum (s : Finset ι) (f : ι → Multiset α) (a : α)
  : a ∈ s.sum f ↔ (∃i ∈ s, a ∈ f i) := mem_sum_map s.val f a

theorem Multiset.not_mem_finsum_univ [Fintype ι] (f : ι → Multiset α) (a : α)
  : a ∉ Finset.univ.sum f ↔ (∀i, a ∉ f i) := by
  rw [Multiset.not_mem_finsum]
  simp

theorem Multiset.mem_finsum_univ [Fintype ι] (f : ι → Multiset α) (a : α)
  : a ∈ Finset.univ.sum f ↔ (∃i, a ∈ f i) := by
  rw [Multiset.mem_finsum]
  simp

theorem Multiset.mem_of_mem_cons_of_ne {a b : α} {l : Multiset α}
  (h : a ∈ b ::ₘ l) (h' : a ≠ b) : a ∈ l := by
  simp only [mem_cons] at h
  cases h with
  | inl h => exact (h' h).elim
  | inr h => exact h
