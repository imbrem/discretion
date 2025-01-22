import Mathlib.Data.Set.Function
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Quot
import Mathlib.Data.Fintype.Quotient

theorem Quotient.finChoice_eq_choice {ι : Type u} [Fintype ι] [DecidableEq ι] {α : ι → Type v}
  [S : (i : ι) → Setoid (α i)] (f : (i : ι) → Quotient (S i))
  : Quotient.finChoice f = Quotient.choice f := by
  rw [choice, <-Quotient.finChoice_eq]
  simp

theorem Quotient.forall_of_choice_eq {ι : Type u} {α : ι → Type v} [S : (i : ι) → Setoid (α i)]
  {f : (i : ι) → Quotient (S i)} {g : (i : ι) → α i}
  (h : Quotient.choice f = ⟦g⟧)
  : ∀i, f i = ⟦g i⟧ := by
  rw [Quotient.choice] at h
  simp only [eq] at h
  intro i
  have h := Quotient.sound <| h i
  simp only [out_eq] at h
  exact h

theorem Quotient.forall_of_finChoice_eq {ι : Type u} [Fintype ι] [DecidableEq ι] {α : ι → Type v}
  [S : (i : ι) → Setoid (α i)] {f : (i : ι) → Quotient (S i)} {g : (i : ι) → α i}
  : Quotient.finChoice f = ⟦g⟧ → ∀i, f i = ⟦g i⟧ := by
  rw [finChoice_eq_choice]
  apply forall_of_choice_eq
