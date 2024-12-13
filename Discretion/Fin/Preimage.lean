import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Algebra.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.BigOperators.Group.Finset

variable {α : Type u} {β : Type v} [Fintype α] [DecidableEq β]

def Finset.rangeF (f : α → β) : Finset β := Finset.univ.image f

@[simp]
theorem Finset.mem_rangeF_iff (f : α → β) (b : β) : b ∈ rangeF f ↔ ∃a, f a = b := by
  simp [rangeF]

def Finset.preimageF (f : α → β) (bs : Finset β)
  : Finset α := Finset.univ.filter (f · ∈ bs)

theorem Finset.mem_preimageF_iff (f : α → β) (bs : Finset β)
  (a : α) : a ∈ preimageF f bs ↔ f a ∈ bs := by simp [preimageF]

theorem Finset.preimageF_eq (f : α → β) (bs : Finset β)
  : preimageF f bs = f⁻¹' bs := by ext a; simp [mem_preimageF_iff]

@[simp]
theorem Finset.preimageF_id [DecidableEq α] : preimageF (α := α) (β := α) id = id := by
  ext; simp [mem_preimageF_iff]

@[simp]
theorem Finset.preimageF_empty (f : α → β) : preimageF f ∅ = ∅ := by ext a; simp [mem_preimageF_iff]

@[simp]
theorem Finset.preimageF_univ [Fintype β] (f : α → β) : preimageF f Finset.univ = Finset.univ := by
  ext a; simp [mem_preimageF_iff]

theorem Finset.preimageF_union [DecidableEq α] (f : α → β) (bs bs' : Finset β)
  : preimageF f (bs ∪ bs') = preimageF f bs ∪ preimageF f bs' := by
  ext a; simp only [mem_preimageF_iff, mem_union]

theorem Finset.preimageF_inter [DecidableEq α] (f : α → β) (bs bs' : Finset β)
  : preimageF f (bs ∩ bs') = preimageF f bs ∩ preimageF f bs' := by
  ext a; simp only [mem_preimageF_iff, mem_inter]

theorem Finset.preimageF_disjoint
  (f : α → β) (bs bs' : Finset β) (hbs : Disjoint bs bs')
  : Disjoint (preimageF f bs) (preimageF f bs')
  := by
  simp only [disjoint_iff_ne, ne_eq, forall_mem_not_eq, mem_preimageF_iff] at *
  intro b hb c hc h; cases h
  exact hbs _ hb hc

theorem Finset.eq_of_preimageF (f : α → β) (a : α) (b c : β)
  (hb : a ∈ preimageF f {b}) (hc : a ∈ preimageF f {c}) : b = c := open Classical in by
  have h : a ∈ preimageF f ({b} ∩ {c}) := by have _ := decEq α; simp [preimageF_inter, *]
  by_contra
  simp [*] at h

theorem Finset.preimageF_empty_of_disjoint
  (f : α → β) (bs : Finset β) (hb : Disjoint bs (rangeF f)) : preimageF f bs = ∅ := by
  ext k
  simp only [mem_preimageF_iff, not_mem_empty, iff_false]
  simp only [disjoint_iff_ne, mem_rangeF_iff, ne_eq, forall_exists_index,
    forall_apply_eq_imp_iff] at hb
  exact λhk => hb _ hk _ rfl

theorem Finset.disjoint_of_preimageF_empty
  (f : α → β) (bs : Finset β) (hb : preimageF f bs = ∅) : Disjoint bs (rangeF f) := by
  simp [disjoint_iff_ne]
  intro b hb' c h
  cases h
  rw [<-mem_preimageF_iff, hb] at hb'
  cases hb'

theorem Finset.preimageF_empty_iff {f : α → β} {bs : Finset β}
  : preimageF f bs = ∅ ↔ Disjoint bs (rangeF f)
  := ⟨disjoint_of_preimageF_empty f bs, preimageF_empty_of_disjoint f bs⟩

theorem Finset.preimageF1_empty_iff {f : α → β} {b : β}
  : preimageF f {b} = ∅ ↔ b ∉ rangeF f
  := by simp [preimageF_empty_iff]

theorem Finset.preimageF1_empty_of (f : α → β) (b : β)
  : b ∉ rangeF f → preimageF f {b} = ∅ := preimageF1_empty_iff.mpr

theorem Finset.not_mem_range_of_preimageF1_empty (f : α → β) (b : β)
  : preimageF f {b} = ∅ → b ∉ rangeF f := preimageF1_empty_iff.mp

section AddCommMonoid

variable [AddCommMonoid γ]

open Finset

def Fintype.preSum (f : α → β) (g : α → γ) (b : β) : γ := ∑ a ∈ preimageF f {b}, g a

@[simp]
theorem Fintype.preSum_not_mem_image (f : α → β) (b : β) (g : α → γ) (hb : b ∉ rangeF f)
  : preSum f g b = 0 := by simp [preSum, preimageF1_empty_of, hb]

theorem Fintype.preSum_add (f : α → β) (g h : α → γ)
  : preSum f (g + h) = preSum f g + preSum f h := by ext b; simp [preSum, Finset.sum_add_distrib]

end AddCommMonoid

section OrderedAddCommMonoid

variable [OrderedAddCommMonoid γ]

theorem Fintype.preSum_mono (f : α → β) {lo hi : α → γ} (h : lo ≤ hi) : preSum f lo ≤ preSum f hi
  := by
  intro b
  simp [Fintype.preSum]
  apply Finset.sum_le_sum
  intro i _
  apply h

end OrderedAddCommMonoid

def Fintype.preCard (f : α → β) (b : β) : ℕ
  := (Finset.preimageF f {b}).card
