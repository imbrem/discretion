import Mathlib.Data.Set.Function
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Basic

import Mathlib.Order.SetNotation

theorem Set.iUnion_union_iUnion {α β : Type _} {f g : α → Set β} :
  Set.iUnion f ∪ Set.iUnion g = ⋃x, f x ∪ g x := by ext x; simp [exists_or]

theorem Set.biUnion_union_biUnion {α β : Type _} {s : Set α} {f g : α → Set β}:
  (⋃x ∈ s, f x) ∪ (⋃x ∈ s, g x) = ⋃x ∈ s, f x ∪ g x := by
  rw [iUnion_union_iUnion]
  apply congrArg
  ext a
  simp [and_or_left]

@[simp]
theorem Set.eqOn_insert {s : Set α} {f₁ f₂ : α → β}
  : (insert a s).EqOn f₁ f₂ ↔ s.EqOn f₁ f₂ ∧ f₁ a = f₂ a := by
  rw [<-union_singleton, eqOn_union]
  simp [*]

theorem Set.eqOn_iUnion {f : α → Set β} {g h : β → γ}
  : (Set.iUnion f).EqOn g h ↔ ∀a, (f a).EqOn g h := by
  simp only [EqOn, mem_iUnion, forall_exists_index]
  rw [forall_comm]

theorem Set.eqOn_biUnion {s : Set α} {f : α → Set β} {g h : β → γ}
  : ((⋃x ∈ s, f x).EqOn g h) ↔ (∀x ∈ s, (f x).EqOn g h) := by
  simp only [EqOn, mem_iUnion, exists_prop', nonempty_prop, forall_exists_index, and_imp]
  rw [forall_comm]
  apply forall_congr'
  intro _
  rw [forall_comm]

-- TODO: think about this...
@[simp]
theorem Set.eqOn_insert' {s : Set α} {f₁ f₂ : α → β}
  : (s.insert a).EqOn f₁ f₂ ↔ s.EqOn f₁ f₂ ∧ f₁ a = f₂ a := eqOn_insert

theorem Set.EqOn.insert {s : Set α} {f₁ f₂ : α → β} (heq : s.EqOn f₁ f₂) (ha : f₁ a = f₂ a)
  : (insert a s).EqOn f₁ f₂ := eqOn_insert.mpr ⟨heq, ha⟩

theorem Set.eqOn_comp_left_iff_of_eqOn_injOn_image
  {s : Set α} {f₁ f₂ : α → β} {g₁ g₂ : β → γ}
  (hf₁ : (f₁ '' s ∪ f₂ '' s).InjOn g₁)
  (hg : (f₁ '' s ∪ f₂ '' s).EqOn g₁ g₂)
  : s.EqOn (g₁ ∘ f₁) (g₂ ∘ f₂) ↔ s.EqOn f₁ f₂ := by
  simp only [EqOn, iff_iff_eq]
  apply forall_congr
  intro a
  apply propext
  simp only [Function.comp_apply]
  · constructor
    · intro h ha
      apply hf₁
      · exact mem_union_left _ (mem_image_of_mem _ ha)
      · exact mem_union_right _ (mem_image_of_mem _ ha)
      · rw [<-hg] at h
        · exact h ha
        · exact mem_union_right _ (mem_image_of_mem _ ha)
    · intro h ha; rw [h ha, hg];  exact mem_union_right _ (mem_image_of_mem _ ha)

theorem Set.eqOn_comp_left_iff_of_injOn_image
  {s : Set α} {f₁ f₂ : α → β} {g : β → γ} (hf : (f₁ '' s ∪ f₂ '' s).InjOn g)
  : s.EqOn (g ∘ f₁) (g ∘ f₂) ↔ s.EqOn f₁ f₂
  := eqOn_comp_left_iff_of_eqOn_injOn_image hf (λ_ _ => rfl)

theorem Set.eqOn_comp_left_iff_of_injective
  {s : Set α} {f₁ f₂ : α → β} {g : β → γ} (hf : Function.Injective g)
  : s.EqOn (g ∘ f₁) (g ∘ f₂) ↔ s.EqOn f₁ f₂
  := eqOn_comp_left_iff_of_injOn_image (injOn_of_injective hf)

theorem Set.iUnion_applied
  {s : Set α} {f : β → Set γ} {g : α → β}
  : ⋃ a ∈ s, f (g a) = ⋃ b ∈ g '' s, f b
  := by simp

theorem Set.Iio_intersect_Iio [LinearOrder α] {a b : α} : Iio a ∩ Iio b = Iio (a ⊓ b) := by
  ext x; simp

theorem Set.Iio_inf [LinearOrder α] {a b : α} : Iio (a ⊓ b) = Iio a ∩ Iio b := by
  ext x; simp

theorem Set.Iio_sup [LinearOrder α] {a b : α} : Iio (a ⊔ b) = Iio a ∪ Iio b := by
  ext x; simp

theorem Set.Iio_min [LinearOrder α] {a b : α} : Iio (min a b) = Iio a ∩ Iio b := by
  ext x; simp

theorem Set.Iio_max [LinearOrder α] {a b : α} : Iio (max a b) = Iio a ∪ Iio b := by
  ext x; simp

theorem Set.Iio_finset_sup [LinearOrder β] [OrderBot β] (s : Finset α) (f : α → β)
  : Iio (s.sup f) = ⋃x ∈ s, Set.Iio (f x)
  := by open Classical in induction s using Finset.induction <;> simp [Iio_sup, *]

theorem Set.Iio_finset_univ_sup [Fintype α] [LinearOrder β] [OrderBot β] (f : α → β)
  : Iio (Finset.univ.sup f) = ⋃x, Set.Iio (f x)
  := by simp [Iio_finset_sup]
