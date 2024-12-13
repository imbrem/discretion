import Mathlib.Order.Monotone.Basic
import Mathlib.Order.BoundedOrder.Basic
import Mathlib.Order.Nat
import Mathlib.Order.Disjoint
import Mathlib.Algebra.BigOperators.Group.Finset
import Mathlib.Data.Multiset.Functor

import Discretion.Vector.Basic
import Discretion.Fin.Preimage

section Preorder

variable {α} [Preorder α] {s t u : α} {ρ σ : α → α}

class BoundedOn (s : α) (t : α) (ρ : α → α) : Prop where
  bounded_on : ∀i, i < s → ρ i < t

class BoundedFrom (s : α) (t : α) (ρ : α → α) : Prop where
  bounded_from : ∀i, ρ i < t → i < s

theorem BoundedOn.comp (s t u) [BoundedOn s t σ] [BoundedOn t u ρ] : BoundedOn s u (ρ ∘ σ) where
  bounded_on i h := bounded_on (s := t) (σ i) (bounded_on i h)

theorem BoundedFrom.comp (s t u) [BoundedFrom s t σ] [BoundedFrom t u ρ] : BoundedFrom s u (ρ ∘ σ) where
  bounded_from i h := bounded_from i (bounded_from (s := t) (σ i) h)

class BoundedIff (s : α) (t : α) (ρ : α → α) extends BoundedOn s t ρ, BoundedFrom s t ρ : Prop

instance BoundedOn.from_bot [OrderBot α] : BoundedOn ⊥ t ρ where
  bounded_on i h := by simp at h

instance BoundedFrom.to_bot [OrderBot α] : BoundedFrom s ⊥ ρ where
  bounded_from i h := by simp at h

namespace BoundedIff

export BoundedOn (bounded_on)

export BoundedFrom (bounded_from)

theorem of_bot [OrderBot α] : BoundedIff ⊥ ⊥ ρ where

-- TODO: fiddle with priority?
instance mkInst [BoundedOn s t ρ] [BoundedFrom s t ρ] : BoundedIff s t ρ where
  bounded_on := bounded_on
  bounded_from := bounded_from

theorem comp (t) [BoundedIff s t σ] [BoundedIff t u ρ] : BoundedIff s u (ρ ∘ σ) where
  bounded_on := (BoundedOn.comp s t u).bounded_on
  bounded_from := (BoundedFrom.comp s t u).bounded_from

instance of_id : BoundedIff s s id where
  bounded_on _ h := h
  bounded_from _ h := h

theorem bounded_iff [BoundedIff s t ρ] : ∀i, i < s ↔ ρ i < t := λi => ⟨bounded_on i, bounded_from i⟩

end BoundedIff

class BoundedInj (s : α) (ρ : α → α) : Prop where
  bounded_inj : ∀i j, i < s → j < s → ρ i = ρ j → i = j

class BoundedMono (s : α) (ρ : α → α) : Prop where
  bounded_mono : ∀i j, i < s → j < s → i ≤ j → ρ i ≤ ρ j

class BoundedStrictMono (s : α) (ρ : α → α) : Prop where
  bounded_strict_mono : ∀i j, i < s → j < s → i < j → ρ i < ρ j

instance BoundedInj.of_id : BoundedInj s id where
  bounded_inj _ _ _ _ h := h

instance BoundedMono.of_id : BoundedMono s id where
  bounded_mono _ _ _ _ h := h

instance BoundedStrictMono.of_id : BoundedStrictMono s id where
  bounded_strict_mono _ _ _ _ h := h

instance BoundedInj.of_bot [OrderBot α] : BoundedInj ⊥ ρ where
  bounded_inj i j h := by simp at h

instance BoundedMono.of_bot [OrderBot α] : BoundedMono ⊥ ρ where
  bounded_mono i j h := by simp at h

instance BoundedStrictMono.of_bot [OrderBot α] : BoundedStrictMono ⊥ ρ where
  bounded_strict_mono i j h := by simp at h

end Preorder

instance BoundedOn.from_zero : BoundedOn (0 : ℕ) t ρ := from_bot

instance BoundedFrom.to_zero : BoundedFrom s (0 : ℕ) ρ := to_bot

instance BoundedIff.of_zero : BoundedIff (0 : ℕ) (0 : ℕ) ρ := of_bot

instance BoundedInj.of_zero : BoundedInj (0 : ℕ) ρ := of_bot

instance BoundedMono.of_zero : BoundedMono (0 : ℕ) ρ := of_bot

instance BoundedStrictMono.of_zero : BoundedStrictMono (0 : ℕ) ρ := of_bot

namespace BoundedOn

def toFin {s t : ℕ} (ρ : ℕ → ℕ) [BoundedOn s t ρ] : Fin s → Fin t
  := λs => ⟨ρ s, bounded_on _ s.is_lt⟩

@[simp]
theorem toFin_id {s : ℕ} : toFin (s := s) (t := s) id = id := by funext; simp [toFin]

theorem toFin_comp (s t u : ℕ) (ρ σ : ℕ → ℕ) [hσ : BoundedOn s t σ] [hρ : BoundedOn t u ρ]
  : (BoundedOn.comp s t u).toFin (ρ ∘ σ) = toFin ρ ∘ hσ.toFin σ := rfl

def finPi {s t : ℕ} (ρ : ℕ → ℕ) [BoundedOn s t ρ] : Fin t → Finset (Fin s)
  := Finset.preimageF1 (toFin ρ)

@[simp]
theorem finPi_id {s : ℕ} : finPi (s := s) (t := s) id = ({·}) := by
  ext i j; simp [finPi, Finset.mem_preimageF1_iff]

theorem finPi_comp_apply (s t u : ℕ) (ρ σ : ℕ → ℕ) [hσ : BoundedOn s t σ] [hρ : BoundedOn t u ρ]
  (i) : (BoundedOn.comp s t u).finPi (ρ ∘ σ) i = Finset.sup (hρ.finPi _ i) hσ.finPi := by
  ext j; simp [finPi, Finset.mem_preimageF1_iff, toFin_comp s t u]

theorem eq_of_finPi {s t : ℕ} (ρ : ℕ → ℕ) [BoundedOn s t ρ] (i : Fin s) (j k : Fin t)
  : i ∈ finPi ρ j → i ∈ finPi ρ k → j = k := Finset.eq_of_preimageF1 (toFin ρ) i j k

theorem finPi_disjoint {s t : ℕ} (ρ : ℕ → ℕ) [hρ : BoundedOn s t ρ] (i j : Fin t) (hij : i ≠ j)
  : Disjoint (hρ.finPi ρ i) (hρ.finPi ρ j) := Finset.preimageF1_disjoint (toFin ρ) i j hij


def mulPi {s t : ℕ} (ρ : ℕ → ℕ) [BoundedOn s t ρ] (i : Fin t) : Multiset (Fin s)
  := (finPi ρ i).val

@[simp]
theorem mulPi_id {s : ℕ} : mulPi (s := s) id = pure := by ext j; simp [mulPi]

-- theorem mulPi_comp_apply_sup (s t u : ℕ) (ρ σ : ℕ → ℕ) [hσ : BoundedOn s t σ] [hρ : BoundedOn t u ρ]
--   (i) : (BoundedOn.comp s t u).mulPi (ρ ∘ σ) i = Finset.sup (hρ.finPi _ i) (λj => (finPi σ j).val)
--   := by
--   rw [mulPi, finPi_comp_apply s t u]
--   sorry

-- @[simp]
-- theorem mulPi_comp_apply (s t u : ℕ) (ρ σ : ℕ → ℕ) [hσ : BoundedOn s t σ] [hρ : BoundedOn t u ρ]
--   (i : Fin u) : (BoundedOn.comp s t u).mulPi (ρ ∘ σ) i = hρ.mulPi _ i >>= hσ.mulPi := by
--   ext j
--   sorry

def pv {s t : ℕ} (ρ : ℕ → ℕ) [BoundedOn s t ρ] (v : Vector' α t) : Vector' α s
  := Vector'.ofFn (v.get ∘ toFin ρ)

@[simp]
theorem pv_id {s : ℕ} (v : Vector' α s) : pv id v = v := by simp [pv]

theorem pv_comp {s t u : ℕ} (ρ σ : ℕ → ℕ) [hσ : BoundedOn s t σ] [hρ : BoundedOn t u ρ]
  (v : Vector' α u) : (BoundedOn.comp s t u).pv (ρ ∘ σ) v = hσ.pv σ (pv ρ v) := by
  simp [pv, toFin_comp (s := s) (t := t) (u := u), Function.comp_assoc]

def pvSum {s t : ℕ} (ρ : ℕ → ℕ) [BoundedOn s t ρ] [AddCommMonoid α] (v : Vector' α s) : Vector' α t
  := Vector'.ofFn (λi => ∑ j ∈ finPi ρ i, v.get j )

@[simp]
theorem pvSum_id {s : ℕ} [AddCommMonoid α] (v : Vector' α s) : pvSum id v = v := by
  simp [pvSum, finPi_id, Finset.sum_singleton]

-- @[simp]
-- theorem pvSum_comp (s t u : ℕ) (ρ σ : ℕ → ℕ) [hσ : BoundedOn s t σ] [hρ : BoundedOn t u ρ]
--   [AddCommMonoid α] (v : Vector' α s)
--   : (BoundedOn.comp s t u).pvSum (ρ ∘ σ) v = hρ.pvSum ρ (pvSum σ v) := by
--   simp [pvSum, finPi_comp (s := s) (t := t) (u := u), Function.comp_assoc]
--   sorry

-- TODO: pvSum comp ==> covariant functor

end BoundedOn
