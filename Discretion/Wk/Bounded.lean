import Mathlib.Order.Monotone.Basic
import Mathlib.Order.BoundedOrder.Basic
import Mathlib.Order.Nat

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
