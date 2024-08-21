import Mathlib.Data.Set.Defs
import Mathlib.Order.Basic
import Mathlib.Order.BoundedOrder
import Mathlib.Data.Set.Operations

import Discretion.Utils.Kleisli

section Monad

open Set

variable {m : Type u → Type v}

class IsSubmonad (m : Type u → Type v) [Monad m]  (s : ∀α, Set (m α)) : Prop where
  pure_mem: ∀{α} (a: α), pure a ∈ s α
  bind_mem: ∀{α β} {x: m α} {f: α → m β}, x ∈ s α → (∀a, f a ∈ s β) → x >>= f ∈ s β

structure Submonad (m : Type u → Type v) [Monad m] where
  carrier : ∀α, Set (m α)
  is_submonad : IsSubmonad m carrier

namespace IsSubmonad

variable {s : ∀α, Set (m α)}

theorem elim_mem {α β γ} {f: α → m γ} {g : β → m γ}
  (hf : ∀a, f a ∈ s γ) (hg : ∀b, g b ∈ s γ) : ∀i : α ⊕ β, Sum.elim f g i ∈ s γ
  := λ| Sum.inl a => hf a | Sum.inr b => hg b

theorem elim_mem_iff {α β γ} {f: α → m γ} {g : β → m γ}
  : (∀i : α ⊕ β, Sum.elim f g i ∈ s γ) ↔ (∀a, f a ∈ s γ) ∧ (∀b, g b ∈ s γ)
  := ⟨λh => ⟨λa => h (Sum.inl a), λb => h (Sum.inr b)⟩, λ⟨hf, hg⟩ => elim_mem hf hg⟩

variable [Monad m] [IsSubmonad m s]

instance univ : IsSubmonad m (λα => univ) where
  pure_mem _ := by trivial
  bind_mem _ _ := by trivial

theorem kleisli_mem {α β γ} {f: α → m β} {g : β → m γ}
  (hf : ∀a, f a ∈ s β) (hg : ∀b, g b ∈ s γ) : ∀a, (f >=> g) a ∈ s γ := λa => bind_mem (hf a) hg

variable [LawfulMonad m]

theorem map_mem {α β} {f: α → β} {x: m α} (hx : x ∈ s α) : f <$> x ∈ s β
  := by convert (bind_mem hx (λa => pure_mem (f a))); rw [map_eq_pure_bind]

theorem sumM_mem {α β α' β'} {f: α → m α'} {g : β → m β'}
  (hf : ∀a, f a ∈ s α') (hg : ∀b, g b ∈ s β') : ∀i, sumM f g i ∈ s (α' ⊕ β')
  := elim_mem (λa => map_mem (hf a)) (λb => map_mem (hg b))

instance pure : IsSubmonad m (λ_ => range pure) where
  pure_mem _ := by simp
  bind_mem | ⟨x, hx⟩, ha => by cases hx; simp [ha]

-- TODO: intersection lore, etc

-- TODO: nomempty sets are a submonad

end IsSubmonad

namespace Submonad

-- TODO: complete lattice structure, etc...

end Submonad

end Monad
