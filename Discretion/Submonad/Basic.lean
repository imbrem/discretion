import Mathlib.Data.Set.Defs
import Mathlib.Order.Basic
import Mathlib.Order.BoundedOrder
import Mathlib.Data.Set.Operations

section Monad

open Set

variable {m : Type u → Type v}

class IsSubmonad (m : Type u → Type v) [Monad m]  (s : ∀α, Set (m α)) : Prop where
  pure_mem: ∀{α} (a: α), pure a ∈ s α
  bind_mem: ∀{α β} {x: m α} {f: α → m β}, x ∈ s α → (∀a, f a ∈ s β) → x >>= f ∈ s β

structure Submonad (m : Type u → Type v) [Monad m] where
  carrier : ∀α, Set (m α)
  is_submonad : IsSubmonad m s

namespace IsSubmonad

variable [Monad m] {s : ∀α, Set (m α)} [IsSubmonad m s]

instance univ : IsSubmonad m (λα => univ) where
  pure_mem _ := by trivial
  bind_mem _ _ := by trivial

variable [LawfulMonad m]

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
