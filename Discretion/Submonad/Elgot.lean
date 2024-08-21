import Discretion.Submonad.Basic
import Discretion.Elgot.Monad

open MonadIterate

class IsElgotSubmonad (m : Type u → Type v) [Monad m] [MonadIterate m] (s : ∀α, Set (m α))
  extends IsSubmonad m s : Prop where
  iterate_mem : ∀{α β} {f: α → m (β ⊕ α)}, (∀a, f a ∈ s (β ⊕ α)) → ∀x, iterate f x ∈ s β
