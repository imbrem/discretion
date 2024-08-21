import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Action.Defs

section Multiplicative

open SMul

theorem smul_one (M α) [Monoid M] [MulAction M α] : smul (M := M) (α := α) 1 = id
  := by funext x; exact one_smul _ _

variable {M} (α) [Monoid M] [MulAction M α]

theorem smul_mul (x y : M) : smul (x * y) = smul x ∘ smul (α := α) y
  := by funext a; exact mul_smul x y a

end Multiplicative

-- TODO: Additive?
