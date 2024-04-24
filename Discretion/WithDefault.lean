/- Placeholder until [`#9181`](https://github.com/leanprover-community/mathlib4/pull/9181) -/
/- Mostly copy-pased from https://github.com/leanprover-community/mathlib4/blob/64630834f1984a7b498ade5d5c895c4a335a093c/Mathlib/Order/WithBot.lean-/
import Init
import Mathlib.Order.BoundedOrder
import Mathlib.Tactic.Lift
import Mathlib.Data.Option.Basic
import Mathlib.Data.Option.NAry
import Mathlib.Init.Algebra.Classes
import Mathlib.Logic.Nontrivial.Basic

/-- Attach `default` to a type. -/
def WithDefault (α) := Option α

namespace WithDefault

variable {a b : α}

instance [Repr α] : Repr (WithDefault α) :=
  ⟨fun o _ =>
    match o with
    | none => "default"
    | some a => "↑" ++ repr a⟩

/-- The canonical map from `α` into `WithDefault α` -/
@[coe, match_pattern] def some : α → WithDefault α :=
  Option.some

instance coe : Coe α (WithDefault α) :=
  ⟨some⟩

instance inhabited : Inhabited (WithDefault α) :=
  ⟨none⟩

-- TODO: change things to use .default?

open Function

open Inhabited

theorem coe_injective : Injective ((↑) : α → WithDefault α) :=
  Option.some_injective _

@[simp, norm_cast]
theorem coe_inj : (a : WithDefault α) = b ↔ a = b :=
  Option.some_inj

protected theorem «forall» {p : WithDefault α → Prop} : (∀ x, p x) ↔ p default ∧ ∀ x : α, p x :=
  Option.forall

protected theorem «exists» {p : WithDefault α → Prop} : (∃ x, p x) ↔ p default ∨ ∃ x : α, p x :=
  Option.exists

theorem none_eq_default : (none : WithDefault α) = (default : WithDefault α) :=
  rfl

theorem some_eq_coe (a : α) : (Option.some a : WithDefault α) = (↑a : WithDefault α) :=
  rfl

@[simp]
theorem bot_ne_coe : default ≠ (a : WithDefault α) :=
  nofun

@[simp]
theorem coe_ne_bot : (a : WithDefault α) ≠ default :=
  nofun


-- TODO: `recDefaultCoe`

/-- Specialization of `Option.getD` to values in `WithDefault α` that respects API boundaries.
-/
def unbot' (d : α) : WithDefault α → α
  | none => d
  | some a => a

-- ...
