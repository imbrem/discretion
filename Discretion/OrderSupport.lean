import Mathlib.Data.Set.Basic

/-- `infSupport` of a function is the set of points `x` such that `f x ≠ ⊤` -/
def Function.infSupport {α M} [Top M] (f : α → M) : Set α := {a | f a ≠ ⊤}

/-- `supSupport` of a function is the set of points `x` such that `f x ≠ ⊥` -/
def Function.supSupport {α M} [Bot M] (f : α → M) : Set α := {a | f a ≠ ⊥}

/-- `defaultSupport` of a function is the set of points `x` such that `f x ≠ default` -/
def Function.defaultSupport {α M} [Inhabited M] (f : α → M) : Set α := {a | f a ≠ default}
