/-
Copyright (c) 2024 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
import Mathlib.Tactic.CategoryTheory.Coherence.Basic
import Discretion.Tactic.CategoryTheory.Monoidal.Normalize
import Discretion.Tactic.CategoryTheory.Monoidal.PureCoherence

/-!
# `monoidal` tactic

This file provides `monoidal` tactic, which solves equations in a monoidal category, where
the two sides only differ by replacing strings of monoidal structural morphisms (that is,
associators, unitors, and identities) with different strings of structural morphisms with the same
source and target. In other words, `monoidal` solves equalities where both sides have the same
string diagrams.

The core function for the `monoidal` tactic is provided in
`Mathlib.Tactic.CategoryTheory.Coherence.Basic`. See this file for more details about the
implementation.

-/

open Lean Meta Elab Tactic
open CategoryTheory Mathlib.Tactic.BicategoryLike

namespace Discretion.Tactic.Monoidal

/-- Normalize the both sides of an equality. -/
def monoidalNf (mvarId : MVarId) : MetaM (List MVarId) := do
  Mathlib.Tactic.BicategoryLike.normalForm Monoidal.Context `premonoidal mvarId

@[inherit_doc monoidalNf]
elab "premonoidal_nf" : tactic => withMainContext do
  replaceMainGoal (← monoidalNf (← getMainGoal))

/--
Use the coherence theorem for monoidal categories to solve equations in a monoidal category,
where the two sides only differ by replacing strings of monoidal structural morphisms
(that is, associators, unitors, and identities)
with different strings of structural morphisms with the same source and target.

That is, `monoidal` can handle goals of the form
`a ≫ f ≫ b ≫ g ≫ c = a' ≫ f ≫ b' ≫ g ≫ c'`
where `a = a'`, `b = b'`, and `c = c'` can be proved using `monoidal_coherence`.
-/
def monoidal (mvarId : MVarId) : MetaM (List MVarId) :=
  Mathlib.Tactic.BicategoryLike.main Monoidal.Context `premonoidal mvarId

@[inherit_doc monoidal]
elab "premonoidal" : tactic => withMainContext do
  replaceMainGoal <| ← monoidal <| ← getMainGoal

end Discretion.Tactic.Monoidal
