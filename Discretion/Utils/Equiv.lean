import Mathlib.Data.Set.Function
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset

import Discretion.Utils.Multiset

open Classical

instance topIsEquiv {α} : IsEquiv α ⊤ where
  refl _ := trivial
  symm _ _ _ := trivial
  trans _ _ _ _ _ := trivial

-- TODO: IsEquiv for sup, inf, sSup, sInf?

theorem Relation.EqvGen.monotone {α} : Monotone (EqvGen (α := α))
  := λ_ _ hr _ _ h => EqvGen.mono hr h

theorem Relation.EqvGen.increasing {r : α → α → Prop} : r ≤ EqvGen r := EqvGen.rel

instance Relation.eqvGen_isEquiv {r : α → α → Prop} : IsEquiv α (EqvGen r) where
  refl := EqvGen.refl
  symm := EqvGen.symm
  trans := EqvGen.trans

theorem Relation.equivalence_isEquiv (r : α → α → Prop) [IsEquiv α r] : Equivalence r where
  refl := IsRefl.refl
  symm := IsSymm.symm _ _
  trans := IsTrans.trans _ _ _

theorem Relation.eqvGen_of_isEquiv {r : α → α → Prop} [IsEquiv α r]
  : EqvGen r = r := (equivalence_isEquiv r).eqvGen_eq

theorem Relation.eqvGen_le_of_le_isEquiv {r s : α → α → Prop} [IsEquiv α s]
  (hr : r ≤ s) : EqvGen r ≤ s
  := eqvGen_of_isEquiv (r := s) ▸ EqvGen.monotone hr

def Relation.StepGen (β : Sort u) (r : α → α → Prop) (f : β → α) (g : β → α) : Prop
  := ∃b: β, r (f b) (g b) ∧ g = Function.update f b (g b)

theorem Relation.StepGen.monotone {α} (β : Type u) : Monotone (Relation.StepGen (α := α) β)
  := λ_ _ hrs _ _ ⟨b, hb, hg⟩ => ⟨b, hrs _ _ hb, hg⟩

theorem Relation.StepGen.mono {α} {r p : α → α → Prop} (β : Type u) {f g : β → α}
  (hrp : ∀a b : α, r a b → p a b)
  : Relation.StepGen β r f g → Relation.StepGen β p f g
  := λ⟨b, hb, hg⟩ => ⟨b, hrp _ _ hb, hg⟩

def Relation.Elementwise (β : Sort u) (r : α → α → Prop) (f : β → α) (g : β → α) : Prop
  := ∀b: β, r (f b) (g b)

theorem Relation.Elementwise.monotone {α} (β : Type u) : Monotone (Relation.Elementwise (α := α) β)
  := λ_ _ hrs _ _ hfg b => hrs _ _ (hfg b)

theorem Region.Elementwise.mono {α} {r p : α → α → Prop} (β : Type u) {f g : β → α}
  (hrp : ∀a b : α, r a b → p a b)
  : Relation.Elementwise β r f g → Relation.Elementwise β p f g
  := λhfg b => hrp _ _ (hfg b)

instance elementwise_isSymm {β} {r : α → α → Prop} [IsSymm α r]
    : IsSymm (β → α) (Relation.Elementwise β r) where
  symm _ _ h x := IsSymm.symm _ _ (h x)

instance elementwise_isTrans {β} {r : α → α → Prop} [IsTrans α r]
    : IsTrans (β → α) (Relation.Elementwise β r) where
  trans _ _ _ h h' x := IsTrans.trans _ _ _ (h x) (h' x)

instance elementwise_isRefl {β} {r : α → α → Prop} [IsRefl α r]
    : IsRefl (β → α) (Relation.Elementwise β r) where
  refl f x := IsRefl.refl (f x)

instance elementwise_isEquiv {β} {r : α → α → Prop} [IsEquiv α r]
  : IsEquiv (β → α) (Relation.Elementwise β r) where

instance elementwise_isAntisymm {β} {r : α → α → Prop} [IsAntisymm α r]
    : IsAntisymm (β → α) (Relation.Elementwise β r) where
  antisymm _ _ h h' := funext λx => IsAntisymm.antisymm _ _ (h x) (h' x)

instance elementwise_isIrrefl {β} [b : Nonempty β] {r : α → α → Prop} [IsIrrefl α r]
    : IsIrrefl (β → α) (Relation.Elementwise β r) where
  irrefl _ h := b.elim (λb => IsIrrefl.irrefl _ (h b))

theorem Relation.EqvGen.elementwise
  {β : Type u} {r : α → α → Prop} {f g: β → α} (h : EqvGen (Relation.Elementwise β r) f g)
  : Relation.Elementwise β (EqvGen r) f g
  := by induction h with
  | rel _ _ h => exact λx => EqvGen.rel _ _ (h x)
  | refl f => exact λx => EqvGen.refl (f x)
  | symm f g _ I => exact λx => EqvGen.symm _ _ (I x)
  | trans f g h _ _ Il Ir => exact λx => EqvGen.trans _ _ _ (Il x) (Ir x)

theorem Relation.EqvGen.le_elementwise
  {β : Type u} {r : α → α → Prop}
  : EqvGen (Relation.Elementwise β r) ≤ Relation.Elementwise β (EqvGen r)
  := λ_ _ => EqvGen.elementwise

-- TODO: weird choice based nonsense for the other way around...

theorem Relation.StepGen.elementwise_eqvGen
  {β : Type u} {r : α → α → Prop} {f g : β → α}
  : Relation.StepGen β r f g → Relation.Elementwise β (EqvGen r) f g
  | ⟨b, hb, hg⟩, a => if ha : a = b then ha ▸ EqvGen.rel _ _ hb else by
    rw [hg, Function.update_of_ne ha]
    apply EqvGen.refl

theorem Relation.StepGen.le_elementwise_eqvGen
  {β : Type u} {r : α → α → Prop}
  : Relation.StepGen β r ≤ Relation.Elementwise β (EqvGen r)
  := λ_ _ h => Relation.StepGen.elementwise_eqvGen h

theorem Relation.StepGen.elementwise
  {β : Type u} {r : α → α → Prop} {f g : β → α} [IsRefl α r]
  : Relation.StepGen β r f g → Relation.Elementwise β r f g
  | ⟨b, hb, hg⟩, a => if ha : a = b then ha ▸ hb else by
    rw [hg, Function.update_of_ne ha]
    apply IsRefl.refl

theorem Relation.StepGen.le_elementwise {β : Type u} {r : α → α → Prop} [IsRefl α r]
  : StepGen β r ≤ Elementwise β (EqvGen r)
  := λ_ _ h => Relation.StepGen.elementwise_eqvGen h

theorem Relation.StepGen.eqvGen_le_elementwise_eqvGen {β : Type u} {r : α → α → Prop}
  : EqvGen (StepGen β r) ≤ Elementwise β (EqvGen r)
  := eqvGen_le_of_le_isEquiv le_elementwise_eqvGen

theorem Relation.StepGen.eqvGen_le_eqvGen {β : Type u} {r : α → α → Prop}
  : StepGen β (EqvGen r) ≤ EqvGen (StepGen β r)
  | f, g, ⟨b, hb, hg⟩ => by
    generalize hfb : (f b) = fb
    generalize hgb : (g b) = gb
    rw [hfb, hgb] at hb
    induction hb generalizing f g with
    | rel _ _ h => exact EqvGen.rel _ _ ⟨b, hfb ▸ hgb ▸ h, hg⟩
    | refl _ =>
      cases hfb
      rw [hgb, Function.update_eq_self] at hg
      rw [hg]
      apply EqvGen.refl
    | symm _ _ _ I =>
      apply EqvGen.symm
      apply I
      rw [hg, Function.update_idem, Function.update_eq_self]
      exact hgb
      exact hfb
    | trans x y z _ _ Il Ir =>
      apply EqvGen.trans
      apply Il _ (Function.update f b y)
      rw [Function.update_self]
      exact hfb
      rw [Function.update_self]
      apply Ir
      rw [hg, Function.update_idem, Function.update_self]
      rw [Function.update_self]
      exact hgb

theorem Relation.Elementwise.multiset_diff
  {β : Type u} {r : α → α → Prop} {f g : β → α}
  (hr : Elementwise β (EqvGen r) f g) (S : Multiset β) (hs : ∀b : β, f b ≠ g b → b ∈ S)
  : EqvGen (StepGen β r) f g := by induction S using Multiset.induction generalizing f g with
  | empty =>
    have h : f = g := funext (λb => Classical.not_not.mp (λh => by cases hs _ h))
    cases h
    apply EqvGen.refl
  | @cons b S I =>
    apply EqvGen.trans
    apply StepGen.eqvGen_le_eqvGen
    have h : g b = Function.update f b (g b) b := by simp
    exact ⟨b, h ▸ hr b, by simp⟩
    apply I
    intro x
    if hb : x = b then
      cases hb
      rw [Function.update_self]
      apply EqvGen.refl
    else
      rw [Function.update_of_ne hb]
      exact hr x
    intro x hx
    have hb : x ≠ b := λhb => by cases hb; simp at hx
    apply Multiset.mem_of_mem_cons_of_ne
    apply hs
    simp only [ne_eq, hb, not_false_eq_true, Function.update_of_ne] at hx
    exact hx
    exact hb

theorem Relation.Elementwise.finset_diff
  {β : Type u} {r : α → α → Prop} {f g : β → α}
  (hr : Elementwise β (EqvGen r) f g) (S : Finset β) (hs : ∀b : β, f b ≠ g b → b ∈ S)
  : EqvGen (StepGen β r) f g := multiset_diff hr S.val hs

theorem Relation.StepGen.elementwise_eqvGen_le_eqvGen_fintype
  {β : Type u} [Fintype β] {r : α → α → Prop}
  : Elementwise β (EqvGen r) ≤ EqvGen (StepGen β r)
  := λ_ _ hr => hr.finset_diff Fintype.elems (λ_ _ => Fintype.complete _)

theorem Relation.StepGen.eqvGen_fintype {β : Type u} [Fintype β] {r : α → α → Prop}
  : EqvGen (StepGen β r) = Elementwise β (EqvGen r)
  := le_antisymm eqvGen_le_elementwise_eqvGen elementwise_eqvGen_le_eqvGen_fintype
