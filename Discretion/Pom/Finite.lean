import Mathlib.Data.Fin.Basic
import Mathlib.Order.Fin.Basic
import Mathlib.Data.Rel

import Discretion.Utils.Rel
import Discretion.Utils.Fin

structure Potuple (α : Type u) where
  arity : ℕ
  actions : Fin arity → α
  order : PartialOrder (Fin arity)

instance : EmptyCollection (Potuple α) := ⟨⟨0, λ i => Fin.elim0 i, inferInstance⟩⟩

instance : Inhabited (Potuple α) := ⟨∅⟩

instance [IsEmpty α] : Subsingleton (Potuple α) where allEq
  | ⟨n, an, _⟩, ⟨m, am, _⟩ => by cases n with
    | zero => cases m with
      | zero => congr <;> ext i <;> exact i.elim0
      | succ => exact isEmptyElim (am 0)
    | succ => exact isEmptyElim (an 0)

instance : Singleton α (Potuple α) where
  singleton a := ⟨1, Fin.elim1 a, inferInstance⟩

instance [Nonempty α] : Nontrivial (Potuple α) where
  exists_pair_ne := ⟨
    ∅, {Classical.ofNonempty},
    by simp [EmptyCollection.emptyCollection, Singleton.singleton]
  ⟩

def Potuple.map {α β : Type u} (f : α → β) (p : Potuple α) : Potuple β :=
  ⟨p.arity, λ i => f (p.actions i), p.order⟩

def Potuple.ofOpt {α : Type u} : Option α → Potuple α
  | none => ∅
  | some a => {a}

-- instance : Insert α (Potuple α) where
--   insert a p := ⟨p.arity + 1, sorry, sorry⟩

-- TODO: linearly ordered potuple...

-- TODO: Potuple is actually a monad, in a weird, weird way...

structure Potuple.RHom {α β : Type u} (r : Rel α β) (p : Potuple α) (q : Potuple β) : Type u
  where
  toFun : Fin p.arity → Fin q.arity
  actions : ∀ i, r (p.actions i) (q.actions (toFun i))
  order : ∀i j, p.order.le i j -> q.order.le (toFun i) (toFun j)

def Potuple.RHom.comp {α β γ : Type u}
  {r : Rel α β} {s : Rel β γ} {p : Potuple α} {q : Potuple β} {t : Potuple γ}
  (f : Potuple.RHom r p q) (g : Potuple.RHom s q t) : Potuple.RHom (r.comp s) p t
  where
  toFun := g.toFun ∘ f.toFun
  actions i := ⟨q.actions (f.toFun i), f.actions i, g.actions (f.toFun i)⟩
  order _ _ h := g.order _ _ (f.order _ _ h)

structure Potuple.RIso {α β : Type u} (r : Rel α β) (p : Potuple α) (q : Potuple β)
  extends Equiv (Fin p.arity) (Fin q.arity) : Type u
  where
  actions : ∀ i, r (p.actions i) (q.actions (toFun i))
  order : ∀i j, p.order.le i j ↔ q.order.le (toFun i) (toFun j)

def Potuple.RIso.inv {α β : Type u} {r : Rel α β} {p : Potuple α} {q : Potuple β}
  (f : Potuple.RIso r p q) : Potuple.RIso r.inv q p
  where
  toFun := f.invFun
  invFun := f.toFun
  left_inv := f.right_inv
  right_inv := f.left_inv
  actions i := by convert f.actions (f.invFun i); simp [Rel.inv, flip]
  order i j := by convert f.order (f.invFun i) (f.invFun j) using 0; simp [Iff.comm]

def Potuple.RIso.comp {α β γ : Type u}
  {r : Rel α β} {s : Rel β γ} {p : Potuple α} {q : Potuple β} {t : Potuple γ}
  (f : Potuple.RIso r p q) (g : Potuple.RIso s q t) : Potuple.RIso (r.comp s) p t
  where
  toEquiv := f.toEquiv.trans g.toEquiv
  actions i := ⟨q.actions (f.toFun i), f.actions i, g.actions (f.toFun i)⟩
  order i j := Iff.trans (f.order i j) (g.order _ _)

def Potuple.RIso.refl {α : Type u} (p : Potuple α) : Potuple.RIso Eq p p
  where
  toEquiv := Equiv.refl _
  actions := λ_ => rfl
  order := λ_ _ => Iff.rfl

def Potuple.Iso {α : Type u} := Potuple.RIso (Eq (α := α))

def Potuple.Iso.refl {α : Type u} (p : Potuple α) : Potuple.Iso p p := Potuple.RIso.refl p

def Potuple.Iso.symm {α : Type u} {p q : Potuple α} (f : Potuple.Iso p q) : Potuple.Iso q p where
  toEquiv := f.toEquiv.symm
  actions i := by convert f.actions (f.invFun i) using 0; simp [Eq.comm]
  order i j := by convert f.order (f.invFun i) (f.invFun j) using 0; simp [Iff.comm]

def Potuple.Iso.trans {α : Type u} {p q r : Potuple α} (f : Potuple.Iso p q) (g : Potuple.Iso q r)
  : Potuple.Iso p r where
  toEquiv := f.toEquiv.trans g.toEquiv
  actions i := (f.actions i).trans (g.actions (f.toFun i))
  order i j := Iff.trans (f.order i j) (g.order _ _)

def Potuple.Eqv {α : Type u} (p q : Potuple α) := Nonempty (Potuple.Iso p q)

theorem Potuple.Eqv.refl {α : Type u} (p : Potuple α) : Potuple.Eqv p p :=
  ⟨Potuple.Iso.refl p⟩

theorem Potuple.Eqv.symm {α : Type u} {p q : Potuple α}
  : Potuple.Eqv p q → Potuple.Eqv q p | ⟨f⟩ => ⟨f.symm⟩

theorem Potuple.Eqv.trans {α : Type u} {p q r : Potuple α}
  : Potuple.Eqv p q → Potuple.Eqv q r → Potuple.Eqv p r | ⟨f⟩, ⟨g⟩ => ⟨f.trans g⟩

instance Potuple.EqvSetoid (α : Type u) : Setoid (Potuple α) where
  r := Potuple.Eqv
  iseqv := {
    refl := Potuple.Eqv.refl,
    symm := Potuple.Eqv.symm,
    trans := Potuple.Eqv.trans
  }

structure Potuple.RMatchExcept
  {α β : Type u}
  (r : Rel α β) (eα : Set α) (eβ : Set β) (p : Potuple α) (q : Potuple β) : Type u
  where
  toRel : Rel (Fin p.arity) (Fin q.arity)
  actions : ∀ i j, toRel i j -> r (p.actions i) (q.actions j)
  order : ∀i j i' j', toRel i j -> toRel i' j' -> (p.order.le i i' ↔ q.order.le j j')
  bij : ∀i j i' j', toRel i j -> toRel i' j' -> (i = i' ↔ j = j')
  left_skip : ∀i, (∃j, toRel i j) ∨ p.actions i ∈ eα
  right_skip : ∀j, (∃i, toRel i j) ∨ q.actions j ∈ eβ

def Potuple.Match1 {α : Type u} [One α] := Potuple.RMatchExcept (Eq (α := α)) {1} {1}

def Potuple.Match1.refl {α : Type u} [One α] (p : Potuple α) : Potuple.Match1 p p
  where
  toRel := Eq
  actions i j h := by cases h; rfl
  order i j i' j' h h' := by cases h; cases h'; rfl
  bij i j i' j' h h' := by cases h; cases h'; rfl
  left_skip i := Or.inl ⟨i, rfl⟩
  right_skip j := Or.inl ⟨j, rfl⟩

def Potuple.Match1.symm {α : Type u} [One α] {p q : Potuple α}
  (f : Potuple.Match1 p q) : Potuple.Match1 q p
  where
  toRel i j := f.toRel j i
  actions i j h := (f.actions j i h).symm
  order i j i' j' h h' := Iff.symm (f.order j i j' i' h h')
  bij i j i' j' h h' := (f.bij j i j' i' h h').symm
  left_skip i := f.right_skip i
  right_skip j := f.left_skip j

def Potuple.Match1.trans {α : Type u} [One α] {p q r : Potuple α}
  (f : Potuple.Match1 p q) (g : Potuple.Match1 q r) : Potuple.Match1 p r
  where
  toRel := f.toRel.comp g.toRel
  actions i k | ⟨j, hij, hjk⟩ => (f.actions i j hij).trans (g.actions j k hjk)
  order i k i' k' | ⟨j, hij, hjk⟩, ⟨j', hij', hjk'⟩ =>
                    (f.order i j i' j' hij hij').trans (g.order j k j' k' hjk hjk')
  bij i k i' k' | ⟨j, hij, hjk⟩, ⟨j', hij', hjk'⟩ =>
                  (f.bij i j i' j' hij hij').trans (g.bij j k j' k' hjk hjk')
  left_skip i := match f.left_skip i with
    | Or.inl ⟨j, h⟩ => match g.left_skip j with
      | Or.inl ⟨k, h'⟩ => Or.inl ⟨k, ⟨j, h, h'⟩⟩
      | Or.inr h' => Or.inr (by convert h' using 1; exact f.actions _ _ h)
    | Or.inr h => Or.inr h
  right_skip k := match g.right_skip k with
    | Or.inl ⟨j, h⟩ => match f.right_skip j with
      | Or.inl ⟨i, h'⟩ => Or.inl ⟨i, ⟨j, h', h⟩⟩
      | Or.inr h' => Or.inr (by convert h' using 1; exact (g.actions _ _ h).symm)
    | Or.inr h => Or.inr h

def Potuple.Bisim {α : Type u} [One α] (p q : Potuple α) := Nonempty (Potuple.Match1 p q)

theorem Potuple.Bisim.refl {α : Type u} [One α] (p : Potuple α) : Potuple.Bisim p p :=
  ⟨Potuple.Match1.refl p⟩

theorem Potuple.Bisim.symm {α : Type u} [One α] {p q : Potuple α}
  : Potuple.Bisim p q → Potuple.Bisim q p | ⟨f⟩ => ⟨f.symm⟩

theorem Potuple.Bisim.trans {α : Type u} [One α] {p q r : Potuple α}
  : Potuple.Bisim p q → Potuple.Bisim q r → Potuple.Bisim p r | ⟨f⟩, ⟨g⟩ => ⟨f.trans g⟩

def Potuple.BisimSetoid (α : Type u) [One α] : Setoid (Potuple α) where
  r := Potuple.Bisim
  iseqv := {
    refl := Potuple.Bisim.refl,
    symm := Potuple.Bisim.symm,
    trans := Potuple.Bisim.trans
  }

theorem Potuple.arity_eq_zero_singleton {p : Potuple α} : p.arity = 0 ↔ p = ∅ :=
  ⟨λh => by
    cases p; cases h; simp only [EmptyCollection.emptyCollection]
    congr <;> ext i <;> exact i.elim0,
    λh => h ▸ rfl
  ⟩

-- theorem Potuple.Eqv.arity_eq {p q : Potuple α} : p ≈ q → p.arity = q.arity :=
--   sorry

-- theorem Potuple.Eqv.singleton {p : Potuple α} : p ≈ ∅ -> p = ∅ :=
--   sorry

def FPom (α : Type u) := Quotient (Potuple.EqvSetoid α)

def FPom1 (α : Type u) [One α] := Quotient (Potuple.BisimSetoid α)

-- TODO: Wts FPom α has a monoid isomorphism with FPom1 (WithOne α)
