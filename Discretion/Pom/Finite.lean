import Mathlib.Data.Fin.Basic
import Mathlib.Order.Fin.Basic
import Mathlib.Data.Rel

import Discretion.Utils.Rel
import Discretion.Utils.Fin

import Discretion.Pom.OrderOps

namespace Fin

structure GPom (α : Type u) where
  arity : ℕ
  actions : Fin arity → α
  order : PartialOrder (Fin arity)

namespace GPom

instance : EmptyCollection (GPom α) := ⟨⟨0, λ i => Fin.elim0 i, inferInstance⟩⟩

@[simp]
theorem arity_empty {α} : (∅ : GPom α).arity = 0 := rfl

theorem order_empty {α} : (∅ : GPom α).order = ⊥ := PartialOrder.ext (λa => a.elim0)

instance : Inhabited (GPom α) := ⟨∅⟩

instance [IsEmpty α] : Subsingleton (GPom α) where allEq
  | ⟨n, an, _⟩, ⟨m, am, _⟩ => by cases n with
    | zero => cases m with
      | zero => congr <;> ext i <;> exact i.elim0
      | succ => exact isEmptyElim (am 0)
    | succ => exact isEmptyElim (an 0)

instance : Singleton α (GPom α) where
  singleton a := ⟨1, Fin.elim1 a, inferInstance⟩

@[simp]
theorem arity_singleton {α} {a : α} : ({a} : GPom α).arity = 1 := rfl

instance [Nonempty α] : Nontrivial (GPom α) where
  exists_pair_ne := ⟨
    ∅, {Classical.ofNonempty},
    by simp [EmptyCollection.emptyCollection, Singleton.singleton]
  ⟩

def map {α : Type u} {β : Type v} (f : α → β) (p : GPom α) : GPom β :=
  ⟨p.arity, λ i => f (p.actions i), p.order⟩

theorem arity_eq_zero {p : GPom α} : p.arity = 0 ↔ p = ∅ :=
  ⟨λh => by
    cases p; cases h; simp only [EmptyCollection.emptyCollection]
    congr <;> ext i <;> exact i.elim0,
    λh => h ▸ rfl
  ⟩

@[simp]
theorem map_arity {f : α → β} {p : GPom α} : (p.map f).arity = p.arity := rfl

@[simp]
theorem map_empty {f : α → β} : map f ∅ = ∅ := arity_eq_zero.mp rfl

@[simp]
theorem map_singleton {f : α → β} {a : α} : map f {a} = {f a} := by
  simp only [map, singleton, Fin.elim1_const, mk.injEq, heq_eq_eq, and_true, true_and]
  funext i; cases i using Fin.elim1; rfl

@[simp]
def ofOpt {α : Type u} : Option α → GPom α
  | none => ∅
  | some a => {a}

@[simp]
theorem map_ofOpt {f : α → β} {a : Option α} : map f (ofOpt a) = ofOpt (a.map f)
  := by cases a <;> simp

def seq {α : Type u} (p q : GPom α) : GPom α where
  arity := p.arity + q.arity
  actions i := i.addCases p.actions q.actions
  order := poseq p.order q.order

theorem seq_empty (p : GPom α) : p.seq ∅ = p := by simp [seq, poseq_zero, addCases, castLT]

theorem empty_seq (p : GPom α) : seq ∅ p = p
  := by cases p; simp [seq, zero_poseq, addCases, Fin.heq_fun_iff, Fin.cast]

theorem seq_assoc (p q r : GPom α) : seq (seq p q) r = seq p (seq q r)
  := by
  cases p; cases q; cases r
  simp only [seq, poseq_assoc, mk.injEq, Nat.add_assoc, Fin.heq_fun_iff, heq_pocast, and_true,
    true_and]
  intro i
  apply Eq.symm
  exact addCases_cast_assoc i

instance instMonoid : Monoid (GPom α) where
  mul := seq
  mul_assoc := seq_assoc
  one := ∅
  one_mul := empty_seq
  mul_one := seq_empty

def par {α : Type u} (p q : GPom α) : GPom α where
  arity := p.arity + q.arity
  actions i := i.addCases p.actions q.actions
  order := popar p.order q.order

theorem par_empty (p : GPom α) : p.par ∅ = p := by simp [par, popar_zero, addCases, castLT]

theorem empty_par (p : GPom α) : par ∅ p = p
  := by cases p; simp [par, zero_popar, addCases, Fin.heq_fun_iff, Fin.cast]

theorem par_assoc (p q r : GPom α) : par (par p q) r = par p (par q r)
  := by
  cases p; cases q; cases r
  simp only [par, popar_assoc, mk.injEq, Nat.add_assoc, Fin.heq_fun_iff, heq_pocast, and_true,
    true_and]
  intro i
  apply Eq.symm
  exact addCases_cast_assoc i

instance instZero : Zero (GPom α) where
  zero := ∅

instance instAdd : Add (GPom α) where
  add := par

instance instAddMonoid : AddMonoid (GPom α) where
  add_assoc := par_assoc
  zero_add := empty_par
  add_zero := par_empty
  nsmul := nsmulRec

-- instance : Insert α (GPom α) where
--   insert a p := ⟨p.arity + 1, sorry, sorry⟩

-- TODO: linearly ordered potuple...

-- TODO: GPom is actually a monad, in a weird, weird way...

structure RHom {α β : Type u} (r : Rel α β) (p : GPom α) (q : GPom β) : Type u
  where
  toFun : Fin p.arity → Fin q.arity
  actions : ∀ i, r (p.actions i) (q.actions (toFun i))
  order : ∀i j, p.order.le i j -> q.order.le (toFun i) (toFun j)

def RHom.comp {α β γ : Type u}
  {r : Rel α β} {s : Rel β γ} {p : GPom α} {q : GPom β} {t : GPom γ}
  (f : RHom r p q) (g : RHom s q t) : RHom (r.comp s) p t
  where
  toFun := g.toFun ∘ f.toFun
  actions i := ⟨q.actions (f.toFun i), f.actions i, g.actions (f.toFun i)⟩
  order _ _ h := g.order _ _ (f.order _ _ h)

structure RIso {α β : Type u} (r : Rel α β) (p : GPom α) (q : GPom β)
  extends Equiv (Fin p.arity) (Fin q.arity) : Type u
  where
  actions : ∀ i, r (p.actions i) (q.actions (toFun i))
  order : ∀i j, p.order.le i j ↔ q.order.le (toFun i) (toFun j)

def RIso.inv {α β : Type u} {r : Rel α β} {p : GPom α} {q : GPom β}
  (f : RIso r p q) : RIso r.inv q p
  where
  toFun := f.invFun
  invFun := f.toFun
  left_inv := f.right_inv
  right_inv := f.left_inv
  actions i := by convert f.actions (f.invFun i); simp [Rel.inv, flip]
  order i j := by convert f.order (f.invFun i) (f.invFun j) using 0; simp [Iff.comm]

def RIso.comp {α β γ : Type u}
  {r : Rel α β} {s : Rel β γ} {p : GPom α} {q : GPom β} {t : GPom γ}
  (f : RIso r p q) (g : RIso s q t) : RIso (r.comp s) p t
  where
  toEquiv := f.toEquiv.trans g.toEquiv
  actions i := ⟨q.actions (f.toFun i), f.actions i, g.actions (f.toFun i)⟩
  order i j := Iff.trans (f.order i j) (g.order _ _)

def RIso.refl {α : Type u} (p : GPom α) : RIso Eq p p
  where
  toEquiv := Equiv.refl _
  actions := λ_ => rfl
  order := λ_ _ => Iff.rfl

def Iso {α : Type u} := RIso (Eq (α := α))

def Iso.refl {α : Type u} (p : GPom α) : Iso p p := RIso.refl p

def Iso.symm {α : Type u} {p q : GPom α} (f : Iso p q) : Iso q p where
  toEquiv := f.toEquiv.symm
  actions i := by convert f.actions (f.invFun i) using 0; simp [Eq.comm]
  order i j := by convert f.order (f.invFun i) (f.invFun j) using 0; simp [Iff.comm]

def Iso.trans {α : Type u} {p q r : GPom α} (f : Iso p q) (g : Iso q r)
  : Iso p r where
  toEquiv := f.toEquiv.trans g.toEquiv
  actions i := (f.actions i).trans (g.actions (f.toFun i))
  order i j := Iff.trans (f.order i j) (g.order _ _)

def Eqv {α : Type u} (p q : GPom α) := Nonempty (Iso p q)

theorem Eqv.refl {α : Type u} (p : GPom α) : Eqv p p :=
  ⟨Iso.refl p⟩

theorem Eqv.symm {α : Type u} {p q : GPom α}
  : Eqv p q → Eqv q p | ⟨f⟩ => ⟨f.symm⟩

theorem Eqv.trans {α : Type u} {p q r : GPom α}
  : Eqv p q → Eqv q r → Eqv p r | ⟨f⟩, ⟨g⟩ => ⟨f.trans g⟩

instance EqvSetoid (α : Type u) : Setoid (GPom α) where
  r := Eqv
  iseqv := {
    refl := Eqv.refl,
    symm := Eqv.symm,
    trans := Eqv.trans
  }

structure RMatchExcept
  {α β : Type u}
  (r : Rel α β) (eα : Set α) (eβ : Set β) (p : GPom α) (q : GPom β) : Type u
  where
  toRel : Rel (Fin p.arity) (Fin q.arity)
  actions : ∀ i j, toRel i j -> r (p.actions i) (q.actions j)
  order : ∀i j i' j', toRel i j -> toRel i' j' -> (p.order.le i i' ↔ q.order.le j j')
  bij : ∀i j i' j', toRel i j -> toRel i' j' -> (i = i' ↔ j = j')
  left_skip : ∀i, (∃j, toRel i j) ∨ p.actions i ∈ eα
  right_skip : ∀j, (∃i, toRel i j) ∨ q.actions j ∈ eβ

def Match1 {α : Type u} [One α] := RMatchExcept (Eq (α := α)) {1} {1}

def Match1.refl {α : Type u} [One α] (p : GPom α) : Match1 p p
  where
  toRel := Eq
  actions i j h := by cases h; rfl
  order i j i' j' h h' := by cases h; cases h'; rfl
  bij i j i' j' h h' := by cases h; cases h'; rfl
  left_skip i := Or.inl ⟨i, rfl⟩
  right_skip j := Or.inl ⟨j, rfl⟩

def Match1.symm {α : Type u} [One α] {p q : GPom α}
  (f : Match1 p q) : Match1 q p
  where
  toRel i j := f.toRel j i
  actions i j h := (f.actions j i h).symm
  order i j i' j' h h' := Iff.symm (f.order j i j' i' h h')
  bij i j i' j' h h' := (f.bij j i j' i' h h').symm
  left_skip i := f.right_skip i
  right_skip j := f.left_skip j

def Match1.trans {α : Type u} [One α] {p q r : GPom α}
  (f : Match1 p q) (g : Match1 q r) : Match1 p r
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

def Bisim {α : Type u} [One α] (p q : GPom α) := Nonempty (Match1 p q)

theorem Bisim.refl {α : Type u} [One α] (p : GPom α) : Bisim p p :=
  ⟨Match1.refl p⟩

theorem Bisim.symm {α : Type u} [One α] {p q : GPom α}
  : Bisim p q → Bisim q p | ⟨f⟩ => ⟨f.symm⟩

theorem Bisim.trans {α : Type u} [One α] {p q r : GPom α}
  : Bisim p q → Bisim q r → Bisim p r | ⟨f⟩, ⟨g⟩ => ⟨f.trans g⟩

def BisimSetoid (α : Type u) [One α] : Setoid (GPom α) where
  r := Bisim
  iseqv := {
    refl := Bisim.refl,
    symm := Bisim.symm,
    trans := Bisim.trans
  }
-- theorem Eqv.arity_eq {p q : GPom α} : p ≈ q → p.arity = q.arity :=
--   sorry

-- theorem Eqv.singleton {p : GPom α} : p ≈ ∅ -> p = ∅ :=
--   sorry

end GPom

def Pom (α : Type u) := Quotient (GPom.EqvSetoid α)

def Pom1 (α : Type u) [One α] := Quotient (GPom.BisimSetoid α)

-- TODO: Wts Pom α has a monoid isomorphism with Pom1 (WithOne α)
