import Mathlib.Algebra.Group.WithOne.Defs
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Order.BoundedOrder
import Mathlib.Order.Lattice

class Split (α : Type u) where
  splits : α → α → α → Prop

class Resource (α : Type u) extends Split α, Zero α where
  splits_comm : ∀ {a b c}, splits a b c → splits a c b
  splits_assoc : ∀ {a123 a12 a1 a2 a3},
    splits a123 a12 a3 → splits a12 a1 a2 → ∃a23, splits a123 a1 a23 ∧ splits a23 a2 a3
  splits_zero_left : ∀ {a}, splits a 0 a
  splits_weakens_right : ∀ {a b c d}, splits a b c → splits c 0 d → splits a b d

def Affine (α : Type u) := WithZero α

instance Affine.instZero {α} : Zero (Affine α) := (inferInstance : Zero (WithZero α))

def Relevant (α : Type u) := WithZero α

instance Relevant.instZero {α} : Zero (Relevant α) := (inferInstance : Zero (WithZero α))

def Nonlinear (α : Type u) := WithZero α

instance Nonlinear.instZero {α} : Zero (Nonlinear α) := (inferInstance : Zero (WithZero α))

def OrdRes (α : Type u) := α

instance OrdRes.instBot [Bot α] : Bot (OrdRes α) := (inferInstance : Bot α)

instance OrdRes.instTop [Top α] : Top (OrdRes α) := (inferInstance : Top α)

instance OrdRes.instLE [LE α] : LE (OrdRes α) := (inferInstance : LE α)

instance OrdRes.instPreorder [Preorder α] : Preorder (OrdRes α)
  := (inferInstance : Preorder α)

instance OrdRes.instPartialOrder [PartialOrder α] : PartialOrder (OrdRes α)
  := (inferInstance : PartialOrder α)

instance OrdRes.instOrderBot [LE α] [OrderBot α] : OrderBot (OrdRes α)
  := (inferInstance : OrderBot α)

instance OrdRes.instOrderTop [LE α] [OrderTop α] : OrderTop (OrdRes α)
  := (inferInstance : OrderTop α)

instance OrdRes.instMax [Max α] : Max (OrdRes α) := (inferInstance : Max α)

instance OrdRes.instMin [Min α] : Min (OrdRes α) := (inferInstance : Min α)

instance OrdRes.instSemilatticeInf [SemilatticeInf α] : SemilatticeInf (OrdRes α)
  := (inferInstance : SemilatticeInf α)

instance OrdRes.instSemilatticeSup [SemilatticeSup α] : SemilatticeSup (OrdRes α)
  := (inferInstance : SemilatticeSup α)

instance OrdRes.instLattice [Lattice α] : Lattice (OrdRes α) := (inferInstance : Lattice α)

instance OrdRes.instZero [Bot α] : Zero (OrdRes α) := ⟨⊥⟩

def MonRes (α : Type u) := α

instance MonRes.instAddCommMonoid [AddCommMonoid α] : AddCommMonoid (MonRes α)
  := (inferInstance : AddCommMonoid α)

def Ctx (α : Type u) := List α

instance Ctx.instZero {α} : Zero (Ctx α) := ⟨[]⟩

@[match_pattern]
def Ctx.cons {α} (a : α) (Γ : Ctx α) : Ctx α := List.cons a Γ

@[match_pattern]
def Ctx.nil {α} : Ctx α := []

instance Ctx.instEmptyCollection {α} : EmptyCollection (Ctx α) := ⟨Ctx.nil⟩

infixr:67 " ::ᶜ " => Ctx.cons

inductive Ctx.Wk : Ctx α → Ctx α → Prop
  | nil : Ctx.Wk ∅ ∅
  | cons (a : α) (Γ Δ) : Ctx.Wk Γ Δ → Ctx.Wk (a ::ᶜ Γ) (a ::ᶜ Δ)
  | skip (a : α) (Γ Δ) : Ctx.Wk Γ Δ → Ctx.Wk (a ::ᶜ Γ) Δ

def Ctx.Splits (Γ Δ Θ : Ctx α) : Prop := Γ.Wk Δ ∧ Γ.Wk Θ

theorem Ctx.Wk.refl {Γ : Ctx α} : Γ.Wk Γ := by induction Γ <;> constructor; assumption

theorem Ctx.Wk.trans {Γ Δ Θ : Ctx α} (h1 : Γ.Wk Δ) (h2 : Δ.Wk Θ) : Γ.Wk Θ := by
  induction h1 generalizing Θ
  <;> cases h2 <;> constructor <;> apply_assumption
  <;> first | assumption | constructor; assumption

theorem Ctx.Wk.affine {Γ : Ctx α} : Γ.Wk ∅ := by induction Γ <;> constructor; assumption

theorem Ctx.Splits.relevant {Γ : Ctx α} : Γ.Splits Γ Γ := ⟨Ctx.Wk.refl, Ctx.Wk.refl⟩

theorem Ctx.Splits.nil : Ctx.Splits (α := α) ∅ ∅ ∅ := relevant

theorem Ctx.Splits.left (a) {Γ Δ Θ : Ctx α} (h : Γ.Splits Δ Θ) : Splits (a :: Γ) (a :: Δ) Θ
  := ⟨h.1.cons a, h.2.skip a⟩

theorem Ctx.Splits.right (a) {Γ Δ Θ : Ctx α} (h : Γ.Splits Δ Θ) : Splits (a :: Γ) Δ (a :: Θ)
  := ⟨h.1.skip a, h.2.cons a⟩

theorem Ctx.Splits.both (a) {Γ Δ Θ : Ctx α} (h : Γ.Splits Δ Θ) : Splits (a :: Γ) (a :: Δ) (a :: Θ)
  := ⟨h.1.cons a, h.2.cons a⟩

theorem Ctx.Splits.neither (a) {Γ Δ Θ : Ctx α} (h : Γ.Splits Δ Θ) : Splits (a :: Γ) Δ Θ
  := ⟨h.1.skip a, h.2.skip a⟩

theorem Ctx.Splits.induction {motive : (Γ Δ Θ : Ctx α) → Splits Γ Δ Θ → Prop}
  (nil : motive ∅ ∅ ∅ ⟨Ctx.Wk.nil, Ctx.Wk.nil⟩)
  (left : ∀a Γ Δ Θ h, motive Γ Δ Θ h → motive (a :: Γ) (a :: Δ) Θ (Splits.left a h))
  (right : ∀a Γ Δ Θ h, motive Γ Δ Θ h → motive (a :: Γ) Δ (a :: Θ) (Splits.right a h))
  (both : ∀a Γ Δ Θ h, motive Γ Δ Θ h → motive (a :: Γ) (a :: Δ) (a :: Θ) (Splits.both a h))
  (neither : ∀a Γ Δ Θ h, motive Γ Δ Θ h → motive (a :: Γ) Δ Θ (Splits.neither a h))
  {Γ Δ Θ} : (h : Splits Γ Δ Θ) → motive Γ Δ Θ h
  | ⟨h1, h2⟩ => by induction h1 generalizing Θ with
  | nil => cases h2; apply nil
  | cons a Γ Δ h ih => cases h2 with
    | cons a Δ Θ h2 => exact both _ _ _ _ ⟨h, h2⟩ (ih h2)
    | skip a Δ Θ h2 => exact left _ _ _ _ ⟨h, h2⟩ (ih h2)
  | skip a Γ Δ h ih => cases h2 with
    | cons a Δ Θ h2 => exact right _ _ _ _ ⟨h, h2⟩ (ih h2)
    | skip a Δ Θ h2 => exact neither _ _ _ _ ⟨h, h2⟩ (ih h2)

def RCtx (α : Type u) := List α

instance RCtx.instZero {α} : Zero (RCtx α) := ⟨[]⟩

@[match_pattern]
def RCtx.cons {α} (a : α) (Γ : Ctx α) : RCtx α := List.cons a Γ

@[match_pattern]
def RCtx.nil {α} : RCtx α := []

instance RCtx.instEmptyCollection {α} : EmptyCollection (RCtx α) := ⟨RCtx.nil⟩

infixr:67 " ::ʳ " => Ctx.cons

namespace Resource

open Split

variable {α : Type u}

instance instWithZero : Resource (WithZero α) where
  splits a b c := (b = a ∧ c = 0) ∨ (b = 0 ∧ c = a)
  splits_comm | Or.inl ⟨h1, h2⟩ => Or.inr ⟨h2, h1⟩ | Or.inr ⟨h1, h2⟩ => Or.inl ⟨h2, h1⟩
  splits_assoc  | Or.inl ⟨rfl, h3⟩, h => ⟨_, h, Or.inl ⟨rfl, h3⟩⟩
                | h, Or.inl ⟨rfl, h2⟩ => ⟨_, h, Or.inr ⟨h2, rfl⟩⟩
                | h, Or.inr ⟨h1, rfl⟩ => ⟨_, Or.inr ⟨h1, rfl⟩, h⟩
  splits_zero_left := Or.inr ⟨rfl, rfl⟩
  splits_weakens_right h | Or.inl ⟨h1, h2⟩ | Or.inr ⟨h1, h2⟩ => by cases h1; cases h2; exact h

instance instNonlinear : Resource (Nonlinear α) where
  splits a b c := (b = a ∨ b = 0) ∧ (c = a ∨ c = 0)
  splits_comm := And.symm
  splits_assoc {a123} | ⟨ha12, ha3⟩, ⟨ha1, ha2⟩ => ⟨a123, by aesop⟩
  splits_zero_left := ⟨Or.inr rfl, Or.inl rfl⟩
  splits_weakens_right h1 h2 := by aesop

instance instCtx : Resource (Ctx α) where
  splits := Ctx.Splits
  splits_comm h := ⟨h.2, h.1⟩
  splits_assoc h123 h12 := ⟨_, ⟨h123.1.trans h12.1, Ctx.Wk.refl⟩, ⟨h123.1.trans h12.2, h123.2⟩⟩
  splits_zero_left := ⟨Ctx.Wk.affine, Ctx.Wk.refl⟩
  splits_weakens_right h h' := ⟨h.1, h.2.trans h'.2⟩

instance instOrdRes [Preorder α] [OrderTop α] : Resource (OrdRes α) where
  splits a b c := (a ≤ b ∧ a ≤ c)
  splits_comm := And.symm
  splits_assoc h123 h12 := ⟨_, ⟨le_trans h123.1 h12.1, le_refl _⟩, ⟨le_trans h123.1 h12.2, h123.2⟩⟩
  splits_zero_left := ⟨le_top, le_refl _⟩
  splits_weakens_right h1 h2 := ⟨h1.1, le_trans h1.2 h2.2⟩

instance instMonRes [AddCommMonoid α] : Resource (MonRes α) where
  splits a b c := (a = b + c)
  splits_comm h := by simp only [add_comm]; exact h
  splits_assoc h123 h12 := by cases h123; cases h12; exact ⟨_, by simp [add_assoc], rfl⟩
  splits_zero_left := by simp
  splits_weakens_right h1 h2 := by cases h2; convert h1; simp

instance instPiSplit [Split α] {ι : Type v} : Split (ι → α) where
  splits a b c := ∀i, splits (a i) (b i) (c i)

class Splits [Split α] (a b c : α) where
  prop : splits a b c

abbrev Wk [Split α] [Zero α] (a b : α) := Splits a 0 b

abbrev Drop [Split α] [Zero α] (a : α) := Wk a 0

abbrev Copy [Split α] (a : α) := Splits a a a

class Affine (α) [Split α] [Zero α] where
  prop : ∀a : α, splits a 0 0

instance Affine.instCtx : Affine (Ctx α) where
  prop _ := ⟨Ctx.Wk.affine, Ctx.Wk.affine⟩

instance Splits.affine {a : α} [Split α] [Zero α] [Affine α]  : Drop a := ⟨Affine.prop a⟩

class Relevant (α) [Split α] where
  prop : ∀a : α, splits a a a

instance Relevant.instCtx : Relevant (Ctx α) where
  prop _ := ⟨Ctx.Wk.refl, Ctx.Wk.refl⟩

instance Splits.relevant {a : α} [Split α] [Relevant α] : Splits a a a
  := ⟨Relevant.prop a⟩

instance Splits.instPi [Split α] {ι : Type v} {a b c : ι → α}
  [h : ∀i, Splits (a i) (b i) (c i)] : Splits a b c := ⟨λi => (h i).1⟩

variable [Resource α]

instance Splits.refl_left {a : α} : Splits a 0 a := ⟨splits_zero_left⟩

theorem Splits.comm {a b c : α} (h : Splits a b c) : Splits a c b := ⟨splits_comm h.prop⟩

instance Splits.refl_right {a : α} : Splits a a 0 := refl_left.comm

theorem Splits.assoc_left {a123 a12 a1 a2 a3 : α}
  (h : Splits a123 a12 a3) (h12 : Splits a12 a1 a2) : ∃a23, Splits a123 a1 a23 ∧ Splits a23 a2 a3
  := have ⟨a23, h1, h2⟩ := splits_assoc h.prop h12.prop; ⟨a23, ⟨h1⟩, ⟨h2⟩⟩

theorem Splits.assoc_right {a123 a23 a1 a2 a3 : α}
  (h : Splits a123 a1 a23) (h23 : Splits a23 a2 a3) : ∃a12, Splits a123 a12 a3 ∧ Splits a12 a1 a2
  := have ⟨a12, h1, h2⟩ := h.comm.assoc_left h23.comm; ⟨a12, h1.comm, h2.comm⟩

theorem Wk.refl {a : α} : Wk a a := inferInstance

theorem Splits.wk_right {a b c d : α} (h1 : Splits a b c) (h2 : Wk c d) : Splits a b d :=
  ⟨splits_weakens_right h1.prop h2.prop⟩

theorem Splits.wk_left {a b c d : α} (h1 : Splits a b c) (h2 : Wk b d) : Splits a d c :=
  (h1.comm.wk_right h2).comm

theorem Wk.trans {a b c : α} (h1 : Wk a b) (h2 : Wk b c) : Wk a c := h1.wk_right h2

theorem Drop.wk {a b : α} (h1 : Wk a b) (h2 : Drop b) : Drop a := h1.trans h2

instance instPi {ι : Type v} : Resource (ι → α) where
  splits_comm h i := splits_comm (h i)
  splits_assoc h123 h12 :=
    have h123' := λi => splits_assoc (h123 i) (h12 i)
    ⟨λi => (h123' i).choose, (λi => (h123' i).choose_spec.1), (λi => (h123' i).choose_spec.2)⟩
  splits_zero_left _ := splits_zero_left
  splits_weakens_right h h' i := splits_weakens_right (h i) (h' i)

end Resource

class ResourceSystem.{u} (τ : Type u) where
  res : τ → Type
  isResource : ∀t, Resource (res t)

variable {τ : Type u} [ResourceSystem τ]

def res : τ → Type := ResourceSystem.res

instance Resource.instRes {t : τ} : Resource (res t) := ResourceSystem.isResource t

open Resource
