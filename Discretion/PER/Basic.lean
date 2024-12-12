import Mathlib.Order.Defs.Unbundled
import Mathlib.Order.CompleteLattice

class IsPER (α) (r : α → α → Prop) extends IsTrans α r, IsSymm α r

instance IsPER.instMk {α} (r : α → α → Prop) [IsTrans α r] [IsSymm α r] : IsPER α r where

instance IsPER.instEmptyRelation {α} : IsPER α EmptyRelation where
  trans _ _ _ h := h.elim
  symm _ _ h := h.elim

instance IsPER.bot {α} : IsPER α ⊥ := instEmptyRelation

instance IsPER.top {α} : IsPER α ⊤ where
  trans := by tauto
  symm := by tauto

instance IsPER.inf {α} {r r' : α → α → Prop} [IsPER α r] [IsPER α r'] : IsPER α (r ⊓ r') where
  trans _ _ _ h h' := ⟨Trans.trans h.1 h'.1, Trans.trans h.2 h'.2⟩
  symm _ _ h := ⟨symm h.1, symm h.2⟩

theorem IsPER.sInf {α} {rs : Set (α → α → Prop)} (hr : ∀r ∈ rs, IsPER α r) : IsPER α (sInf rs) where
  trans _ _ _ := by
    simp only [sInf_apply, iInf_apply, iInf_Prop_eq, Subtype.forall]
    intro h1 h2 a ha
    apply (hr a ha).trans _ _ _ (h1 a ha) (h2 a ha)
  symm _ _ := by
    simp only [sInf_apply, iInf_apply, iInf_Prop_eq, Subtype.forall]
    intro h a ha
    apply (hr a ha).symm _ _ (h a ha)

inductive Relation.SymmGen {α} (r : α → α → Prop) : α → α → Prop
  | rel {a b} : r a b → Relation.SymmGen r a b
  | rel_op {a b} : r b a → Relation.SymmGen r a b

theorem Relation.SymmGen.symm {α} {r : α → α → Prop} {a b : α}
  : SymmGen r a b → SymmGen r b a
  | .rel h => .rel_op h
  | .rel_op h => .rel h

theorem Relation.SymmGen.increasing {α} (r : α → α → Prop) : r ≤ SymmGen r := λ_ _ => .rel

theorem Relation.SymmGen.symmGen_eq_self {α : Type u} {r : α → α → Prop} (hs : Symmetric r)
  : SymmGen r = r := le_antisymm (λ | _, _, .rel h => h | _, _, .rel_op h => hs h) (increasing r)

theorem Relation.SymmGen.symmGen_eq_self' {α : Type u} (r : α → α → Prop) [IsSymm α r]
  : SymmGen r = r := symmGen_eq_self IsSymm.symm

theorem Relation.SymmGen.minimal {α} {r s : α → α → Prop} [IsSymm α s] (hr : r ≤ s) : SymmGen r ≤ s :=
  λa b h => by induction h with
  | rel h => exact hr _ _ h
  | rel_op h => exact IsSymm.symm _ _ <| hr _ _ h

theorem Relation.SymmGen.minimal_iff {α} (r s : α → α → Prop) [IsSymm α s] : SymmGen r ≤ s ↔ r ≤ s :=
  ⟨λh => λ_ _ h' => h _ _ (.rel h'), λh => SymmGen.minimal h⟩

theorem Relation.TransGen.increasing {α} (r : α → α → Prop) : r ≤ TransGen r := λ_ _ => .single

theorem Relation.TransGen.transGen_eq_self' {α : Type u} (r : α → α → Prop) [IsTrans α r]
  : TransGen r = r := transGen_eq_self IsTrans.trans

def Relation.PERGen {α} (r : α → α → Prop) : α → α → Prop := TransGen (SymmGen r)

theorem Relation.PERGen.trans {α} {r : α → α → Prop} {a b c : α}
  : PERGen r a b → PERGen r b c → PERGen r a c := TransGen.trans

theorem Relation.PERGen.symm {α} {r : α → α → Prop} {a b : α} (h : PERGen r a b) : PERGen r b a :=
  by induction h with
  | single h => exact .single h.symm
  | tail h h' I => exact TransGen.trans (.single h'.symm) I

instance Relation.PERGen.isper {α} {r : α → α → Prop} : IsPER α (PERGen r) where
  trans _ _ _ := trans
  symm _ _ := symm

theorem Relation.PERGen.increasing {α} (r : α → α → Prop) : r ≤ PERGen r
  := λ_ _ h => .single (.rel (h))

theorem Relation.PERGen.perGen_eq_self {α : Type u} (r : α → α → Prop) [IsPER α r]
  : PERGen r = r := by rw [PERGen, SymmGen.symmGen_eq_self', TransGen.transGen_eq_self']

theorem Relation.PERGen.minimal {α} {r s : α → α → Prop} [IsPER α s] (hr : r ≤ s) : PERGen r ≤ s :=
  λa b h => by induction h with
  | single h => exact h.minimal hr
  | tail h h' I => exact IsTrans.trans _ _ _ I (h'.minimal hr)

theorem Relation.PERGen.minimal_iff {α} (r s : α → α → Prop) [IsPER α s] : PERGen r ≤ s ↔ r ≤ s :=
  ⟨λh => λ_ _ h' => h _ _ (.single <| .rel h'), λh => PERGen.minimal h⟩

structure PER (α) where
  r : α → α → Prop
  isper : IsPER α r

@[ext]
theorem PER.ext {α} {a b : PER α} (h : a.r = b.r) : a = b := by cases a; cases b; cases h; rfl

instance PER.instCoe {α} : Coe (PER α) (α → α → Prop) where
  coe a := a.r

instance PER.instIsPER {α} (a : PER α) : IsPER α a := a.isper

instance PER.instPartialOrder {α : Type u} : PartialOrder (PER α) where
  le a b := a.r ≤ b.r
  le_refl a := Preorder.le_refl (α := α → α → Prop) a.r
  le_trans a b c := Preorder.le_trans (α := α → α → Prop) a.r b.r c.r
  le_antisymm a b h h' := ext (PartialOrder.le_antisymm (α := α → α → Prop) a.r b.r h h')

theorem PER.le_iff {α} {a b : PER α} : a ≤ b ↔ a.r ≤ b.r := Iff.rfl

instance PER.instBoundedOrder {α : Type u} : BoundedOrder (PER α) where
  top := ⟨⊤, IsPER.top⟩
  le_top a := OrderTop.le_top (α := α → α → Prop) a.r
  bot := ⟨⊥, IsPER.bot⟩
  bot_le a := OrderBot.bot_le (α := α → α → Prop) a.r

instance PER.instMin {α : Type u} : Min (PER α) where
  min a b := ⟨a.r ⊓ b.r, IsPER.inf⟩

instance PER.instMax {α : Type u} : Max (PER α) where
  max a b := ⟨Relation.PERGen (a.r ⊔ b.r), Relation.PERGen.isper⟩

instance PER.instCompleteLattice {α : Type u} : CompleteLattice (PER α) where
  inf a b := a ⊓ b
  inf_le_left a b := SemilatticeInf.inf_le_left (α := α → α → Prop) a.r b.r
  inf_le_right a b := SemilatticeInf.inf_le_right (α := α → α → Prop) a.r b.r
  le_inf a b c := SemilatticeInf.le_inf (α := α → α → Prop) a.r b.r c.r
  sInf s := ⟨sInf (Coe.coe '' s), IsPER.sInf (λr ⟨a, _, ha⟩ => by cases ha; apply PER.isper)⟩
  sInf_le s a ha := CompleteSemilatticeInf.sInf_le (Coe.coe '' s) a.r ⟨_, ha, rfl⟩
  le_sInf s a ha := CompleteSemilatticeInf.le_sInf (Coe.coe '' s) a.r
    (λ_ ⟨b, hb, he⟩ => by cases he; exact ha _ hb)
  le_top := OrderTop.le_top
  bot_le := OrderBot.bot_le
  sup a b := a ⊔ b
  le_sup_left _ _ := by rw [le_iff]; exact le_trans le_sup_left (Relation.PERGen.increasing _)
  le_sup_right _ _ := by rw [le_iff]; exact le_trans le_sup_right (Relation.PERGen.increasing _)
  sup_le _ _ _ h h' := Relation.PERGen.minimal (sup_le h h')
  sSup s := ⟨Relation.PERGen (sSup (Coe.coe '' s)), Relation.PERGen.isper⟩
  le_sSup _ a h
    := by rw [le_iff]; exact le_trans (le_sSup (by exists a)) (Relation.PERGen.increasing _)
  sSup_le a s h := Relation.PERGen.minimal (sSup_le (λb ⟨b', hb, he⟩ => by cases he; exact h _ hb))

def PER.elem {α} (r : PER α) : Set α := {a | r.r a a}

theorem PER.elem_left {α} (r : PER α) {a b : α} (h : r.r a b) : a ∈ r.elem := trans h (symm h)

theorem PER.elem_right {α} (r : PER α) {a b : α} (h : r.r a b) : b ∈ r.elem := trans (symm h) h

theorem PER.elem_top {α} : (⊤ : PER α).elem = ⊤ := Set.ext (λ_ => Iff.rfl)

theorem PER.elem_bot {α} : (⊥ : PER α).elem = ⊥ := Set.ext (λ_ => Iff.rfl)
