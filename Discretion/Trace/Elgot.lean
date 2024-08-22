import Discretion.Trace.Basic
import Discretion.Elgot.Monad
import Discretion.Stream.Action

open StreamProd

namespace Trace

variable {step : α → Set (Trace ε τ (β ⊕ α))}

def mapLeftTraces (step : α → Set (Trace ε τ (β ⊕ γ)))
  (a : α) : Set (Trace ε τ β) := { b : Trace ε τ β | Sum.inl <$> b ∈ step a }

def mapRightTraces (step : α → Set (Trace ε τ (β ⊕ γ)))
  (a : α) : Set (Trace ε τ γ) := { c : Trace ε τ γ | Sum.inr <$> c ∈ step a }

def IsLeft : Trace ε τ (α ⊕ β) → Prop
  | done (Sum.inl _) _ => True
  | _ => False

def IsRight : Trace ε τ (α ⊕ β) → Prop
  | done (Sum.inr _) _ => True
  | _ => False

def Diverges : Trace ε τ (α ⊕ β) → Prop
  | inf _ => True
  | _ => False

def IsEffectList (step : α → Set (Trace ε τ (β ⊕ α))) (a : α) : List ε → Trace ε τ β → Prop
  | [] , b => Sum.inl <$> b ∈ step a
  | e::t, b => ∃a', done (Sum.inr a') e ∈ step a ∧ IsEffectList step a' t b

theorem IsEffectList.cons_iff {a : α} {e : ε} {es : List ε} {b : Trace ε τ β}
  : IsEffectList step a (e::es) b ↔ ∃a', done (Sum.inr a') e ∈ step a ∧ IsEffectList step a' es b
  := Iff.rfl

def IsEffectStream (step : α → Set (Trace ε τ (β ⊕ α))) (as : Stream' α) (es : Stream' ε) : Prop
  := ∀n, done (Sum.inr (as.get (n + 1))) (es.get (n + 1)) ∈ step (as.get n)

theorem IsEffectStream.tail (h : IsEffectStream step as es) : IsEffectStream step as.tail es.tail
  := λn => h (n + 1)

theorem IsEffectStream.head (h : IsEffectStream step as es)
  : done (Sum.inr (as.get 1)) (es.get 1) ∈ step (as.get 0)
  := h 0

theorem IsEffectStream.cons
  (ha : done (Sum.inr (as.get 0)) (es.get 0) ∈ step a) (h : IsEffectStream step as es)
  : IsEffectStream step (as.cons a) (es.cons e) | 0 => ha | n + 1 => h n

theorem IsEffectStream.cons_iff : IsEffectStream step (as.cons a) (es.cons e)
  ↔ done (Sum.inr (as.get 0)) (es.get 0) ∈ step a ∧ IsEffectStream step as es
  := ⟨λh => ⟨h.head, h.tail⟩, λ⟨hd, h⟩ => h.cons hd⟩

theorem IsEffectStream.tail_iff
  : IsEffectStream step as es
  ↔ done (Sum.inr (as.get 1)) (es.get 1) ∈ step (as.get 0) ∧ IsEffectStream step as.tail es.tail
  := by
  convert cons_iff (a := as.head) (e := es.head) (as := as.tail) (es := es.tail) using 2 <;>
  funext k <;> cases k <;> rfl

def effectStreams (step : α → Set (Trace ε τ (β ⊕ α))) (a : α) : Set (Stream' ε)
  := {es : Stream' ε | ∃as : Stream' α,
                              done (Sum.inr (as 0)) (es 0) ∈ step a ∧ IsEffectStream step as es}

def actionStreams (step : α → Set (Trace ε τ (β ⊕ α))) (a : α) : Set (Stream' α)
  := {as : Stream' α | ∃es : Stream' ε,
                              done (Sum.inr (as 0)) (es 0) ∈ step a ∧ IsEffectStream step as es}

theorem effectStreams_nonempty_iff_actionStreams_nonempty
  : (effectStreams step a).Nonempty ↔ (actionStreams step a).Nonempty
  := by
  apply Iff.intro
  · intro ⟨es, ⟨as, ha0, has⟩⟩
    exact ⟨as, ⟨es, ha0, has⟩⟩
  · intro ⟨as, ⟨es, ha0, has⟩⟩
    exact ⟨es, ⟨as, ha0, has⟩⟩

theorem effectStreams_empty_iff_actionStreams_empty
  : effectStreams step a = ∅ ↔ actionStreams step a = ∅
  := by simp [<-Set.not_nonempty_iff_eq_empty, effectStreams_nonempty_iff_actionStreams_nonempty]

def infiniteResults [StreamProd ε τ] (step : α → Set (Trace ε τ (β ⊕ α))) (a : α) : Set τ
  := streamProd '' effectStreams step a

def infiniteTraces [StreamProd ε τ] (step : α → Set (Trace ε τ (β ⊕ α))) (a : α)
  : Set (Trace ε τ γ) := inf '' infiniteResults step a

def leftResults (step : α → Set (Trace ε τ (β ⊕ γ))) (a : α) : Set (β × ε)
  := { (b, e) : β × ε | done (Sum.inl b) e ∈ step a }

def rightResults (step : α → Set (Trace ε τ (β ⊕ γ))) (a : α) : Set (γ × ε)
  := { (c, e) : γ × ε | done (Sum.inr c) e ∈ step a }

def divergentResults (step : α → Set (Trace ε τ (β ⊕ γ))) (a : α) : Set τ
  := { t : τ | inf t ∈ step a }

def leftTraces (step : α → Set (Trace ε τ (β ⊕ γ))) (a : α) : Set (Trace ε τ β)
  := (λ(b, e) => done b e) '' leftResults step a

def rightTraces (step : α → Set (Trace ε τ (β ⊕ γ))) (a : α) : Set (Trace ε τ γ)
  := (λ(c, e) => done c e) '' rightResults step a

def divergentTraces (step : α → Set (Trace ε τ (β ⊕ γ))) (a : α) : Set (Trace ε τ δ)
  := inf '' divergentResults step a

theorem iUnion_rightResults_effectStreams
  : ⋃ r ∈ rightResults step a , Stream'.cons r.2 '' effectStreams step r.1
    = effectStreams step a := by
  ext es
  simp only [Set.mem_iUnion, Set.mem_image, exists_prop, Prod.exists]
  constructor
  · intro ⟨a, e, hae, es, ⟨as, ha0, has⟩, hes⟩
    cases hes
    exact ⟨as.cons a, hae, has.cons ha0⟩
  · intro ⟨as, ha0, has⟩
    exact ⟨as.head, es.head, ha0, es.tail,
      ⟨as.tail, has.head, has.tail⟩,
      by funext k; cases k <;> rfl⟩

theorem iUnion_rightResults_actionStreams
  : ⋃ r ∈ rightResults step a , Stream'.cons r.1 '' actionStreams step r.1
    = actionStreams step a := by
  ext as
  simp only [Set.mem_iUnion, Set.mem_image, exists_prop, Prod.exists]
  constructor
  · intro ⟨a, e, hae, as, ⟨es, ha0, has⟩, hes⟩
    cases hes
    exact ⟨es.cons e, hae, has.cons ha0⟩
  · intro ⟨es, ha0, has⟩
    exact ⟨as.head, es.head, ha0, as.tail,
      ⟨es.tail, has.head, has.tail⟩,
      by funext k; cases k <;> rfl⟩

section Ops

variable [SMul ε τ]

theorem iUnion_rightResults_infiniteResults [StreamMulAction ε τ]
  : ⋃ r ∈ rightResults step a , (r.2 • ·) '' infiniteResults step r.1 = infiniteResults step a
  := calc
  _ = streamProd '' ⋃ r ∈ rightResults step a , Stream'.cons r.2 '' effectStreams step r.1
    := by simp [Set.image_iUnion, Set.image_image, infiniteResults, StreamMulAction.streamProd_cons]
  _ = _
    := by rw [infiniteResults, iUnion_rightResults_effectStreams]

variable [Mul ε]

@[simp]
def prependTrace : List ε → Trace ε τ α → Trace ε τ α
  | [], t => t
  | e::es, t => e • (prependTrace es t)

def approxFiniteTraces (step : α → Set (Trace ε τ (β ⊕ α))) (a : α)
  : ℕ → Set (Trace ε τ β)
  | 0 => mapLeftTraces step a
  | n + 1 => ⋃ r ∈ rightResults step a, (r.2 • ·) '' approxFiniteTraces step r.1 n

def finiteTraces (step : α → Set (Trace ε τ (β ⊕ α))) (a : α) : Set (Trace ε τ β)
  := ⋃ n, approxFiniteTraces step a n

theorem mapLeftTraces_subset_finiteTraces
  : mapLeftTraces step a ⊆ finiteTraces step a
  := by intro t ht; simp only [finiteTraces, Set.mem_iUnion]; exact ⟨0, ht⟩

theorem mapLeftTraces_empty_of_finiteTraces_empty (h : finiteTraces step a = ∅)
  : mapLeftTraces step a = ∅ := Set.subset_eq_empty mapLeftTraces_subset_finiteTraces h

def iterateTraces [StreamProd ε τ] (step : α → Set (Trace ε τ (β ⊕ α))) (a : α)
  : Set (Trace ε τ β) := finiteTraces step a ∪ infiniteTraces step a

theorem mapLeftTraces_union_iUnion_rightResults_finiteTraces
  : mapLeftTraces step a ∪ ⋃ r ∈ rightResults step a , (r.2 • ·) '' finiteTraces step r.1
  = finiteTraces step a := calc
  _ = approxFiniteTraces step a 0 ∪
      ⋃ r ∈ rightResults step a , ⋃n, (r.2 • ·) '' approxFiniteTraces step r.1 n
    := by simp only [approxFiniteTraces, finiteTraces, Set.image_iUnion]; rfl
  _ = approxFiniteTraces step a 0 ∪ ⋃n, approxFiniteTraces step a (n + 1)
    := by
    congr; ext t
    simp only [Set.mem_iUnion, Set.mem_image, exists_prop, Prod.exists, approxFiniteTraces]
    rw [exists_comm (α := ℕ)]
    apply exists_congr; intro a
    rw [exists_comm (α := ℕ)]
    apply exists_congr; intro b
    simp
  _ = _
    := by ext t; simp only [Set.mem_union, Set.mem_iUnion, finiteTraces]; exact ⟨
        λ| Or.inl h => ⟨0, h⟩ | Or.inr ⟨i, h⟩ => ⟨i + 1, h⟩,
        λ| ⟨0, h⟩ => Or.inl h | ⟨n + 1, h⟩ => Or.inr ⟨n, h⟩⟩

theorem rightResults_finiteTraces_empty_of_finiteTraces_empty
  (h : finiteTraces step a = ∅) : ∀ r ∈ rightResults step a , finiteTraces step r.1 = ∅ := by
  rw [<-mapLeftTraces_union_iUnion_rightResults_finiteTraces] at h
  simp only [Set.union_empty_iff, Set.iUnion_eq_empty, Set.image_eq_empty, Prod.forall] at h
  intro (a, e) hr
  apply h.2 a e hr

noncomputable def choose_action_finiteTrace_empty
  (hstep : ∀a, Set.Nonempty (step a)) (a) (hfin : finiteTraces step a = ∅) : Stream' α
  := λn =>
    have h : ∃r : α × ε, r ∈ rightResults step a := by
      let ⟨t, ht⟩ := hstep a;
      cases t with
      | done d e => cases d with
        | inl b =>
          apply False.elim (Set.Nonempty.ne_empty _ hfin)
          exact ⟨done b e, mapLeftTraces_subset_finiteTraces ht⟩
        | inr a => exact ⟨(a, e), ht⟩
      | inf t =>
        apply False.elim (Set.Nonempty.ne_empty _ hfin)
        exact ⟨inf t, mapLeftTraces_subset_finiteTraces ht⟩;
    match n with
    | 0 => (Classical.choose h).1
    | n + 1 => choose_action_finiteTrace_empty hstep (Classical.choose h).1
      (rightResults_finiteTraces_empty_of_finiteTraces_empty hfin _ (Classical.choose_spec h)) n

noncomputable def choose_effect_finiteTrace_empty
  (hstep : ∀a, Set.Nonempty (step a)) (a) (hfin : finiteTraces step a = ∅) : Stream' ε
  := λn =>
    have h : ∃r : α × ε, r ∈ rightResults step a := by
      let ⟨t, ht⟩ := hstep a;
      cases t with
      | done d e => cases d with
        | inl b =>
          apply False.elim (Set.Nonempty.ne_empty _ hfin)
          exact ⟨done b e, mapLeftTraces_subset_finiteTraces ht⟩
        | inr a => exact ⟨(a, e), ht⟩
      | inf t =>
        apply False.elim (Set.Nonempty.ne_empty _ hfin)
        exact ⟨inf t, mapLeftTraces_subset_finiteTraces ht⟩;
    match n with
    | 0 => (Classical.choose h).2
    | n + 1 => choose_effect_finiteTrace_empty hstep (Classical.choose h).1
      (rightResults_finiteTraces_empty_of_finiteTraces_empty hfin _ (Classical.choose_spec h)) n

def _root_.Classical.choose_spec_p {p : α → Prop} {h :  ∃ (x : α), p x} {c : α}
  (_ : Classical.choose h = c) : α → Prop := p

def _root_.Classical.choose_spec_h {p : α → Prop} {h :  ∃ (x : α), p x} {c : α}
  (_ : Classical.choose h = c) : ∃ (x : α), p x := h

theorem _root_.Classical.choose_spec_eq {p : α → Prop} {h :  ∃ (x : α), p x} {c : α}
  (h : Classical.choose h = c) : p c := by cases h; exact Classical.choose_spec h

theorem choose_finiteTrace_empty_spec
  (hstep : ∀a, Set.Nonempty (step a)) (a) (hfin : finiteTraces step a = ∅)
  : IsEffectStream step
    (choose_action_finiteTrace_empty hstep a hfin)
    (choose_effect_finiteTrace_empty hstep a hfin) := by
  intro n
  induction n generalizing step a with
  | zero =>
    simp only [choose_action_finiteTrace_empty, choose_effect_finiteTrace_empty, Stream'.get]
    generalize hc : Classical.choose _ = c;
    exact hc ▸ Classical.choose_spec (Classical.choose_spec_h hc)
  | succ n I =>
    simp only [choose_action_finiteTrace_empty, choose_effect_finiteTrace_empty, Stream'.get] at *
    apply I

theorem choose_action_finiteTrace_empty_spec
  (hstep : ∀a, Set.Nonempty (step a)) (a) (hfin : finiteTraces step a = ∅)
  : choose_action_finiteTrace_empty hstep a hfin ∈ actionStreams step a
  := ⟨choose_effect_finiteTrace_empty hstep a hfin,
    by
      simp only [choose_action_finiteTrace_empty, choose_effect_finiteTrace_empty]
      generalize hc : Classical.choose _ = c;
      exact hc ▸ Classical.choose_spec (Classical.choose_spec_h hc)
    ,
    choose_finiteTrace_empty_spec hstep a hfin⟩

theorem choose_effect_finiteTrace_empty_spec
  (hstep : ∀a, Set.Nonempty (step a)) (a) (hfin : finiteTraces step a = ∅)
  : choose_effect_finiteTrace_empty hstep a hfin ∈ effectStreams step a
  := ⟨choose_action_finiteTrace_empty hstep a hfin,
    by
      simp only [choose_action_finiteTrace_empty, choose_effect_finiteTrace_empty]
      generalize hc : Classical.choose _ = c;
      exact hc ▸ Classical.choose_spec (Classical.choose_spec_h hc)
    ,
    choose_finiteTrace_empty_spec hstep a hfin⟩

theorem effectStreams_nonempty_of_finiteTrace_empty
  (hstep : ∀a, Set.Nonempty (step a)) (a) (hfin : finiteTraces step a = ∅)
  : (effectStreams step a).Nonempty := ⟨_, choose_effect_finiteTrace_empty_spec hstep a hfin⟩

theorem actionStreams_nonempty_of_finiteTrace_empty
  (hstep : ∀a, Set.Nonempty (step a)) (a) (hfin : finiteTraces step a = ∅)
  : (actionStreams step a).Nonempty := ⟨_, choose_action_finiteTrace_empty_spec hstep a hfin⟩

theorem infiniteResults_nonempty_of_finiteTrace_empty [StreamProd ε τ]
  (hstep : ∀a, Set.Nonempty (step a)) (a) (hfin : finiteTraces step a = ∅)
  : (infiniteResults step a).Nonempty := by
  simp only [infiniteResults, Set.image_nonempty]
  apply effectStreams_nonempty_of_finiteTrace_empty hstep a hfin

theorem infiniteTraces_nonempty_of_finiteTrace_empty [StreamProd ε τ]
  (hstep : ∀a, Set.Nonempty (step a)) (a) (hfin : finiteTraces step a = ∅)
  : (infiniteTraces (γ := γ) step a).Nonempty := by
  simp only [infiniteTraces, Set.image_nonempty]
  apply infiniteResults_nonempty_of_finiteTrace_empty hstep a hfin

theorem iterateTraces_nonempty [StreamProd ε τ]
  (hstep : ∀a, Set.Nonempty (step a)) (a) : (iterateTraces step a).Nonempty := by
  simp only [iterateTraces, Set.union_nonempty]
  if h : (finiteTraces step a).Nonempty then
    exact Or.inl h
  else
    exact Or.inr (infiniteTraces_nonempty_of_finiteTrace_empty hstep a
      (Set.not_nonempty_iff_eq_empty.mp h))

-- TODO: determinism via subsingleton preservation...

variable [StreamMulAction ε τ]

theorem iUnion_rightResults_infiniteTraces
  : ⋃ r ∈ rightResults step a , (r.2 • ·) '' infiniteTraces step r.1
  = infiniteTraces (γ := γ) step a
  := calc
  _ = inf '' ⋃ r ∈ rightResults step a , (r.2 • ·) '' infiniteResults step r.1
    := by simp [Set.image_iUnion, Set.image_image, infiniteTraces, StreamMulAction.streamProd_cons]
  _ = _
    := by rw [infiniteTraces, iUnion_rightResults_infiniteResults]

theorem mapLeftTraces_union_iUnion_rightResults_iterateTraces
  : mapLeftTraces step a ∪ ⋃ r ∈ rightResults step a , (r.2 • ·) '' iterateTraces step r.1
  = iterateTraces step a := calc
  _ = mapLeftTraces step a
    ∪ (⋃ r ∈ rightResults step a , (r.2 • ·) '' finiteTraces step r.1)
    ∪ (⋃ r ∈ rightResults step a , (r.2 • ·) '' infiniteTraces step r.1)
    := by
      simp only [iterateTraces, Set.image_union, Set.union_assoc, <-Set.iUnion_union_distrib]
      rfl
  _ = _
    := by
    rw [mapLeftTraces_union_iUnion_rightResults_finiteTraces, iUnion_rightResults_infiniteTraces]
    rfl

end Ops

end Trace

-- namespace Trace

-- variable {ε τ} [Monoid ε] [MulAction ε τ]

-- noncomputable instance instMonadIterate : MonadIterate (Trace ε τ) where
--   iterate f x := ⟨sorry, sorry⟩

-- end Trace

open Trace

namespace Traces?

variable {ε : Type u} {τ : Type v} [Monoid ε] [MulAction ε τ] [StreamMulAction ε τ]

open MonadIterate

instance instMonadIterate : MonadIterate.{w, max u v w} (Traces? ε τ) where
  iterate f x := iterateTraces f x

-- instance instElgotMonad : ElgotMonad (Traces? ε τ) where
--   fixpoint f := by
--     ext x
--     simp [Bind.kleisliRight, iterate, bind]
--     sorry
--   naturality f g := sorry
--   codiagonal f := sorry
--   uniformity f g h H := sorry

end Traces?

namespace Traces

variable {ε τ} [Monoid ε] [MulAction ε τ] [StreamMulAction ε τ]

open MonadIterate

instance instMonadIterate : MonadIterate (Traces ε τ) where
  iterate f x := ⟨
    iterateTraces (λa => (f a).val) x,
    iterateTraces_nonempty (λa => (f a).prop) x
  ⟩

-- instance instElgotMonad : ElgotMonad (Traces ε τ) where
--   fixpoint f := by
--     ext x
--     apply NSet.ext
--     have h := (Traces?.instElgotMonad (ε := ε) (τ := τ)).fixpoint (λx => (f x).val)
--     have h := congrFun h x
--     apply Eq.trans _ h
--     apply Set.ext
--     intro t
--     simp [Bind.kleisliRight, bind]
--     apply exists_congr
--     intro t
--     simp
--     intro h
--     cases t <;> sorry
--   naturality f g := sorry
--   codiagonal f := sorry
--   uniformity f g h H := sorry

end Traces
