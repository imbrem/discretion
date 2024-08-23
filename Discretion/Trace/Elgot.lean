import Discretion.Trace.Basic
import Discretion.Elgot.Monad
import Discretion.Stream.Action
import Discretion.Utils.Set

open StreamProd

open Functor

namespace Trace

variable {step : α → Set (Trace ε τ (β ⊕ α))}

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

def leftResults (s : Set (Trace ε τ (α ⊕ β))) : Set (α × ε)
  := { (x, e) : α × ε | done (Sum.inl x) e ∈ s }

def rightResults (s : Set (Trace ε τ (α ⊕ β))) : Set (β × ε)
  := { (y, e) : β × ε | done (Sum.inr y) e ∈ s }

def doneResults (s : Set (Trace ε τ α)) : Set (α × ε)
  := { (x, e) : α × ε | done x e ∈ s }

theorem leftResults_union_rightResults {s : Set (Trace ε τ (α ⊕ β))}
  : (λ(a, e) => (Sum.inl a, e)) '' leftResults s
  ∪ (λ(b, e) => (Sum.inr b, e)) '' rightResults s = doneResults s
  := by
  ext ⟨x, e⟩
  cases x <;> simp [leftResults, rightResults, doneResults]

def divergentResults (s : Set (Trace ε τ α)) : Set τ
  := inf ⁻¹' s

theorem leftResults_union {s t : Set (Trace ε τ (α ⊕ β))}
  : leftResults (s ∪ t) = leftResults s ∪ leftResults t := rfl

theorem rightResults_union {s t : Set (Trace ε τ (α ⊕ β))}
  : rightResults (s ∪ t) = rightResults s ∪ rightResults t := rfl

theorem doneResults_union {s t : Set (Trace ε τ α)}
  : doneResults (s ∪ t) = doneResults s ∪ doneResults t := rfl

@[simp]
theorem doneResults_infiniteTraces [StreamProd ε τ] {step : α → Set (Trace ε τ (β ⊕ α))} {a : α}
  : doneResults (α := γ) (infiniteTraces step a) = ∅ := by simp [doneResults, infiniteTraces]

@[simp]
theorem divergentResults_map {f : α → β} {s : Set (Trace ε τ α)}
  : divergentResults (map f '' s) = divergentResults s
  := Set.ext (λt => ⟨λ⟨x, hx, ht⟩ => by cases x <;> cases ht; exact hx, λhx => ⟨inf t, hx, rfl⟩⟩)

theorem divergentResults_union {s t : Set (Trace ε τ α)}
  : divergentResults (s ∪ t) = divergentResults s ∪ divergentResults t
  := rfl

def leftTraces (s : Set (Trace ε τ (α ⊕ β))) : Set (Trace ε τ α)
  := (λ(b, e) => done b e) '' leftResults s

theorem leftTraces_union {s t : Set (Trace ε τ (α ⊕ β))}
  : leftTraces (s ∪ t) = leftTraces s ∪ leftTraces t
  := by simp [leftResults_union, leftTraces, Set.image_union]

@[simp]
theorem leftTraces_infiniteTraces [StreamProd ε τ]
  {step : α → Set (Trace ε τ (β ⊕ α))} {a : α}
  : leftTraces (infiniteTraces (γ := γ ⊕ δ) step a) = ∅
  := by simp [leftTraces, leftResults, infiniteTraces]

def rightTraces (s : Set (Trace ε τ (α ⊕ β))) : Set (Trace ε τ β)
  := (λ(c, e) => done c e) '' rightResults s

theorem rightTraces_union {s t : Set (Trace ε τ (α ⊕ β))}
  : rightTraces (s ∪ t) = rightTraces s ∪ rightTraces t
  := by simp [rightResults_union, rightTraces, Set.image_union]

@[simp]
theorem rightTraces_infiniteTraces [StreamProd ε τ]
  {step : α → Set (Trace ε τ (β ⊕ α))} {a : α}
  : rightTraces (infiniteTraces (γ := γ ⊕ δ) step a) = ∅
  := by simp [rightTraces, rightResults, infiniteTraces]

def doneTraces (s : Set (Trace ε τ α)) : Set (Trace ε τ α)
  := (λ(a, e) => done a e) '' doneResults s

theorem doneTraces_union {s t : Set (Trace ε τ α)}
  : doneTraces (s ∪ t) = doneTraces s ∪ doneTraces t
  := by simp [doneResults_union, doneTraces, Set.image_union]

-- theorem doneTraces_map {f : α → β} {s : Set (Trace ε τ α)}
--   : doneTraces (map f '' s) = map f '' doneTraces s
--   := sorry

def divergentTraces (s : Set (Trace ε τ α)) : Set (Trace ε τ β)
  := inf '' divergentResults s

@[simp]
theorem map_divergentTraces
  {f : β → γ} {s : Set (Trace ε τ α)}
  : map f '' divergentTraces s = divergentTraces s
  := Set.ext (λx => by cases x <;> simp [divergentTraces])

@[simp]
theorem divergentTraces_map {f : α → β} {s : Set (Trace ε τ α)}
  : divergentTraces (β := γ) (map f '' s) = divergentTraces (β := γ) s
  := Set.ext (λx => by cases x <;> simp [divergentTraces])

theorem divergentTraces_union {s t : Set (Trace ε τ α)}
  : divergentTraces (β := β) (s ∪ t) = divergentTraces s ∪ divergentTraces t
  := by simp [divergentResults_union, divergentTraces, Set.image_union]

@[simp]
theorem divergentTraces_infiniteTraces [StreamProd ε τ]
  {step : α → Set (Trace ε τ (β ⊕ α))} {a : α}
  : divergentTraces (α := γ) (β := γ') (infiniteTraces step a) = infiniteTraces step a
  := by ext x; simp [divergentTraces, divergentResults, infiniteTraces]

def mapLeftTraces (s : Set (Trace ε τ (α ⊕ β))) : Set (Trace ε τ α)
  := map Sum.inl ⁻¹' s

theorem leftTraces_subset_mapLeftTraces {s : Set (Trace ε τ (α ⊕ β))}
  : leftTraces s ⊆ mapLeftTraces s
  := λx ⟨(a, e), hy, ey⟩ => by cases ey; simp only [mapLeftTraces, Set.mem_preimage]; exact hy

theorem divergentTraces_subset_mapLeftTraces {s : Set (Trace ε τ (α ⊕ β))}
  : divergentTraces s ⊆ mapLeftTraces s
  := λx ⟨t, ht, et⟩ => by cases et; simp only [mapLeftTraces, Set.mem_preimage]; exact ht

def mapRightTraces (s : Set (Trace ε τ (α ⊕ β))) : Set (Trace ε τ β)
  := map Sum.inr ⁻¹' s

theorem rightTraces_subset_mapRightTraces {s : Set (Trace ε τ (α ⊕ β))}
  : rightTraces s ⊆ mapRightTraces s
  := λx ⟨(a, e), hy, ey⟩ => by cases ey; simp only [mapRightTraces, Set.mem_preimage]; exact hy

theorem divergentTraces_subset_mapRightTraces {s : Set (Trace ε τ (α ⊕ β))}
  : divergentTraces s ⊆ mapRightTraces s
  := λx ⟨t, ht, et⟩ => by cases et; simp only [mapRightTraces, Set.mem_preimage]; exact ht

theorem divergentTraces_union_leftTraces {s : Set (Trace ε τ (α ⊕ β))}
  : divergentTraces s ∪ leftTraces s = mapLeftTraces s
  := Set.Subset.antisymm
    (Set.union_subset divergentTraces_subset_mapLeftTraces leftTraces_subset_mapLeftTraces)
    (λx => by cases x <;>
      simp [mapLeftTraces, divergentTraces, leftTraces, leftResults, divergentResults])

@[simp]
theorem mapLeftTraces_infiniteTraces [StreamProd ε τ]
  {step : α → Set (Trace ε τ (β ⊕ α))} {a : α}
  : mapLeftTraces (infiniteTraces (γ := γ ⊕ δ) step a) = infiniteTraces step a
  := by simp [<-divergentTraces_union_leftTraces]

theorem divergentTraces_union_rightTraces {s : Set (Trace ε τ (α ⊕ β))}
  : divergentTraces s ∪ rightTraces s = mapRightTraces s
  := Set.Subset.antisymm
    (Set.union_subset divergentTraces_subset_mapRightTraces rightTraces_subset_mapRightTraces)
    (λx => by cases x <;>
      simp [mapRightTraces, divergentTraces, rightTraces, rightResults, divergentResults])

@[simp]
theorem mapRightTraces_infiniteTraces [StreamProd ε τ]
  {step : α → Set (Trace ε τ (β ⊕ α))} {a : α}
  : mapRightTraces (infiniteTraces (γ := γ ⊕ δ) step a) = infiniteTraces step a
  := by simp [<-divergentTraces_union_rightTraces]

@[simp]
theorem inl_mapLeftTraces {s : Set (Trace ε τ (α ⊕ β))}
  : map Sum.inl '' mapLeftTraces s ⊆ s := by simp [mapLeftTraces]

@[simp]
theorem inr_mapRightTraces {s : Set (Trace ε τ (α ⊕ β))}
  : map Sum.inr '' mapRightTraces s ⊆ s := by simp [mapRightTraces]

-- theorem divergentTraces_union_traces {s : Set (Trace ε τ α)}
--   : divergentTraces s ∪ doneTraces s = s
--   := sorry

-- theorem inl_leftTraces_union_inr_rightTraces {s : Set (Trace ε τ (α ⊕ β))}
--   : (map Sum.inl '' leftTraces s) ∪ (map Sum.inr '' rightTraces s) = doneTraces s
--   := sorry

theorem mapLeftTraces_union_mapRightTraces {s : Set (Trace ε τ (α ⊕ β))}
  : (map (Sum.inl (β := β)) '' mapLeftTraces s) ∪ (map Sum.inr '' mapRightTraces s) = s
  := Set.Subset.antisymm
    (Set.union_subset inl_mapLeftTraces inr_mapRightTraces)
    (λx hx => by
      cases x with
      | done x e =>
        cases x with
        | inl x =>
          apply Set.subset_union_left
          exact ⟨done x e, hx, rfl⟩
        | inr x =>
          apply Set.subset_union_right
          exact ⟨done x e, hx, rfl⟩
      | inf t =>
        rw [<-divergentTraces_union_leftTraces, Set.image_union, map_divergentTraces]
        apply Set.subset_union_left
        apply Set.subset_union_left
        exact ⟨t, hx, rfl⟩
    )

theorem leftTraces_intersect_rightTraces
  {α β : Type u} {ε : Type ue} {τ : Type ut}
  {s : Set (Trace ε τ (α ⊕ β))}
  : (map (Sum.inl (β := β)) '' leftTraces s) ∩ (map Sum.inr '' rightTraces s) = ∅
  := Set.ext (λx => by
    simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
    intro ⟨y, ⟨(_, _), _, et⟩, ey⟩
    cases ey
    cases et
    simp only [map_done, Set.mem_image, not_exists, not_and, ne_eq]
    intro x ⟨y, _, ey⟩
    cases ey
    simp
  )

theorem leftTraces_disjoint_rightTraces
  {s : Set (Trace ε τ (α ⊕ β))} :
  Disjoint (map (Sum.inl (β := β)) '' leftTraces s) (map Sum.inr '' rightTraces s)
  := Set.disjoint_iff_inter_eq_empty.mpr leftTraces_intersect_rightTraces

theorem mapLeftTraces_intersect_mapRightTraces
  {α β : Type u} {ε : Type ue} {τ : Type ut} {s : Set (Trace ε τ (α ⊕ β))}
  : (map (Sum.inl (β := β)) '' mapLeftTraces s) ∩ (map Sum.inr '' mapRightTraces s)
  = divergentTraces s
  := by simp [
    <-divergentTraces_union_leftTraces, <-divergentTraces_union_rightTraces,
    Set.image_union, map_divergentTraces, <-Set.union_inter_distrib_left,
    leftTraces_intersect_rightTraces (α := α) (β := β) (s := s)
  ]

def IsLeft : Trace ε τ (α ⊕ β) → Prop
  | done (Sum.inl _) _ => True
  | _ => False

def IsRight : Trace ε τ (α ⊕ β) → Prop
  | done (Sum.inr _) _ => True
  | _ => False

def Diverges : Trace ε τ α → Prop
  | inf _ => True
  | _ => False

theorem iUnion_rightResults_effectStreams
  : ⋃ r ∈ rightResults (step a) , Stream'.cons r.2 '' effectStreams step r.1
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
  : ⋃ r ∈ rightResults (step a) , Stream'.cons r.1 '' actionStreams step r.1
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
  : ⋃ r ∈ rightResults (step a) , (r.2 • ·) '' infiniteResults step r.1 = infiniteResults step a
  := calc
  _ = streamProd '' ⋃ r ∈ rightResults (step a) , Stream'.cons r.2 '' effectStreams step r.1
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
  | 0 => mapLeftTraces (step a)
  | n + 1 => ⋃ r ∈ rightResults (step a), (r.2 • ·) '' approxFiniteTraces step r.1 n

def finiteTraces (step : α → Set (Trace ε τ (β ⊕ α))) (a : α) : Set (Trace ε τ β)
  := ⋃ n, approxFiniteTraces step a n

theorem mapLeftTraces_subset_finiteTraces
  : mapLeftTraces (step a) ⊆ finiteTraces step a
  := by intro t ht; simp only [finiteTraces, Set.mem_iUnion]; exact ⟨0, ht⟩

theorem mapLeftTraces_empty_of_finiteTraces_empty (h : finiteTraces step a = ∅)
  : mapLeftTraces (step a) = ∅ := Set.subset_eq_empty mapLeftTraces_subset_finiteTraces h

def iterateTraces [StreamProd ε τ] (step : α → Set (Trace ε τ (β ⊕ α))) (a : α)
  : Set (Trace ε τ β) := finiteTraces step a ∪ infiniteTraces step a

theorem mapLeftTraces_union_iUnion_rightResults_finiteTraces
  : mapLeftTraces (step a) ∪ ⋃ r ∈ rightResults (step a) , (r.2 • ·) '' finiteTraces step r.1
  = finiteTraces step a := calc
  _ = approxFiniteTraces step a 0 ∪
      ⋃ r ∈ rightResults (step a) , ⋃n, (r.2 • ·) '' approxFiniteTraces step r.1 n
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
  (h : finiteTraces step a = ∅) : ∀ r ∈ rightResults (step a) , finiteTraces step r.1 = ∅ := by
  rw [<-mapLeftTraces_union_iUnion_rightResults_finiteTraces] at h
  simp only [Set.union_empty_iff, Set.iUnion_eq_empty, Set.image_eq_empty, Prod.forall] at h
  intro (a, e) hr
  apply h.2 a e hr

noncomputable def choose_action_finiteTrace_empty
  (hstep : ∀a, Set.Nonempty (step a)) (a) (hfin : finiteTraces step a = ∅) : Stream' α
  := λn =>
    have h : ∃r : α × ε, r ∈ rightResults (step a) := by
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
    have h : ∃r : α × ε, r ∈ rightResults (step a) := by
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
  : ⋃ r ∈ rightResults (step a) , (r.2 • ·) '' infiniteTraces step r.1
  = infiniteTraces (γ := γ) step a
  := calc
  _ = inf '' ⋃ r ∈ rightResults (step a) , (r.2 • ·) '' infiniteResults step r.1
    := by simp [Set.image_iUnion, Set.image_image, infiniteTraces, StreamMulAction.streamProd_cons]
  _ = _
    := by rw [infiniteTraces, iUnion_rightResults_infiniteResults]

theorem mapLeftTraces_union_iUnion_rightResults_iterateTraces
  : mapLeftTraces (step a) ∪ ⋃ r ∈ rightResults (step a) , (r.2 • ·) '' iterateTraces step r.1
  = iterateTraces step a := calc
  _ = mapLeftTraces (step a)
    ∪ (⋃ r ∈ rightResults (step a) , (r.2 • ·) '' finiteTraces step r.1)
    ∪ (⋃ r ∈ rightResults (step a) , (r.2 • ·) '' infiniteTraces step r.1)
    := by
      simp only [iterateTraces, Set.image_union, Set.union_assoc, <-Set.iUnion_union_distrib]
      rfl
  _ = _
    := by
    rw [mapLeftTraces_union_iUnion_rightResults_finiteTraces, iUnion_rightResults_infiniteTraces]
    rfl

end Ops

section Elgot

variable [Monoid ε] [MulAction ε τ] [StreamMulAction ε τ]

theorem fixpoint_apply {x : α} {step : α → Set (Trace ε τ (β ⊕ α))}
  : divergentTraces (step x) ∪ ⋃ r ∈ doneResults (step x),
    (r.2 • ·) '' Sum.elim (λb => {done b 1}) (λx => iterateTraces step x) r.1
  = iterateTraces step x
  := by
  apply Eq.trans _ mapLeftTraces_union_iUnion_rightResults_iterateTraces
  rw [<-divergentTraces_union_leftTraces, Set.union_assoc]
  apply congrArg
  rw [<-leftResults_union_rightResults]
  simp only [
    Set.biUnion_union, leftTraces, rightTraces, Set.image_eq_iUnion, Set.biUnion_iUnion,
    Set.biUnion_singleton
  ]
  congr
  apply congrArg
  funext (x, e)
  apply congrArg
  funext _
  apply Set.ext
  simp [HSMul.hSMul, SMul.smul, Iff.intro Eq.symm Eq.symm]

end Elgot

end Trace

-- namespace Trace

-- variable {ε τ} [Monoid ε] [MulAction ε τ]

-- noncomputable instance instMonadIterate : MonadIterate (Trace ε τ) where
--   iterate f x := ⟨sorry, sorry⟩

-- end Trace

open Trace

namespace Traces?

section Iterate

variable {ε : Type u} {τ : Type v} [Monoid ε] [SMul ε τ]

open MonadIterate

theorem divergentTraces_subset_bind {x : Traces? ε τ α} {f : α → Traces? ε τ β}
  : divergentTraces x ⊆ (x >>= f : Traces? ε τ β) := by
  intro tm ⟨t, ht, et⟩
  cases et
  simp only [divergentResults, Set.mem_preimage] at ht
  simp only [bind, Set.pure_def, Set.bind_def, Set.mem_iUnion, exists_prop]
  exact ⟨inf t, ht, by simp⟩

theorem doneResults_subset_bind {x : Traces? ε τ α} {f : α → Traces? ε τ β}
  {a : α} {e : ε} : (a, e) ∈ doneResults x → e • f a ⊆ x >>= f := by
  simp only [doneResults, Set.mem_setOf_eq]
  intro hx t ht
  simp only [bind, Set.pure_def, Set.bind_def, Set.mem_iUnion, exists_prop]
  exact ⟨done a e, hx, ht⟩

theorem bind_eq {x : Traces? ε τ α} {f : α → Traces? ε τ β}
  : x >>= f = divergentTraces x ∪ ⋃ r ∈ doneResults x, r.2 • f r.1
  := Set.Subset.antisymm
    (by
      simp only [bind, Set.pure_def, Set.bind_def, Set.iUnion_subset_iff]
      intro t ht
      cases t with
      | done a e =>
        simp only
        apply Set.subset_union_of_subset_right
        apply Set.subset_iUnion_of_subset (a, e)
        simp [doneResults, ht]
      | inf t => simp [divergentTraces, divergentResults, ht]
    )
    (Set.union_subset divergentTraces_subset_bind (by
      simp only [Set.iUnion_subset_iff, Prod.forall]
      intro a e; apply doneResults_subset_bind
    ))

theorem kleisli_apply_eq (f : α → Traces? ε τ β) (g : β → Traces? ε τ γ) (a : α)
  : (f >=> g) a
  = divergentTraces (f a) ∪ ⋃ r ∈ doneResults (f a), r.2 • g r.1
  := by rw [Bind.kleisliRight, bind_eq]

variable [StreamProd ε τ]

instance instMonadIterate : MonadIterate.{w, max u v w} (Traces? ε τ) where
  iterate f x := iterateTraces f x

def finiteIterate (f : α → Traces? ε τ (β ⊕ α)) (a : α) : Traces? ε τ β
  := finiteTraces f a

def infiniteIterate (f : α → Traces? ε τ (β ⊕ α)) (a : α) : Traces? ε τ β
  := infiniteTraces f a

end Iterate

section Elgot

open MonadIterate

variable {ε : Type u} {τ : Type v} [Monoid ε] [MulAction ε τ] [StreamMulAction ε τ]

-- theorem finiteTraces_naturality {f : α → Traces? ε τ (β ⊕ α)} {g : β → Traces? ε τ γ} {a : α}
--   : finiteTraces (f >=> sumM g pure : α → Traces? ε τ (γ ⊕ α)) a
--   = ((finiteTraces f a : Traces? ε τ β) >>= g : Traces? ε τ γ)
--   := sorry

-- theorem _root_.Trace.IsEffectStream.naturality
--   {f : α → Traces? ε τ (β ⊕ α)} {g : β → Traces? ε τ γ} {as : Stream' α} {es : Stream' ε}
--   : IsEffectStream (f >=> sumM g pure : α → Traces? ε τ _) as es ↔ IsEffectStream f as es
--   := sorry

-- theorem effectStreams_naturality {f : α → Traces? ε τ (β ⊕ α)} {g : β → Traces? ε τ γ} {a : α}
--   : effectStreams (f >=> sumM g pure : α → Traces? ε τ (γ ⊕ α)) a = effectStreams f a
--   := by
--   ext es
--   simp only [
--     effectStreams, Set.mem_setOf_eq, Bind.kleisliRight,
--     _root_.Trace.IsEffectStream.naturality
--   ]
--   apply exists_congr
--   intro as
--   apply and_congr _ Iff.rfl
--   simp only [bind_eq, divergentTraces, divergentResults, Set.mem_union, Set.mem_image,
--     Set.mem_preimage, and_false, exists_false, exists_prop, Prod.exists, Sum.exists,
--     false_or]
--   constructor
--   · intro ⟨t, ⟨⟨(x, e), et⟩, htr'⟩⟩
--     simp only [doneResults, Set.mem_setOf_eq] at et
--     cases et
--     let ⟨w, ⟨hw', ew⟩, hw⟩ := htr'
--     simp only at ew
--     cases ew
--     simp only [HSMul.hSMul, SMul.smul, sumM, pure, Set.pure_def, Sum.elim_inl,
--       Function.comp_apply, Set.fmap_eq_image, Set.mem_image] at hw
--     let ⟨y, hy, ey⟩ := hw;
--     cases y with
--     | done y e' =>
--       simp only [done.injEq] at ey
--       have ⟨ey, ee⟩ := ey;
--       cases ey
--       cases x with
--       | inl x =>
--         simp only [map, Set.fmap_eq_image, Sum.elim_inl, Function.comp_apply, Set.mem_image] at hy
--         let ⟨x, hx, hx'⟩ := hy
--         cases x <;> simp at hx'
--       | inr x =>
--         simp only [map, Set.fmap_eq_image, Sum.elim_inr, Function.comp_apply, Set.image_singleton,
--           Set.mem_singleton_iff, done.injEq, Sum.inr.injEq] at hy
--         let ⟨hx, he'⟩ := hy;
--         cases he'
--         cases hx
--         rw [<-ee]
--         simp [hw']
--     | inf t => cases ey
--   · intro hx
--     exact ⟨_, ⟨(Sum.inr (as 0), es 0), rfl⟩, by
--       simp only [doneResults, Set.mem_setOf_eq, hx, HSMul.hSMul, SMul.smul, Set.fmap_eq_image,
--         Set.iUnion_true, Set.mem_image]
--       exact ⟨done (Sum.inr (as 0)) 1, by simp [sumM, pure, map], by simp⟩
--     ⟩

-- theorem infiniteResults_naturality {f : α → Traces? ε τ (β ⊕ α)} {g : β → Traces? ε τ γ} {a : α}
--   : infiniteResults (f >=> sumM g pure : α → Traces? ε τ (γ ⊕ α)) a = infiniteResults f a
--   := by simp [infiniteResults, effectStreams_naturality]

-- theorem infiniteTraces_naturality {f : α → Traces? ε τ (β ⊕ α)} {g : β → Traces? ε τ γ} {a : α}
--   : infiniteTraces (γ := δ) (f >=> sumM g pure : α → Traces? ε τ (γ ⊕ α)) a = infiniteTraces f a
--   := by simp [infiniteTraces, infiniteResults_naturality]

-- instance instElgotMonad : ElgotMonad (Traces? ε τ) where
--   fixpoint f := by
--     ext x
--     simp only [iterate, kleisli_apply_eq]
--     apply Eq.trans _ fixpoint_apply
--     apply congrArg
--     apply congrArg
--     funext ⟨r, e⟩
--     apply congrArg
--     funext h
--     cases r <;> simp [pure, HSMul.hSMul, SMul.smul]
--   naturality f g := by
--     ext x
--     simp only [iterate, iterateTraces, kleisli_apply_eq, divergentTraces_union,
--       divergentTraces_infiniteTraces, doneResults_union, doneResults_infiniteTraces,
--       Set.union_empty]
--     conv => lhs; lhs; rw [Set.union_comm]
--     rw [
--       Set.union_assoc, <-bind_eq, finiteTraces_naturality, Set.union_comm, infiniteTraces_naturality
--     ]
--   codiagonal f := sorry
--   uniformity f g h H := sorry

end Elgot

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
