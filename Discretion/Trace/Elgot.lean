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

@[simp]
theorem divergentResults_map_inf {s : Set τ}
  : divergentResults (inf (ε := ε) (α := α) '' s) = s
  := Set.preimage_image_eq _ (λt => by simp)

theorem leftResults_mono {s t : Set (Trace ε τ (α ⊕ β))}
  (h : s ⊆ t) : leftResults s ⊆ leftResults t
  := Set.preimage_mono h

theorem rightResults_mono {s t : Set (Trace ε τ (α ⊕ β))}
  (h : s ⊆ t) : rightResults s ⊆ rightResults t
  := Set.preimage_mono h

theorem doneResults_mono {s t : Set (Trace ε τ α)}
  (h : s ⊆ t) : doneResults s ⊆ doneResults t
  := Set.preimage_mono h

theorem divergentResults_mono {s t : Set (Trace ε τ α)}
  (h : s ⊆ t) : divergentResults s ⊆ divergentResults t
  := Set.preimage_mono h

theorem leftResults_iUnion {s : ι → Set (Trace ε τ (α ⊕ β))}
  : leftResults (Set.iUnion s) = ⋃ i, leftResults (s i)
  := Set.preimage_iUnion

theorem rightResults_iUnion {s : ι → Set (Trace ε τ (α ⊕ β))}
  : rightResults (Set.iUnion s) = ⋃ i, rightResults (s i)
  := Set.preimage_iUnion

theorem doneResults_iUnion {s : ι → Set (Trace ε τ α)}
  : doneResults (Set.iUnion s) = ⋃ i, doneResults (s i)
  := Set.preimage_iUnion

theorem divergentResults_iUnion {s : ι → Set (Trace ε τ α)}
  : divergentResults (Set.iUnion s) = ⋃ i, divergentResults (s i)
  := Set.preimage_iUnion

def leftTraces (s : Set (Trace ε τ (α ⊕ β))) : Set (Trace ε τ α)
  := (λ(b, e) => done b e) '' leftResults s

theorem leftTraces_mono {s t : Set (Trace ε τ (α ⊕ β))}
  (h : s ⊆ t) : leftTraces s ⊆ leftTraces t
  := Set.image_mono (leftResults_mono h)

theorem leftTraces_union {s t : Set (Trace ε τ (α ⊕ β))}
  : leftTraces (s ∪ t) = leftTraces s ∪ leftTraces t
  := by simp [leftResults_union, leftTraces, Set.image_union]

theorem leftTraces_iUnion {s : ι → Set (Trace ε τ (α ⊕ β))}
  : leftTraces (Set.iUnion s) = ⋃ i, leftTraces (s i)
  := by simp [leftResults_iUnion, leftTraces, Set.image_iUnion]

@[simp]
theorem leftTraces_infiniteTraces [StreamProd ε τ]
  {step : α → Set (Trace ε τ (β ⊕ α))} {a : α}
  : leftTraces (infiniteTraces (γ := γ ⊕ δ) step a) = ∅
  := by simp [leftTraces, leftResults, infiniteTraces]

@[simp]
theorem doneResults_leftTraces {s : Set (Trace ε τ (α ⊕ β))}
  : doneResults (leftTraces s) = leftResults s := by simp [doneResults, leftTraces]

def rightTraces (s : Set (Trace ε τ (α ⊕ β))) : Set (Trace ε τ β)
  := (λ(c, e) => done c e) '' rightResults s

theorem rightTraces_mono {s t : Set (Trace ε τ (α ⊕ β))}
  (h : s ⊆ t) : rightTraces s ⊆ rightTraces t
  := Set.image_mono (rightResults_mono h)

theorem rightTraces_union {s t : Set (Trace ε τ (α ⊕ β))}
  : rightTraces (s ∪ t) = rightTraces s ∪ rightTraces t
  := by simp [rightResults_union, rightTraces, Set.image_union]

theorem rightTraces_iUnion {s : ι → Set (Trace ε τ (α ⊕ β))}
  : rightTraces (Set.iUnion s) = ⋃ i, rightTraces (s i)
  := by simp [rightResults_iUnion, rightTraces, Set.image_iUnion]

@[simp]
theorem rightTraces_infiniteTraces [StreamProd ε τ]
  {step : α → Set (Trace ε τ (β ⊕ α))} {a : α}
  : rightTraces (infiniteTraces (γ := γ ⊕ δ) step a) = ∅
  := by simp [rightTraces, rightResults, infiniteTraces]

@[simp]
theorem doneResults_rightTraces {s : Set (Trace ε τ (α ⊕ β))}
  : doneResults (rightTraces s) = rightResults s := by simp [doneResults, rightTraces]

def doneTraces (s : Set (Trace ε τ α)) : Set (Trace ε τ α)
  := (λ(a, e) => done a e) '' doneResults s

theorem doneTraces_mono {s t : Set (Trace ε τ α)}
  (h : s ⊆ t) : doneTraces s ⊆ doneTraces t
  := Set.image_mono (doneResults_mono h)

@[simp]
theorem doneResults_doneTraces {s : Set (Trace ε τ α)}
  : doneResults (doneTraces s) = doneResults s := by simp [doneResults, doneTraces]

@[simp]
theorem doneTraces_doneTraces {s : Set (Trace ε τ α)}
  : doneTraces (doneTraces s) = doneTraces s := by simp [doneTraces, doneResults]

@[simp]
theorem doneTraces_leftTraces {s : Set (Trace ε τ (α ⊕ β))}
  : doneTraces (leftTraces s) = leftTraces s := by simp [doneTraces, leftTraces, doneResults]

@[simp]
theorem leftTraces_doneTraces {s : Set (Trace ε τ (α ⊕ β))}
  : leftTraces (doneTraces s) = leftTraces s
  := by simp [doneTraces, leftTraces, doneResults, leftResults]

@[simp]
theorem doneTraces_rightTraces {s : Set (Trace ε τ (α ⊕ β))}
  : doneTraces (rightTraces s) = rightTraces s := by simp [doneTraces, rightTraces, doneResults]

@[simp]
theorem rightTraces_doneTraces {s : Set (Trace ε τ (α ⊕ β))}
  : rightTraces (doneTraces s) = rightTraces s
  := by simp [doneTraces, rightTraces, doneResults, rightResults]

theorem doneTraces_union {s t : Set (Trace ε τ α)}
  : doneTraces (s ∪ t) = doneTraces s ∪ doneTraces t
  := by simp [doneResults_union, doneTraces, Set.image_union]

theorem doneTraces_iUnion {s : ι → Set (Trace ε τ α)}
  : doneTraces (Set.iUnion s) = ⋃ i, doneTraces (s i)
  := by simp [doneResults_iUnion, doneTraces, Set.image_iUnion]

-- theorem doneTraces_map {f : α → β} {s : Set (Trace ε τ α)}
--   : doneTraces (map f '' s) = map f '' doneTraces s
--   := sorry

def divergentTraces (s : Set (Trace ε τ α)) : Set (Trace ε τ β)
  := inf '' divergentResults s

theorem divergentTraces_mono {s t : Set (Trace ε τ α)}
  (h : s ⊆ t) : divergentTraces (β := β) s ⊆ divergentTraces t
  := Set.image_mono (divergentResults_mono h)

theorem divergentTraces_iUnion {s : ι → Set (Trace ε τ α)}
  : divergentTraces (β := β) (Set.iUnion s) = ⋃ i, divergentTraces (s i)
  := by simp [divergentResults_iUnion, divergentTraces, Set.image_iUnion]

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
theorem divergentTraces_divergentTraces {s : Set (Trace ε τ α)}
  : divergentTraces (β := γ) (divergentTraces (β := β) s) = divergentTraces s
  := by simp [divergentTraces]

@[simp]
theorem divergentTraces_leftTraces {s : Set (Trace ε τ (α ⊕ β))}
  : divergentTraces (β := γ) (leftTraces s) = ∅ := by
  ext k
  simp [divergentTraces, leftTraces, divergentResults, leftResults]

@[simp]
theorem divergentTraces_rightTraces {s : Set (Trace ε τ (α ⊕ β))}
  : divergentTraces (β := γ) (rightTraces s) = ∅ := by
  ext k
  simp [divergentTraces, rightTraces, divergentResults, rightResults]

@[simp]
theorem divergentTraces_doneTraces {s : Set (Trace ε τ α)}
  : divergentTraces (β := γ) (doneTraces s) = ∅ := by
  ext k
  simp [divergentTraces, doneTraces, divergentResults, doneResults]

@[simp]
theorem doneResults_divergentTraces {s : Set (Trace ε τ α)}
  : doneResults (divergentTraces (β := β) s) = ∅ := by
  ext k
  simp [doneResults, divergentTraces, doneResults, divergentResults]

@[simp]
theorem doneTraces_divergentTraces {s : Set (Trace ε τ α)}
  : doneTraces (divergentTraces (β := β) s) = ∅ := by
  ext k
  simp [doneTraces, divergentTraces, doneResults, divergentResults]

@[simp]
theorem leftResults_divergentTraces {s : Set (Trace ε τ α)}
  : leftResults (divergentTraces (β := β ⊕ γ) s) = ∅ := by
  ext k
  simp [leftResults, divergentTraces, leftResults, divergentResults]

@[simp]
theorem leftTraces_divergentTraces {s : Set (Trace ε τ α)}
  : leftTraces (divergentTraces (β := β ⊕ γ) s) = ∅ := by
  ext k
  simp [leftTraces, divergentTraces, leftResults, divergentResults]

@[simp]
theorem rightResults_divergentTraces {s : Set (Trace ε τ α)}
  : rightResults (divergentTraces (β := β ⊕ γ) s) = ∅ := by
  ext k
  simp [rightResults, divergentTraces, rightResults, divergentResults]

@[simp]
theorem rightTraces_divergentTraces {s : Set (Trace ε τ α)}
  : rightTraces (divergentTraces (β := β ⊕ γ) s) = ∅ := by
  ext k
  simp [rightTraces, divergentTraces, rightResults, divergentResults]

@[simp]
theorem divergentTraces_infiniteTraces [StreamProd ε τ]
  {step : α → Set (Trace ε τ (β ⊕ α))} {a : α}
  : divergentTraces (α := γ) (β := γ') (infiniteTraces step a) = infiniteTraces step a
  := by ext x; simp [divergentTraces, divergentResults, infiniteTraces]

def leftTraces? (s : Set (Trace ε τ (α ⊕ β))) : Set (Trace ε τ α)
  := map Sum.inl ⁻¹' s

theorem leftTraces_subset_leftTraces? {s : Set (Trace ε τ (α ⊕ β))}
  : leftTraces s ⊆ leftTraces? s
  := λx ⟨(a, e), hy, ey⟩ => by cases ey; simp only [leftTraces?, Set.mem_preimage]; exact hy

theorem divergentTraces_subset_leftTraces? {s : Set (Trace ε τ (α ⊕ β))}
  : divergentTraces s ⊆ leftTraces? s
  := λx ⟨t, ht, et⟩ => by cases et; simp only [leftTraces?, Set.mem_preimage]; exact ht

def rightTraces? (s : Set (Trace ε τ (α ⊕ β))) : Set (Trace ε τ β)
  := map Sum.inr ⁻¹' s

theorem rightTraces_subset_rightTraces? {s : Set (Trace ε τ (α ⊕ β))}
  : rightTraces s ⊆ rightTraces? s
  := λx ⟨(a, e), hy, ey⟩ => by cases ey; simp only [rightTraces?, Set.mem_preimage]; exact hy

theorem divergentTraces_subset_rightTraces? {s : Set (Trace ε τ (α ⊕ β))}
  : divergentTraces s ⊆ rightTraces? s
  := λx ⟨t, ht, et⟩ => by cases et; simp only [rightTraces?, Set.mem_preimage]; exact ht

theorem divergentTraces_union_leftTraces {s : Set (Trace ε τ (α ⊕ β))}
  : divergentTraces s ∪ leftTraces s = leftTraces? s
  := Set.Subset.antisymm
    (Set.union_subset divergentTraces_subset_leftTraces? leftTraces_subset_leftTraces?)
    (λx => by cases x <;>
      simp [leftTraces?, divergentTraces, leftTraces, leftResults, divergentResults])

@[simp]
theorem leftTraces?_infiniteTraces [StreamProd ε τ]
  {step : α → Set (Trace ε τ (β ⊕ α))} {a : α}
  : leftTraces? (infiniteTraces (γ := γ ⊕ δ) step a) = infiniteTraces step a
  := by simp [<-divergentTraces_union_leftTraces]

theorem divergentTraces_union_rightTraces {s : Set (Trace ε τ (α ⊕ β))}
  : divergentTraces s ∪ rightTraces s = rightTraces? s
  := Set.Subset.antisymm
    (Set.union_subset divergentTraces_subset_rightTraces? rightTraces_subset_rightTraces?)
    (λx => by cases x <;>
      simp [rightTraces?, divergentTraces, rightTraces, rightResults, divergentResults])

@[simp]
theorem divergentTraces_leftTraces? {s : Set (Trace ε τ (α ⊕ β))}
  : divergentTraces (β := γ) (leftTraces? s) = divergentTraces s
  := by simp [<-divergentTraces_union_leftTraces, divergentTraces_union]

@[simp]
theorem divergentTraces_rightTraces? {s : Set (Trace ε τ (α ⊕ β))}
  : divergentTraces (β := γ) (rightTraces? s) = divergentTraces s
  := by simp [<-divergentTraces_union_rightTraces, divergentTraces_union]

@[simp]
theorem doneResults_leftTraces? {s : Set (Trace ε τ (α ⊕ β))}
  : doneResults (leftTraces? s) = leftResults s
  := by simp [<-divergentTraces_union_leftTraces, doneResults_union]

@[simp]
theorem doneTraces_leftTraces? {s : Set (Trace ε τ (α ⊕ β))}
  : doneTraces (leftTraces? s) = leftTraces s
  := by simp [<-divergentTraces_union_leftTraces, doneTraces_union]

@[simp]
theorem doneResults_rightTraces? {s : Set (Trace ε τ (α ⊕ β))}
  : doneResults (rightTraces? s) = rightResults s
  := by simp [<-divergentTraces_union_rightTraces, doneResults_union]

@[simp]
theorem doneTraces_rightTraces? {s : Set (Trace ε τ (α ⊕ β))}
  : doneTraces (rightTraces? s) = rightTraces s
  := by simp [<-divergentTraces_union_rightTraces, doneTraces_union]

@[simp]
theorem rightTraces?_infiniteTraces [StreamProd ε τ]
  {step : α → Set (Trace ε τ (β ⊕ α))} {a : α}
  : rightTraces? (infiniteTraces (γ := γ ⊕ δ) step a) = infiniteTraces step a
  := by simp [<-divergentTraces_union_rightTraces]

@[simp]
theorem inl_leftTraces? {s : Set (Trace ε τ (α ⊕ β))}
  : map Sum.inl '' leftTraces? s ⊆ s := by simp [leftTraces?]

@[simp]
theorem inr_rightTraces? {s : Set (Trace ε τ (α ⊕ β))}
  : map Sum.inr '' rightTraces? s ⊆ s := by simp [rightTraces?]

theorem leftTraces?_mono {s t : Set (Trace ε τ (α ⊕ β))}
  (h : s ⊆ t) : leftTraces? s ⊆ leftTraces? t
  := Set.preimage_mono h

theorem rightTraces?_mono {s t : Set (Trace ε τ (α ⊕ β))}
  (h : s ⊆ t) : rightTraces? s ⊆ rightTraces? t
  := Set.preimage_mono h

theorem leftTraces?_iUnion {s : ι → Set (Trace ε τ (α ⊕ β))}
  : leftTraces? (Set.iUnion s) = ⋃ i, leftTraces? (s i)
  := Set.preimage_iUnion

theorem rightTraces?_iUnion {s : ι → Set (Trace ε τ (α ⊕ β))}
  : rightTraces? (Set.iUnion s) = ⋃ i, rightTraces? (s i)
  := Set.preimage_iUnion

-- theorem divergentTraces_union_traces {s : Set (Trace ε τ α)}
--   : divergentTraces s ∪ doneTraces s = s
--   := sorry

-- theorem inl_leftTraces_union_inr_rightTraces {s : Set (Trace ε τ (α ⊕ β))}
--   : (map Sum.inl '' leftTraces s) ∪ (map Sum.inr '' rightTraces s) = doneTraces s
--   := sorry

theorem leftTraces?_union_rightTraces? {s : Set (Trace ε τ (α ⊕ β))}
  : (map (Sum.inl (β := β)) '' leftTraces? s) ∪ (map Sum.inr '' rightTraces? s) = s
  := Set.Subset.antisymm
    (Set.union_subset inl_leftTraces? inr_rightTraces?)
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

theorem leftTraces?_intersect_rightTraces?
  {α β : Type u} {ε : Type ue} {τ : Type ut} {s : Set (Trace ε τ (α ⊕ β))}
  : (map (Sum.inl (β := β)) '' leftTraces? s) ∩ (map Sum.inr '' rightTraces? s)
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
  | 0 => leftTraces? (step a)
  | n + 1 => ⋃ r ∈ rightResults (step a), (r.2 • ·) '' approxFiniteTraces step r.1 n

def finiteTraces (step : α → Set (Trace ε τ (β ⊕ α))) (a : α) : Set (Trace ε τ β)
  := ⋃ n, approxFiniteTraces step a n

theorem leftTraces?_subset_finiteTraces
  : leftTraces? (step a) ⊆ finiteTraces step a
  := by intro t ht; simp only [finiteTraces, Set.mem_iUnion]; exact ⟨0, ht⟩

theorem leftTraces?_empty_of_finiteTraces_empty (h : finiteTraces step a = ∅)
  : leftTraces? (step a) = ∅ := Set.subset_eq_empty leftTraces?_subset_finiteTraces h

def iterateTraces [StreamProd ε τ] (step : α → Set (Trace ε τ (β ⊕ α))) (a : α)
  : Set (Trace ε τ β) := finiteTraces step a ∪ infiniteTraces step a

theorem leftTraces?_union_iUnion_rightResults_finiteTraces
  : leftTraces? (step a) ∪ ⋃ r ∈ rightResults (step a) , (r.2 • ·) '' finiteTraces step r.1
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
  rw [<-leftTraces?_union_iUnion_rightResults_finiteTraces] at h
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
          exact ⟨done b e, leftTraces?_subset_finiteTraces ht⟩
        | inr a => exact ⟨(a, e), ht⟩
      | inf t =>
        apply False.elim (Set.Nonempty.ne_empty _ hfin)
        exact ⟨inf t, leftTraces?_subset_finiteTraces ht⟩;
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
          exact ⟨done b e, leftTraces?_subset_finiteTraces ht⟩
        | inr a => exact ⟨(a, e), ht⟩
      | inf t =>
        apply False.elim (Set.Nonempty.ne_empty _ hfin)
        exact ⟨inf t, leftTraces?_subset_finiteTraces ht⟩;
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

theorem leftTraces?_union_iUnion_rightResults_iterateTraces
  : leftTraces? (step a) ∪ ⋃ r ∈ rightResults (step a) , (r.2 • ·) '' iterateTraces step r.1
  = iterateTraces step a := calc
  _ = leftTraces? (step a)
    ∪ (⋃ r ∈ rightResults (step a) , (r.2 • ·) '' finiteTraces step r.1)
    ∪ (⋃ r ∈ rightResults (step a) , (r.2 • ·) '' infiniteTraces step r.1)
    := by
      simp only [iterateTraces, Set.image_union, Set.union_assoc, <-Set.iUnion_union_distrib]
      rfl
  _ = _
    := by
    rw [leftTraces?_union_iUnion_rightResults_finiteTraces, iUnion_rightResults_infiniteTraces]
    rfl

end Ops

section Elgot

variable [Monoid ε] [MulAction ε τ] [StreamMulAction ε τ]

theorem fixpoint_apply {x : α} {step : α → Set (Trace ε τ (β ⊕ α))}
  : divergentTraces (step x) ∪ ⋃ r ∈ doneResults (step x),
    (r.2 • ·) '' Sum.elim (λb => {done b 1}) (λx => iterateTraces step x) r.1
  = iterateTraces step x
  := by
  apply Eq.trans _ leftTraces?_union_iUnion_rightResults_iterateTraces
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

section Ops

variable {ε : Type u} {τ : Type v}

def left' (s : Traces? ε τ (α ⊕ β)) : Set (α × ε) := leftResults s

theorem left'_mono {s t : Traces? ε τ (α ⊕ β)} (h : s ⊆ t) : left' s ⊆ left' t
  := leftResults_mono h

theorem left'_iUnion {s : ι → Traces? ε τ (α ⊕ β)} : left' (Set.iUnion s) = ⋃ i, left' (s i)
  := leftResults_iUnion

def right' (s : Traces? ε τ (α ⊕ β)) : Set (β × ε) := rightResults s

theorem right'_mono {s t : Traces? ε τ (α ⊕ β)} (h : s ⊆ t) : right' s ⊆ right' t
  := rightResults_mono h

theorem right'_iUnion {s : ι → Traces? ε τ (α ⊕ β)} : right' (Set.iUnion s) = ⋃ i, right' (s i)
  := rightResults_iUnion

def dones' (s : Traces? ε τ α) : Set (α × ε) := doneResults s

theorem dones'_mono {s t : Traces? ε τ α} (h : s ⊆ t) : dones' s ⊆ dones' t := doneResults_mono h

theorem dones'_iUnion {s : ι → Traces? ε τ α} : dones' (Set.iUnion s) = ⋃ i, dones' (s i)
  := doneResults_iUnion

theorem left'_union_right' {s : Traces? ε τ (α ⊕ β)}
  : ((λ(a, e) => (Sum.inl a, e)) '' left' s) ∪ ((λ(b, e) => (Sum.inr b, e)) '' right' s) = dones' s
  := leftResults_union_rightResults

def left (s : Traces? ε τ (α ⊕ β)) : Traces? ε τ α := leftTraces s

theorem left_mono {s t : Traces? ε τ (α ⊕ β)} (h : s ⊆ t) : left s ⊆ left t := leftTraces_mono h

theorem left_iUnion {s : ι → Traces? ε τ (α ⊕ β)} : left (Set.iUnion s) = ⋃ i, left (s i)
  := leftTraces_iUnion

def right (s : Traces? ε τ (α ⊕ β)) : Traces? ε τ β := rightTraces s

theorem right_mono {s t : Traces? ε τ (α ⊕ β)} (h : s ⊆ t) : right s ⊆ right t := rightTraces_mono h

theorem right_iUnion {s : ι → Traces? ε τ (α ⊕ β)} : right (Set.iUnion s) = ⋃ i, right (s i)
  := rightTraces_iUnion

def dones (s : Traces? ε τ α) : Traces? ε τ α := doneTraces s

theorem dones_mono {s t : Traces? ε τ α} (h : s ⊆ t) : dones s ⊆ dones t := doneTraces_mono h

theorem dones_iUnion {s : ι → Traces? ε τ α} : dones (Set.iUnion s) = ⋃ i, dones (s i)
  := doneTraces_iUnion

@[simp]
theorem dones'_left {s : Traces? ε τ (α ⊕ β)} : dones' (left s) = left' s := doneResults_leftTraces

@[simp]
theorem dones'_right {s : Traces? ε τ (α ⊕ β)} : dones' (right s) = right' s
  := doneResults_rightTraces

@[simp]
theorem dones'_dones {s : Traces? ε τ α} : dones' (dones s) = dones' s := doneResults_doneTraces

@[simp]
theorem dones_left {s : Traces? ε τ (α ⊕ β)} : dones (left s) = left s := doneTraces_leftTraces

@[simp]
theorem left_dones {s : Traces? ε τ (α ⊕ β)} : left (dones s) = left s := leftTraces_doneTraces

@[simp]
theorem dones_right {s : Traces? ε τ (α ⊕ β)} : dones (right s) = right s := doneTraces_rightTraces

@[simp]
theorem right_dones {s : Traces? ε τ (α ⊕ β)} : right (dones s) = right s := rightTraces_doneTraces

@[simp]
theorem dones_dones {s : Traces? ε τ α} : dones (dones s) = dones s := doneTraces_doneTraces

theorem image_done_dones' {s : Traces? ε τ α} : (λ(a, e) => done a e) '' dones' s = dones s := rfl

def divergent (s : Traces? ε τ α) : Traces? ε τ β := divergentTraces s

theorem divergent_mono {s t : Traces? ε τ α}
  (h : s ⊆ t) : divergent (β := β) s ⊆ divergent t := divergentTraces_mono h

theorem divergent_union {s t : Traces? ε τ α}
  : divergent (β := β) (s ∪ t) = divergent s ∪ divergent t := divergentTraces_union

theorem divergent_iUnion {s : ι → Traces? ε τ α}
  : divergent (β := β) (Set.iUnion s) = ⋃i, divergent (s i) := divergentTraces_iUnion

@[simp]
theorem divergent_divergent {s : Traces? ε τ α}
  : divergent (β := γ) (divergent (β := β) s) = divergent s := divergentTraces_divergentTraces

def left? (s : Traces? ε τ (α ⊕ β)) : Traces? ε τ α := leftTraces? s

theorem left?_mono {s t : Traces? ε τ (α ⊕ β)}
  (h : s ⊆ t) : left? s ⊆ left? t := leftTraces?_mono h

theorem left?_iUnion {s : ι → Traces? ε τ (α ⊕ β)}
  : left? (Set.iUnion s) = ⋃ i, left? (s i) := leftTraces?_iUnion

theorem left?_map_inl {s : Traces? ε τ α} : left? (Sum.inl (β := β) <$> s) = s := by
  apply Set.ext
  intro x
  simp only [left?, leftTraces?, map, Set.mem_preimage, Set.mem_image]
  constructor
  · intro ⟨t, ht, et⟩
    cases t <;> cases x <;> cases et <;> exact ht
  · intro h; exact ⟨x, h, rfl⟩

theorem left?_map_inr {s : Traces? ε τ β} : left? (Sum.inr (α := α) <$> s) = divergent s := by
  apply Set.ext
  intro x
  simp only [left?, leftTraces?, map, Set.mem_preimage, Set.mem_image, divergent, divergentTraces,
    divergentResults]
  constructor
  · intro ⟨t, ht, et⟩
    cases t <;> cases x <;> cases et
    exact ⟨_, ht, rfl⟩
  · intro ⟨t, ht, et⟩
    cases et
    exact ⟨inf t, ht, rfl⟩

def right? (s : Traces? ε τ (α ⊕ β)) : Traces? ε τ β := rightTraces? s

theorem right?_mono {s t : Traces? ε τ (α ⊕ β)}
  (h : s ⊆ t) : right? s ⊆ right? t := rightTraces?_mono h

theorem right?_iUnion {s : ι → Traces? ε τ (α ⊕ β)}
  : right? (Set.iUnion s) = ⋃ i, right? (s i) := rightTraces?_iUnion

theorem right?_map_inl {s : Traces? ε τ α} : right? (Sum.inl (β := β) <$> s) = divergent s := by
  apply Set.ext
  intro x
  simp only [right?, rightTraces?, map, Set.mem_preimage, Set.mem_image, divergent, divergentTraces,
    divergentResults]
  constructor
  · intro ⟨t, ht, et⟩
    cases t <;> cases x <;> cases et
    exact ⟨_, ht, rfl⟩
  · intro ⟨t, ht, et⟩
    cases et
    exact ⟨inf t, ht, rfl⟩

theorem right?_map_inr {s : Traces? ε τ β} : right? (Sum.inr (α := α) <$> s) = s := by
  apply Set.ext
  intro x
  simp only [right?, rightTraces?, map, Set.mem_preimage, Set.mem_image]
  constructor
  · intro ⟨t, ht, et⟩
    cases t <;> cases x <;> cases et <;> exact ht
  · intro h; exact ⟨x, h, rfl⟩

theorem divergent_union_left {s : Traces? ε τ (α ⊕ β)}
  : divergent s ∪ left s = left? s := divergentTraces_union_leftTraces

theorem divergent_union_right {s : Traces? ε τ (α ⊕ β)}
  : divergent s ∪ right s = right? s := divergentTraces_union_rightTraces

@[simp]
theorem divergent_left {s : Traces? ε τ (α ⊕ β)}
  : divergent (β := γ) (left s) = ∅ := divergentTraces_leftTraces

@[simp]
theorem divergent_right {s : Traces? ε τ (α ⊕ β)}
  : divergent (β := γ) (right s) = ∅ := divergentTraces_rightTraces

@[simp]
theorem divergent_dones {s : Traces? ε τ α} : divergent (β := β) (dones s) = ∅
  := divergentTraces_doneTraces

@[simp]
theorem divergent_left? {s : Traces? ε τ (α ⊕ β)}
  : divergent (β := γ) (left? s) = divergent s := divergentTraces_leftTraces?

@[simp]
theorem divergent_right? {s : Traces? ε τ (α ⊕ β)}
  : divergent (β := γ) (right? s) = divergent s := divergentTraces_rightTraces?

@[simp]
theorem left_divergent {s : Traces? ε τ α}
  : left (divergent (β := β ⊕ γ) s) = ∅ := leftTraces_divergentTraces

@[simp]
theorem right_divergent {s : Traces? ε τ α}
  : right (divergent (β := β ⊕ γ) s) = ∅ := rightTraces_divergentTraces

@[simp]
theorem left'_divergent {s : Traces? ε τ α}
  : left' (divergent (β := β ⊕ γ) s) = ∅ := leftResults_divergentTraces

@[simp]
theorem right'_divergent {s : Traces? ε τ α}
  : right' (divergent (β := β ⊕ γ) s) = ∅ := rightResults_divergentTraces

@[simp]
theorem dones'_divergent {s : Traces? ε τ α}
  : dones' (divergent (β := β) s) = ∅ := doneResults_divergentTraces

@[simp]
theorem dones'_left? {s : Traces? ε τ (α ⊕ β)}
  : dones' (left? s) = left' s := doneResults_leftTraces?

@[simp]
theorem dones_left? {s : Traces? ε τ (α ⊕ β)}
  : dones (left? s) = left s := doneTraces_leftTraces?

@[simp]
theorem dones'_right? {s : Traces? ε τ (α ⊕ β)}
  : dones' (right? s) = right' s := doneResults_rightTraces?

@[simp]
theorem dones_right? {s : Traces? ε τ (α ⊕ β)}
  : dones (right? s) = right s := doneTraces_rightTraces?

theorem done_inl_not_mem_map_inr {a : α} {e : ε} {s : Traces? ε τ β}
  : done (Sum.inl a) e ∉ Sum.inr <$> s := λ⟨t, ht, et⟩ => by cases t <;> cases et

theorem done_inr_not_mem_map_inl {b : β} {e : ε} {s : Traces? ε τ α}
  : done (Sum.inr b) e ∉ Sum.inl <$> s := λ⟨t, ht, et⟩ => by cases t <;> cases et

@[simp]
theorem done_inl_mem_map_inl_iff {a : α} {e : ε} {s : Traces? ε τ α}
  : done (Sum.inl a) e ∈ Sum.inl (β := β) <$> s ↔ done a e ∈ s := ⟨
    λ⟨t, ht, et⟩ => by cases t <;> cases et; exact ht,
    λh => ⟨done a e, h, rfl⟩
  ⟩

@[simp]
theorem done_inr_mem_map_inr_iff {b : β} {e : ε} {s : Traces? ε τ β}
  : done (Sum.inr b) e ∈ Sum.inr (α := α) <$> s ↔ done b e ∈ s := ⟨
    λ⟨t, ht, et⟩ => by cases t <;> cases et; exact ht,
    λh => ⟨done b e, h, rfl⟩
  ⟩

@[simp]
theorem inf_mem_map_iff {t : τ} {s : Traces? ε τ α}
  : inf t ∈ f <$> s ↔ inf t ∈ s := ⟨
    λ⟨t', ht', et⟩ => by cases t' <;> cases et; exact ht',
    λh => ⟨inf t, h, rfl⟩
  ⟩

variable [SMul ε τ] [Mul ε]

theorem smul_mono {x y : Traces? ε τ α} {e : ε}
  (h : x ⊆ y) : e • x ⊆ e • y := λ_ ⟨_, ht', et⟩ => ⟨_, h ht', et⟩

theorem image_smul {e : ε} {f : Traces? ε τ α}
  : (e • ·) '' f = e • f := rfl

theorem done_inl_not_mem_smul_map_inr {a : α} {e e' : ε} {s : Traces? ε τ β}
  : done (Sum.inl a) e ∉ e' • Sum.inr <$> s := by rw [smul_map]; exact done_inl_not_mem_map_inr

theorem done_inr_not_mem_smul_map_inl {b : β} {e e' : ε} {s : Traces? ε τ α}
  : done (Sum.inr b) e ∉ e' • Sum.inl <$> s := by rw [smul_map]; exact done_inr_not_mem_map_inl

theorem done_mem_smul_iff {a : α} {e e' : ε} {s : Traces? ε τ α}
  : done a e ∈ e' • s ↔ ∃e'', done a e'' ∈ s ∧ e = e' * e'' := ⟨
    λ⟨t, ht, et⟩ => by cases t <;> cases et; exact ⟨_, ht, rfl⟩,
    λ⟨e'', h, ee⟩ => ⟨done a e'', h, by simp [SMul.smul, ee]⟩
  ⟩

theorem inf_mem_smul_iff {t : τ} {e : ε} {s : Traces? ε τ α}
  : inf t ∈ e • s ↔ ∃t', inf t' ∈ s ∧ e • t' = t := ⟨
    λ⟨x, hx, et⟩ => by cases x <;> cases et; exact ⟨_, hx, rfl⟩,
    λ⟨x, hx, et⟩ => ⟨inf x, hx, by simp [SMul.smul, et]⟩
  ⟩

theorem done_inl_mem_smul_map_inl_iff {a : α} {e e' : ε} {s : Traces? ε τ α}
  : done (Sum.inl a) e ∈ e' • Sum.inl (β := β) <$> s ↔ ∃e'', done a e'' ∈ s ∧ e = e' * e''
  := by rw [smul_map, done_inl_mem_map_inl_iff, done_mem_smul_iff]

theorem done_inr_mem_smul_map_inr_iff {b : β} {e e' : ε} {s : Traces? ε τ β}
  : done (Sum.inr b) e ∈ e' • Sum.inr (α := α) <$> s ↔ ∃e'', done b e'' ∈ s ∧ e = e' * e''
  := by rw [smul_map, done_inr_mem_map_inr_iff, done_mem_smul_iff]

theorem divergent_smul {x : Traces? ε τ α} {e : ε}
  : divergent (β := β) (e • x) = e • divergent x := by
  apply Set.ext
  intro t
  simp only [divergent, divergentTraces, divergentResults, Set.mem_image, Set.mem_preimage]
  constructor
  · intro ⟨t, hx, et⟩
    cases et
    rw [inf_mem_smul_iff] at *
    let ⟨t, ht, et⟩ := hx
    exact ⟨t, ⟨t, ht, rfl⟩, et⟩
  · intro ⟨t, ⟨t', ht', et'⟩, et⟩
    cases et
    cases et'
    exact ⟨e • t', ⟨inf t', ht', rfl⟩, rfl⟩

theorem dones_smul {x : Traces? ε τ α} {e : ε}
  : dones (e • x) = e • dones x := by
  apply Set.ext
  intro t
  simp only [dones, doneTraces, doneResults, Set.mem_image, Set.mem_setOf_eq, Prod.exists]
  constructor
  · intro ⟨a, e, hae, et⟩
    cases et
    rw [done_mem_smul_iff] at *
    let ⟨e'', ht, et⟩ := hae
    cases et
    exact ⟨e'', ⟨(a, e''), ht, rfl⟩, rfl⟩
  · intro ⟨t, ht, et⟩
    cases et
    simp only [Set.mem_image, Set.mem_setOf_eq, Prod.exists] at ht
    let ⟨a, e', hae, et⟩ := ht
    cases et
    exact ⟨a, e * e', ⟨done a e', hae, rfl⟩, rfl⟩

theorem left_smul {x : Traces? ε τ (α ⊕ β)} {e : ε}
  : left (e • x) = e • left x := by
  apply Set.ext
  intro t
  simp only [left, leftTraces, leftResults, Set.mem_image, Set.mem_setOf_eq, Prod.exists]
  constructor
  · intro ⟨a, e, hae, et⟩
    cases et
    rw [done_mem_smul_iff] at *
    let ⟨e'', ht, et⟩ := hae
    cases et
    exact ⟨e'', ⟨(a, e''), ht, rfl⟩, rfl⟩
  · intro ⟨t, ht, et⟩
    cases et
    simp only [Set.mem_image, Set.mem_setOf_eq, Prod.exists] at ht
    let ⟨a, e', hae, et⟩ := ht
    cases et
    exact ⟨a, e * e', ⟨done (Sum.inl a) e', hae, rfl⟩, rfl⟩

theorem right_smul {x : Traces? ε τ (α ⊕ β)} {e : ε}
  : right (e • x) = e • right x := by
  apply Set.ext
  intro t
  simp only [right, rightTraces, rightResults, Set.mem_image, Set.mem_setOf_eq, Prod.exists]
  constructor
  · intro ⟨a, e, hae, et⟩
    cases et
    rw [done_mem_smul_iff] at *
    let ⟨e'', ht, et⟩ := hae
    cases et
    exact ⟨e'', ⟨(a, e''), ht, rfl⟩, rfl⟩
  · intro ⟨t, ht, et⟩
    cases et
    simp only [Set.mem_image, Set.mem_setOf_eq, Prod.exists] at ht
    let ⟨a, e', hae, et⟩ := ht
    cases et
    exact ⟨a, e * e', ⟨done (Sum.inr a) e', hae, rfl⟩, rfl⟩

theorem union_smul {x y : Traces? ε τ α} {e : ε}
  : e • x ∪ e • y = e • (x ∪ y) := by
  simp only [HSMul.hSMul, SMul.smul, Set.fmap_eq_image]
  rw [Set.image_union]

theorem left?_smul {x : Traces? ε τ (α ⊕ β)} {e : ε}
  : left? (e • x) = e • left? x := by
  simp only [<-divergent_union_left, divergent_smul, left_smul, union_smul]

theorem right?_smul {x : Traces? ε τ (α ⊕ β)} {e : ε}
  : right? (e • x) = e • right? x := by
  simp only [<-divergent_union_right, divergent_smul, right_smul, union_smul]

variable [One ε]

theorem iUnion_bind {f : ι → Traces? ε τ α} {g : α → Traces? ε τ β}
  : ((Set.iUnion f : Traces? ε τ α) >>= g : Traces? ε τ β) = ⋃i, (f i >>= g : Traces? ε τ β)
  := by simp only [bind, Set.pure_def, Set.bind_def, Set.biUnion_iUnion]

theorem bind_mono {x y : Traces? ε τ α} {f g : α → Traces? ε τ β}
  (h : x ⊆ y) (h' : ∀r ∈ dones' y, f r.1 ⊆ g r.1) : x >>= f ⊆ y >>= g := by
  simp only [bind, Set.pure_def, Set.bind_def]
  apply Set.biUnion_mono h
  intro x hx
  cases x with
  | done a e => exact smul_mono (h' (a, e) hx)
  | inf => rfl

theorem divergentTraces_subset_bind {x : Traces? ε τ α} {f : α → Traces? ε τ β}
  : divergentTraces x ⊆ (x >>= f : Traces? ε τ β) := by
  intro tm ⟨t, ht, et⟩
  cases et
  simp only [divergentResults, Set.mem_preimage] at ht
  simp only [bind, Set.pure_def, Set.bind_def, Set.mem_iUnion, exists_prop]
  exact ⟨inf t, ht, by simp⟩

theorem divergent_subset_bind {x : Traces? ε τ α} {f : α → Traces? ε τ β}
  : divergent x ⊆ x >>= f := divergentTraces_subset_bind

theorem doneResults_subset_bind {x : Traces? ε τ α} {f : α → Traces? ε τ β}
  {a : α} {e : ε} : (a, e) ∈ doneResults x → e • f a ⊆ x >>= f := by
  simp only [doneResults, Set.mem_setOf_eq]
  intro hx t ht
  simp only [bind, Set.pure_def, Set.bind_def, Set.mem_iUnion, exists_prop]
  exact ⟨done a e, hx, ht⟩

theorem dones'_subset_bind {x : Traces? ε τ α} {f : α → Traces? ε τ β}
  {a : α} {e : ε} : (a, e) ∈ x.dones' → e • f a ⊆ x >>= f := doneResults_subset_bind

theorem dones'_bind {x : Traces? ε τ α} {f : α → Traces? ε τ β}
  : dones' (x >>= f) = ⋃ r ∈ x.dones', dones' (r.2 • f r.1) := by
  ext x
  cases x with
  | mk b e =>
  simp only [dones', doneResults, bind, Set.pure_def, Set.bind_def, Set.mem_iUnion, exists_prop,
    Set.mem_setOf_eq, Prod.exists]
  constructor
  · intro ⟨t, ht, hbe⟩
    cases t with
    | done a e => exact ⟨a, e, ht, hbe⟩
    | inf t => simp at hbe
  · intro ⟨a, e, ht, hbe⟩
    exact ⟨done a e, ht, hbe⟩

theorem dones_bind_set {x : Traces? ε τ α} {f : α → Traces? ε τ β}
  : dones (x >>= f) = ⋃ r ∈ x.dones', dones (r.2 • f r.1) := by
  simp only [<-image_done_dones', dones'_bind, Set.image_iUnion]

theorem left_bind {x : Traces? ε τ α} {f : α → Traces? ε τ (β ⊕ γ)}
  : left (x >>= f) = ⋃ r ∈ x.dones', left (r.2 • f r.1)
  := by rw [<-left_dones, dones_bind_set]; simp [left_iUnion]

theorem right_bind {x : Traces? ε τ α} {f : α → Traces? ε τ (β ⊕ γ)}
  : right (x >>= f) = ⋃ r ∈ x.dones', right (r.2 • f r.1)
  := by rw [<-right_dones, dones_bind_set]; simp [right_iUnion]

-- theorem right'_bind_sum {f : α → Traces? ε τ (β ⊕ γ)}
--   {g : β → Traces? ε τ β'} {h : γ → Traces? ε τ γ'} {a : α}
--   : right' (f a >>= sumM g h : Traces? ε τ (β' ⊕ γ')) = dones' ((f a).right >>= h) := by
--   simp only [right', rightResults, bind, Set.pure_def, Set.bind_def, Set.mem_iUnion, exists_prop,
--     dones', doneResults]
--   apply congrArg
--   funext (c, e)
--   apply propext
--   constructor
--   · intro ⟨t, ht, hce⟩
--     cases t with
--     | done a e =>
--       cases a with
--       | inl a => exact (done_inr_not_mem_smul_map_inl hce).elim
--       | inr a =>
--         simp at hce
--         sorry
--     | inf t => simp at hce
--   · sorry

end Ops

section Action

variable {ε : Type u} {τ : Type v} [Monoid ε] [MulAction ε τ]

-- theorem right'_bind_sum_left {f : α → Traces? ε τ (β ⊕ γ)}
--   {g : β → Traces? ε τ β'} {a : α}
--   : right' ((f a >>= sumM g pure : Traces? ε τ (β' ⊕ γ))) = right' (f a) := by
--   simp [right'_bind_sum]

end Action

section Iterate

variable {ε : Type u} {τ : Type v} [Monoid ε] [SMul ε τ]

open MonadIterate

theorem bind_eq_set {x : Traces? ε τ α} {f : α → Traces? ε τ β}
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

theorem bind_eq {x : Traces? ε τ α} {f : α → Traces? ε τ β}
  : x >>= f = divergent x ∪ ⋃ r ∈ dones' x, r.2 • f r.1
  := bind_eq_set

theorem bind_dones {x : Traces? ε τ α} {f : α → Traces? ε τ β}
  : dones x >>= f = ⋃ r ∈ x.dones', r.2 • f r.1 := by
  simp only [bind_eq, divergent_dones, dones'_dones]
  exact Set.empty_union _

theorem bind_union {x y : Traces? ε τ α} {f : α → Traces? ε τ β}
  : (x ∪ y) >>= f = (x >>= f) ∪ (y >>= f) := by simp [bind, Set.biUnion_union]

theorem bind_divergent {x : Traces? ε τ α} {f : α → Traces? ε τ β}
  : divergent x >>= f = divergent x := by
  simp only [bind_eq, divergent_divergent, dones'_divergent, Set.mem_empty_iff_false,
    Set.iUnion_of_empty, Set.iUnion_empty]
  exact Set.union_empty _

theorem bind_factor {x : Traces? ε τ α} {f : α → Traces? ε τ β}
  : x >>= f = divergent x ∪ dones x >>= f := by
  rw [bind_eq, <-bind_dones, bind_union, bind_divergent]

theorem divergent_bind {x : Traces? ε τ α} {f : α → Traces? ε τ β}
  : divergent (β := γ) (x >>= f) = divergent x ∪ ⋃r ∈ dones' x, divergent (r.2 • f r.1) := by
  rw [bind_eq, divergent_union, divergent_divergent]
  congr
  simp only [divergent_iUnion]

theorem left?_bind {x : Traces? ε τ α} {f : α → Traces? ε τ (β ⊕ γ)}
  : left? (x >>= f) = divergent x ∪ ⋃ r ∈ x.dones', left? (r.2 • f r.1) := by
  rw [<-divergent_union_left, divergent_bind, Set.union_assoc, left_bind]
  apply congrArg
  simp only [Set.biUnion_union_biUnion, <-divergent_union_left]

theorem right?_bind {x : Traces? ε τ α} {f : α → Traces? ε τ (β ⊕ γ)}
  : right? (x >>= f) = divergent x ∪ ⋃ r ∈ x.dones', right? (r.2 • f r.1) := by
  rw [<-divergent_union_right, divergent_bind, Set.union_assoc, right_bind]
  apply congrArg
  simp only [Set.biUnion_union_biUnion, <-divergent_union_right]

theorem left?_bind_sum {x : Traces? ε τ (α ⊕ β)}
  {g : α → Traces? ε τ α'} {h : β → Traces? ε τ β'}
  : left? (x >>= sumM g h) = (left? x >>= g) ∪ divergent (right x >>= h) := by
  rw [left?_bind, bind_eq, divergent_left?]
  simp only [
    dones'_left?, <-left'_union_right', Set.biUnion_union, Set.biUnion_image,
    sumM, Sum.elim_inl, Function.comp_apply, Sum.elim_inr, left?_smul, left?_map_inl
  ]
  rw [<-Set.union_assoc, Set.union_eq_union_iff_left]
  constructor
  · simp only [Set.iUnion_subset_iff, Prod.forall]
    intro a e hae t
    rw [left?_map_inr, <-divergent_smul, divergent, divergentTraces, divergentResults]
    simp only [Set.mem_image, Set.mem_preimage, Set.mem_union, Set.mem_iUnion, exists_prop,
      Prod.exists, forall_exists_index, and_imp]
    intro t ht et
    cases et
    apply Or.inr
    simp only [divergent, divergentTraces, divergentResults, bind, Set.pure_def, Set.bind_def,
      Set.preimage_iUnion, Set.mem_image, Set.mem_iUnion, Set.mem_preimage, exists_prop, inf.injEq,
      exists_eq_right]
    exact ⟨done a e, ⟨(a, e), hae, rfl⟩, ht⟩
  · simp only [divergent_bind, divergent_right, dones'_right]
    apply Set.union_subset_union
    · exact Set.empty_subset _
    · simp only [divergent, divergentTraces, divergentResults, Set.iUnion_subset_iff,
      Set.image_subset_iff, Set.preimage_iUnion, Prod.forall]
      intro b e p t
      simp only [Set.mem_preimage, Set.mem_iUnion, exists_prop, Prod.exists]
      intro ht
      rw [inf_mem_smul_iff] at ht
      let ⟨t', ht', et⟩ := ht
      cases et
      exact ⟨b, e, p, ⟨inf t', ⟨inf t', ht', rfl⟩, rfl⟩⟩

theorem right?_bind_sum {x : Traces? ε τ (α ⊕ β)}
  {g : α → Traces? ε τ α'} {h : β → Traces? ε τ β'}
  : right? (x >>= sumM g h) = (right? x >>= h) ∪ divergent (left x >>= g) := by
  rw [right?_bind, bind_eq, divergent_right?]
  simp only [
    dones'_right?, <-left'_union_right', Set.biUnion_union, Set.biUnion_image,
    sumM, Sum.elim_inl, Function.comp_apply, Sum.elim_inr, right?_smul, right?_map_inr,
  ]
  conv => lhs; rhs; rw [Set.union_comm]
  rw [<-Set.union_assoc, Set.union_eq_union_iff_left]
  constructor
  · simp only [Set.iUnion_subset_iff, Prod.forall]
    intro b e hbe t
    rw [right?_map_inl, <-divergent_smul, divergent, divergentTraces, divergentResults]
    simp only [Set.mem_image, Set.mem_preimage, Set.mem_union, Set.mem_iUnion, exists_prop,
      Prod.exists, forall_exists_index, and_imp]
    intro t ht et
    cases et
    apply Or.inr
    simp only [divergent, divergentTraces, divergentResults, bind, Set.pure_def, Set.bind_def,
      Set.preimage_iUnion, Set.mem_image, Set.mem_iUnion, Set.mem_preimage, exists_prop, inf.injEq,
      exists_eq_right]
    exact ⟨done b e, ⟨(b, e), hbe, rfl⟩, ht⟩
  · simp only [divergent_bind, divergent_left, dones'_left]
    apply Set.union_subset_union
    · exact Set.empty_subset _
    · simp only [divergent, divergentTraces, divergentResults, Set.iUnion_subset_iff,
      Set.image_subset_iff, Set.preimage_iUnion, Prod.forall]
      intro a e p t
      simp only [Set.mem_preimage, Set.mem_iUnion, exists_prop, Prod.exists]
      intro ht
      rw [inf_mem_smul_iff] at ht
      let ⟨t', ht', et⟩ := ht
      cases et
      exact ⟨a, e, p, ⟨inf t', ⟨inf t', ht', rfl⟩, rfl⟩⟩

theorem divergent_pure {a : α} : divergent (β := β) (pure a : Traces? ε τ α) = ∅ := by
  apply Set.ext
  intro t
  simp only [divergent, divergentTraces, divergentResults, Set.mem_image, Set.mem_preimage]
  constructor
  · intro ⟨t, ht, et⟩
    cases et
    simp only [pure, Set.mem_singleton_iff] at ht
    cases ht
  · intro h
    exact h.elim

theorem left?_bind_sum_pure {x : Traces? ε τ (α ⊕ β)}
  {g : α → Traces? ε τ α'}
  : left? (x >>= sumM g pure) = left? x >>= g := by
  rw [left?_bind_sum, divergent_bind, divergent_right]
  simp only [divergent_smul, divergent_pure, smul_empty]
  rw [Set.empty_union]
  convert Set.union_empty _
  simp

theorem left?_naturality {f : α → Traces? ε τ (β ⊕ γ)}
  {g : β → Traces? ε τ β'} {a : α}
  : left? ((f >=> sumM g pure) a)
  = ((left? (f a) : Traces? ε τ β) >>= g)
  := by rw [Bind.kleisliRight, left?_bind_sum_pure]

theorem leftTraces?_naturality {f : α → Traces? ε τ (β ⊕ γ)}
  {g : β → Traces? ε τ β'} {a : α}
  : leftTraces? ((f >=> sumM g pure : α → Traces? ε τ (β' ⊕ _)) a)
  = ((leftTraces? (f a) : Traces? ε τ β) >>= g : Traces? ε τ β')
  := left?_naturality

theorem right?_bind_sum_pure {x : Traces? ε τ (α ⊕ β)}
  {h : β → Traces? ε τ β'}
  : right? (x >>= sumM pure h) = right? x >>= h := by
  rw [right?_bind_sum, divergent_bind, divergent_left]
  simp only [divergent_smul, divergent_pure, smul_empty]
  rw [Set.empty_union]
  convert Set.union_empty _
  simp

theorem right?_naturality {f : α → Traces? ε τ (β ⊕ γ)}
  {h : γ → Traces? ε τ γ'} {a : α}
  : right? ((f >=> sumM pure h) a)
  = ((right? (f a) : Traces? ε τ γ) >>= h)
  := by rw [Bind.kleisliRight, right?_bind_sum_pure]

theorem kleisli_apply_eq_set (f : α → Traces? ε τ β) (g : β → Traces? ε τ γ) (a : α)
  : (f >=> g) a
  = divergentTraces (f a) ∪ ⋃ r ∈ doneResults (f a), r.2 • g r.1
  := by rw [Bind.kleisliRight, bind_eq_set]

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

-- theorem rightResults_bind_sum_left {f : α → Traces? ε τ (β ⊕ γ)}
--   {g : β → Traces? ε τ β'} {a : α}
--   : rightResults ((f a >>= sumM g pure : Traces? ε τ (β' ⊕ γ)))
--   = rightResults (f a) := right'_bind_sum_left

-- theorem rightResults_naturality_left {f : α → Traces? ε τ (β ⊕ γ)}
--   {g : β → Traces? ε τ β'} {a : α}
--   : rightResults ((f >=> sumM g pure : α → Traces? ε τ (β' ⊕ γ)) a)
--   = rightResults (f a)
--   := by rw [Bind.kleisliRight, rightResults_bind_sum_left]

-- theorem approxFiniteTraces_naturality {f : α → Traces? ε τ (β ⊕ α)} {g : β → Traces? ε τ γ} {a : α}
--   : approxFiniteTraces (f >=> sumM g pure : α → Traces? ε τ (γ ⊕ α)) a n
--   = ((approxFiniteTraces f a n : Traces? ε τ β) >>= g : Traces? ε τ γ)
--   := by
--   induction n generalizing a with
--   | zero => rw [approxFiniteTraces, leftTraces?_naturality]; rfl
--   | succ n I => simp only [
--     approxFiniteTraces, rightResults_naturality_left, I, image_smul, Traces?.smul_bind, iUnion_bind]

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
--   simp only [bind_eq_set, divergentTraces, divergentResults, Set.mem_union, Set.mem_image,
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
--     simp only [iterate, kleisli_apply_eq_set]
--     apply Eq.trans _ fixpoint_apply
--     apply congrArg
--     apply congrArg
--     funext ⟨r, e⟩
--     apply congrArg
--     funext h
--     cases r <;> simp [pure, HSMul.hSMul, SMul.smul]
--   naturality f g := by
--     ext x
--     simp only [iterate, iterateTraces, kleisli_apply_eq_set, divergentTraces_union,
--       divergentTraces_infiniteTraces, doneResults_union, doneResults_infiniteTraces,
--       Set.union_empty]
--     conv => lhs; lhs; rw [Set.union_comm]
--     rw [
--       Set.union_assoc, <-bind_eq_set, finiteTraces_naturality, Set.union_comm,
--       infiniteTraces_naturality
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
