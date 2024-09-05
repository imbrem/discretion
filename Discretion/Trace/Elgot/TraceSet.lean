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

theorem exists_rightResult_of_finiteTrace_empty
  (hstep : ∀a, Set.Nonempty (step a)) (a) (hfin : finiteTraces step a = ∅)
    : ∃r : α × ε, r ∈ rightResults (step a) := by
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

noncomputable def choose_rightResult_of_finiteTrace_empty
  (hstep : ∀a, Set.Nonempty (step a)) (a) (hfin : finiteTraces step a = ∅) : α × ε
  := Classical.choose (exists_rightResult_of_finiteTrace_empty hstep a hfin)

theorem choose_rightResult_of_finiteTrace_empty_spec
  (hstep : ∀a, Set.Nonempty (step a)) (a) (hfin : finiteTraces step a = ∅)
  : choose_rightResult_of_finiteTrace_empty hstep a hfin ∈ rightResults (step a) := by
  apply Classical.choose_spec (exists_rightResult_of_finiteTrace_empty hstep a hfin)

theorem finiteTrace_choose_rightResult_empty
  (hstep : ∀a, Set.Nonempty (step a)) (a) (hfin : finiteTraces step a = ∅)
  : finiteTraces step (choose_rightResult_of_finiteTrace_empty hstep a hfin).1 = ∅
  := (rightResults_finiteTraces_empty_of_finiteTraces_empty hfin _
        (choose_rightResult_of_finiteTrace_empty_spec hstep a hfin))

noncomputable def choose_action_finiteTrace_empty
  (hstep : ∀a, Set.Nonempty (step a)) (a) (hfin : finiteTraces step a = ∅) : Stream' α
  := λn =>
    match n with
    | 0 => (choose_rightResult_of_finiteTrace_empty hstep a hfin).1
    | n + 1 => choose_action_finiteTrace_empty
      hstep (choose_rightResult_of_finiteTrace_empty hstep a hfin).1
      (finiteTrace_choose_rightResult_empty hstep a hfin) n

noncomputable def choose_effect_finiteTrace_empty
  (hstep : ∀a, Set.Nonempty (step a)) (a) (hfin : finiteTraces step a = ∅) : Stream' ε
  := λn =>
    match n with
    | 0 => (choose_rightResult_of_finiteTrace_empty hstep a hfin).2
    | n + 1 => choose_effect_finiteTrace_empty hstep
      (choose_rightResult_of_finiteTrace_empty hstep a hfin).1
      (finiteTrace_choose_rightResult_empty hstep a hfin) n

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
    apply choose_rightResult_of_finiteTrace_empty_spec hstep
    apply finiteTrace_choose_rightResult_empty
  | succ n I =>
    simp only [choose_action_finiteTrace_empty, choose_effect_finiteTrace_empty, Stream'.get] at *
    apply I

theorem choose_action_finiteTrace_empty_spec
  (hstep : ∀a, Set.Nonempty (step a)) (a) (hfin : finiteTraces step a = ∅)
  : choose_action_finiteTrace_empty hstep a hfin ∈ actionStreams step a
  := ⟨choose_effect_finiteTrace_empty hstep a hfin,
    by
      simp only [choose_action_finiteTrace_empty, choose_effect_finiteTrace_empty]
      apply choose_rightResult_of_finiteTrace_empty_spec hstep a hfin
    ,
    choose_finiteTrace_empty_spec hstep a hfin⟩

theorem choose_effect_finiteTrace_empty_spec
  (hstep : ∀a, Set.Nonempty (step a)) (a) (hfin : finiteTraces step a = ∅)
  : choose_effect_finiteTrace_empty hstep a hfin ∈ effectStreams step a
  := ⟨choose_action_finiteTrace_empty hstep a hfin,
    by
      simp only [choose_action_finiteTrace_empty, choose_effect_finiteTrace_empty]
      apply choose_rightResult_of_finiteTrace_empty_spec hstep a hfin
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
