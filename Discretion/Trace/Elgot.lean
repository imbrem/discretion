import Discretion.Trace.Basic
import Discretion.Elgot.Monad
import Discretion.Stream.Action
import Discretion.Utils.Set

import Discretion.Trace.Elgot.TraceSet

open StreamProd

open Functor

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
