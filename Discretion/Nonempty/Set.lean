import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Image
import Mathlib.Order.SetNotation
import Mathlib.Order.OmegaCompletePartialOrder
import Mathlib.Order.Max

open Functor

def NSet (α : Type u) := {x : Set α // x.Nonempty}

namespace NSet

@[ext]
theorem ext {s t : NSet α} : s.val = t.val → s = t
  := by intro h; cases s; cases t; cases h; rfl

instance instCoeSet : Coe (NSet α) (Set α) := ⟨fun s => s.val⟩

instance instCoeSort : CoeSort (NSet α) (Type u) := ⟨fun s => Set.Elem s.val⟩

instance instTop [Nonempty α] : Top (NSet α) where
  top := ⟨Set.univ, ⟨Classical.ofNonempty, by trivial⟩⟩

instance instInhabited [Nonempty α] : Inhabited (NSet α) where
  default := ⊤

instance instMembership : Membership α (NSet α) := ⟨fun s a => a ∈ s.val⟩

theorem coe_mem_iff {a : α} {s : NSet α} : a ∈ s ↔ a ∈ s.val := Iff.rfl

theorem coe_mem {a : α} {s : NSet α} : a ∈ s → a ∈ s.val := coe_mem_iff.mp

theorem mem_coe {a : α} {s : NSet α} : a ∈ s.val → a ∈ s := coe_mem_iff.mpr

theorem nonempty (s : NSet α) : Nonempty α := have ⟨a, _⟩ := s.prop; ⟨a⟩

noncomputable def choose (s : NSet α) : α := Classical.choose s.prop

@[simp]
theorem choose_mem (s : NSet α) : choose s ∈ s := Classical.choose_spec s.prop

instance instCoeNonempty {s : NSet α} : Nonempty s := ⟨⟨s.choose, s.choose_mem⟩⟩

instance instSingleton : Singleton α (NSet α) := ⟨fun a => ⟨{a}, ⟨a, rfl⟩⟩⟩

@[simp]
theorem coe_singleton (a : α) : (({a} : NSet α) : Set α) = {a} := rfl

instance instInsert : Insert α (NSet α)
  := ⟨fun a s => ⟨insert a s.val, ⟨a, by simp⟩⟩⟩

@[simp]
theorem coe_insert (a : α) (s : NSet α) : (insert a s : Set α) = insert a (s : Set α) := rfl

instance instUnion : Union (NSet α)
  := ⟨fun s t => ⟨s.val ∪ t.val, by simp [s.prop]⟩⟩

@[simp]
theorem coe_union (s t : NSet α) : (s ∪ t : Set α) = (s : Set α) ∪ (t : Set α) := rfl

instance instHasSubset : HasSubset (NSet α) := ⟨fun s t => s.val ⊆ t.val⟩

theorem coe_subset_iff {s t : NSet α} : s ⊆ t ↔ s.val ⊆ t.val := Iff.rfl

theorem coe_subset {s t : NSet α} : s ⊆ t → s.val ⊆ t.val := coe_subset_iff.mp

theorem subset_coe {s t : NSet α} : s.val ⊆ t.val → s ⊆ t := coe_subset_iff.mpr

instance instHasSSubset : HasSSubset (NSet α) := ⟨fun s t => s.val ⊂ t.val⟩

instance instPartialOrder : PartialOrder (NSet α) where
  le s t := s ⊆ t
  le_refl s := le_refl (α := Set α) s
  le_trans s t u := le_trans (α := Set α)
  le_antisymm s t hst hts := ext <| le_antisymm (α := Set α) hst hts

theorem coe_le_iff {s t : NSet α} : s ≤ t ↔ s.val ≤ t.val := Iff.rfl

theorem coe_le {s t : NSet α} : s ≤ t → s.val ≤ t.val := coe_le_iff.mp

theorem le_coe {s t : NSet α} : s.val ≤ t.val → s ≤ t := coe_le_iff.mpr

def iUnion [Nonempty ι] (s : ι → NSet α) : NSet α
  := ⟨Set.iUnion (λi => s i), ⟨
      (s Classical.ofNonempty).choose, s Classical.ofNonempty,
      ⟨Classical.ofNonempty, rfl⟩, choose_mem _⟩⟩

@[simp]
theorem coe_iUnion [Nonempty ι] (s : ι → NSet α)
  : (iUnion s : Set α) = Set.iUnion (λi => s i) := rfl

@[simp]
theorem iUnion_singleton_set {i : ι} {f : ι → NSet α}
  : iUnion (λx : ({i} : Set ι) => f x) = f i := by ext x; simp [iUnion]

@[simp]
theorem iUnion_singleton_nset {i : ι} {f : ι → NSet α}
  : iUnion (λx : ({i} : NSet ι) => f x) = f i
  := iUnion_singleton_set

theorem biUnion_iUnion {ι : Type u} [Nonempty ι] (s : ι → NSet α) (t : α → NSet β)
  : iUnion (λa : iUnion s => t a) = iUnion (λi : ι => iUnion (λa : s i => t a)) := by
  ext b; simp only [coe_iUnion, Set.mem_iUnion, Subtype.exists, exists_prop]
  constructor
  · intro ⟨a, ⟨i, ha⟩, hb⟩
    exact ⟨i, ⟨a, ha, hb⟩⟩
  · intro ⟨i, ⟨a, ha, hb⟩⟩
    exact ⟨a, ⟨i, ha⟩, hb⟩

def sUnion (s : NSet (NSet α)) : NSet α
  := ⟨{a : α | ∃t ∈ s, a ∈ t}, ⟨s.choose.choose, ⟨s.choose, s.choose_mem, s.choose.choose_mem⟩⟩⟩

@[simp]
theorem sUnion_singleton {s : NSet α} : sUnion {s} = s := by
  ext a; simp only [sUnion, Set.mem_setOf_eq]
  exact ⟨λ⟨_, ht, ha⟩ => ht ▸ ha, λha => ⟨_, rfl, ha⟩⟩

instance instFunctor : Functor NSet where
  map f s := ⟨f '' s.val, let ⟨a, ha⟩ := s.prop; ⟨f a, a, ha, rfl⟩⟩

instance instLawfulFunctor : LawfulFunctor NSet where
  id_map s := by simp [map]
  comp_map f g s := by simp [map, Set.image_image]
  map_const := rfl

@[simp]
theorem map_singleton {f : α → β} {a : α} : f <$> ({a} : NSet α) = {f a} := by
  simp only [map, coe_singleton, Set.image_singleton]; rfl

@[simp]
theorem iUnion_singleton_map_of_nset {s : NSet ι} {f : ι → α}
  : iUnion (λi : s => {f i}) = f <$> s := by
  ext a; simp only [coe_iUnion, coe_singleton, Set.mem_iUnion, Set.mem_singleton_iff,
    Subtype.exists, exists_prop]
  constructor <;> {
    intro ⟨i, hi, ha⟩
    cases ha
    exact ⟨i, hi, rfl⟩
  }

@[simp]
theorem iUnion_singleton_of_nset {s : NSet ι}
  : iUnion (λi : s => {(i : ι)}) = s := (iUnion_singleton_map_of_nset (f := id)).trans (id_map s)

theorem sUnion_map (f : α → NSet β) (s : NSet α) : sUnion (f <$> s) = iUnion (λx : s => f x) := by
  ext x; simp only [sUnion, Set.mem_setOf_eq, iUnion, Set.mem_iUnion, Subtype.exists, exists_prop]
  constructor
  · intro ⟨t, ⟨a, ha, ht⟩, hx⟩
    cases ht
    exact ⟨a, ha, hx⟩
  · intro ⟨a, ha, hx⟩
    exact ⟨f a, ⟨a, ha, rfl⟩, hx⟩

-- theorem map_sUnion (f : α → NSet β) (s : NSet (NSet α))
--   : f <$> sUnion s = sUnion (map f <$> s) := by
--   sorry

instance instMonad : Monad NSet where
  pure a := {a}
  bind s f := iUnion (λx : s => f x)

instance instLawfulMonad : LawfulMonad NSet :=
  LawfulMonad.mk'
    (id_map := λs => by simp)
    (pure_bind := λs f => by simp [bind, pure])
    (bind_assoc := λs f g => by simp [bind, <-biUnion_iUnion])
    (bind_pure_comp := λf s => by simp [bind, pure])

-- instance instNoBotOrder [Nontrivial α] : NoBotOrder (NSet α) where
--   exists_not_ge s := open Classical in if h : ∃x y, x ∈ s ∧ y ∈ s ∧ x ≠ y then
--       have ⟨x, y, hx, hy⟩ := h
--       sorry
--     else
--       sorry

instance instMax : Max (NSet α) where
  max s t := s ∪ t

instance instOrderTop [Nonempty α] : OrderTop (NSet α) where
  le_top a := by
    apply subset_coe
    apply Set.subset_univ

instance instSemilatticeSup : SemilatticeSup (NSet α) where
  sup := max
  le_sup_left s t := by
    apply subset_coe
    apply Set.subset_union_left
  le_sup_right s t := by
    apply subset_coe
    apply Set.subset_union_right
  sup_le s t u hs hu := by
    apply subset_coe
    apply Set.union_subset hs hu

instance instOmegaCompletePartialOrder : OmegaCompletePartialOrder (NSet α) where
  ωSup c := iUnion (λi => c i)
  le_ωSup c i a ha := ⟨c i, ⟨i, rfl⟩, ha⟩
  ωSup_le c s hc a | ⟨s, ⟨i, hi⟩, ha⟩ => by cases hi; exact hc i ha

open Classical

-- NOTE: this is a CPO, but we would need to change Lean's definition of a CPO to show this, since
-- sSup will only be an LUB of a _nonempty_ directed set
noncomputable instance instSupSet [Nonempty α] : SupSet (NSet α) where
  sSup s := if h : s.Nonempty then sUnion ⟨s, h⟩ else ⊤
