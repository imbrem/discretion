/- Adapted from https://github.com/leanprover-community/mathlib4/blob/b856377d9cf6945a16d9abeaf713bcd10ea0d2db/Mathlib/Data/Finsupp/Defs.lean -/

import Discretion.OrderSupport

import Mathlib.Data.Set.Finite

open Finset Function

/-- `FinExcept α M s`, is the type of functions `f : α → M` such that `f x ∈ Z` for all but
  finitely many `x`. -/
structure FinExcept (α : Type*) (M : Type*) (Z : Set M) where
  /-- The support on which this function lies outside of `Z` -/
  support : Finset α
  /-- The underlying function -/
  toFun : α → M
  /-- The witness that the support of a `FinExcept` is indeed the exact locus where its
  underlying function lies outside of `Z`. -/
  mem_support_toFun : ∀ a, a ∈ support ↔ toFun a ∉ Z

namespace FinExcept

section Basic

variable {α : Type u} {M : Type v} {Z Z' : Set M}

instance instFunLike : FunLike (FinExcept α M Z) α M :=
  ⟨toFun, by
    rintro ⟨s, f, hf⟩ ⟨t, g, hg⟩ (rfl : f = g)
    congr
    ext a
    exact (hf _).trans (hg _).symm⟩

/-- Helper instance for when there are too many metavariables to apply the `DFunLike` instance
directly. -/
instance instCoeFun : CoeFun (FinExcept α M Z) fun _ => α → M :=
  inferInstance

@[ext]
theorem ext {f g : FinExcept α M Z} (h : ∀ a, f a = g a) : f = g :=
  DFunLike.ext _ _ h

@[simp, norm_cast]
theorem coe_mk (f : α → M) (s : Finset α) (h : ∀ a, a ∈ s ↔ f a ∉ Z)
  : ⇑(⟨s, f, h⟩ : FinExcept α M Z) = f :=
  rfl

-- @[simp]
-- theorem support_top : (⊤ : α →ᵀ M).support = ∅ :=
--   rfl

/-- `always z` is the function with value `z` everywhere -/
def always (z : Z) : FinExcept α M Z where
  support := ∅
  toFun := fun _ => z
  mem_support_toFun := by simp

theorem always_apply {z : Z} {a : α} : (always z) a = z :=
  rfl

instance instInhabited [hz : Inhabited Z] : Inhabited (FinExcept α M Z) := ⟨always hz.default⟩

-- TODO: in particular, the set of stuff with empty support is Inhabited if Z is

theorem default_apply {Z : Set M} [hz : Inhabited Z] {a : α}
  : (default : FinExcept α M Z) a = hz.default :=
  rfl

@[simp]
theorem mem_support_iff {f : FinExcept α M Z} : ∀ {a : α}, a ∈ f.support ↔ f a ∉ Z :=
  @(f.mem_support_toFun)

@[simp, norm_cast]
theorem fun_support_eq (f : FinExcept α M Z) : f ⁻¹' Zᶜ = f.support :=
  Set.ext fun _x => mem_support_iff.symm

theorem not_mem_support_iff {f : FinExcept α M Z} {a} : a ∉ f.support ↔ f a ∈ Z :=
  by simp

theorem mem_support_iff_ne {f : FinExcept α M {z}} {a} : a ∈ f.support ↔ f a ≠ z :=
  by simp

theorem not_mem_support_iff_eq {f : FinExcept α M {z}} {a} : a ∉ f.support ↔ f a = z :=
  by simp

theorem ext_iff' {f g : FinExcept α M Z} [hZ : Subsingleton Z]
  : f = g ↔ f.support = g.support ∧ ∀ x ∈ f.support, f x = g x :=
  ⟨fun h => h ▸ ⟨rfl, fun _ _ => rfl⟩, fun ⟨h₁, h₂⟩ =>
    ext fun a => by
      classical
      exact if h : a ∈ f.support then h₂ a h else by
        have hf : f a ∈ Z := not_mem_support_iff.mp h
        have hg : g a ∈ Z := by rwa [h₁, not_mem_support_iff] at h
        exact Z.subsingleton_coe.mp hZ hf hg⟩

-- TODO: Subsingleton Z -> f.support = ∅ -> g.support = ∅ -> f = g

-- TODO: i.e. the set of stuff with empty support is a Subsingleton

theorem support_eq_empty_iff_eq_default
  {f : FinExcept α M Z} [hZ : Inhabited Z] [hZ' : Subsingleton Z]
  : f.support = ∅ ↔ f = default :=
  by
    have h : ∀z, z ∈ Z ↔ z = hZ.default := λz => ⟨
      λhz => Z.subsingleton_coe.mp hZ' hz (by simp),
      λhz => by simp [hz]⟩
    simp [Finset.ext_iff, DFunLike.ext_iff, default_apply, h]

theorem support_nonempty_iff_ne_default {f : FinExcept α M Z} [Inhabited Z] [Subsingleton Z]
  : f.support.Nonempty ↔ f ≠ default := by
  simp only [support_eq_empty_iff_eq_default, Finset.nonempty_iff_ne_empty, Ne]

theorem card_support_eq_zero_iff_eq_default {f : FinExcept α M Z} [Inhabited Z] [Subsingleton Z]
  : card f.support = 0 ↔ f = default := by simp [support_eq_empty_iff_eq_default]

instance instDecidableEq {Z : Set M} [DecidableEq α] [DecidableEq M] [Subsingleton Z]
  : DecidableEq (FinExcept α M Z)
  := fun f g => decidable_of_iff (f.support = g.support ∧ ∀ a ∈ f.support, f a = g a) ext_iff'.symm

theorem support_subset_iff {s : Set α} {f : FinExcept α M Z} :
    ↑f.support ⊆ s ↔ ∀ a ∉ s, f a ∈ Z := by
  simp only [Set.subset_def, mem_coe, mem_support_iff]; exact forall_congr' fun a => not_imp_comm

theorem support_subset_iff_eq {s : Set α} {f : FinExcept α M {z}} :
    ↑f.support ⊆ s ↔ ∀ a ∉ s, f a = z := by
  simp only [Set.subset_def, mem_coe, mem_support_iff]; exact forall_congr' fun a => not_imp_comm

-- TODO: this can actually be made computable, where membership in `Z` is...
/-- Given `Finite α`, `equivFunOnFinite` is the `Equiv` between `WhereFin α β p` and `α → β`.
  (All functions on a finite type are finitely supported.) -/
@[simps]
noncomputable def equivFunOnFinite [Finite α] : (FinExcept α M Z) ≃ (α → M) where
  toFun := (⇑)
  invFun f := mk (f ⁻¹' Zᶜ).toFinite.toFinset f fun _a => Set.Finite.mem_toFinset _
  left_inv _f := ext fun _x => rfl
  right_inv _f := rfl

@[simp]
theorem equivFunOnFinite_symm_coe {α} [Finite α] (f : FinExcept α M Z)
  : equivFunOnFinite.symm f = f :=
  equivFunOnFinite.symm_apply_apply f

/--
If `α` has a unique term, `FinExcept α β Z` is equivalent to `β`.
-/
@[simps!]
noncomputable def _root_.Equiv.finExceptUnique {ι : Type*} [Unique ι] : (FinExcept ι M Z) ≃ M :=
  FinExcept.equivFunOnFinite.trans (Equiv.funUnique ι M)

@[ext]
theorem unique_ext [Unique α] {f g : FinExcept α M Z} (h : f default = g default) : f = g :=
  ext fun a => by rwa [Unique.eq_default a]

theorem unique_ext_iff [Unique α] {f g : FinExcept α M Z} : f = g ↔ f default = g default :=
  ⟨fun h => h ▸ rfl, unique_ext⟩

def cast (hZ : Z = Z') (f : FinExcept α M Z) : FinExcept α M Z' where
  support := f.support
  toFun := f.toFun
  mem_support_toFun := hZ ▸ f.mem_support_toFun

def cast' (hZ : ∀x, x ∈ Z ↔ x ∈ Z') (f : FinExcept α M Z) : FinExcept α M Z' := cast (Set.ext hZ) f

theorem cast'_eq_cast (hZ : ∀x, x ∈ Z ↔ x ∈ Z') (f : FinExcept α M Z)
  : cast' hZ f = cast (Set.ext hZ) f := rfl

@[simp]
theorem toFun_cast {hZ : Z = Z'} {f : FinExcept α M Z} : (cast hZ f).toFun = f.toFun :=
  by rfl

@[simp]
theorem toFun_cast' {hZ : ∀x, x ∈ Z ↔ x ∈ Z'} {f : FinExcept α M Z}
  : (cast' hZ f).toFun = f.toFun :=
  by rfl

@[simp]
theorem coe_cast {hZ : Z = Z'} {f : FinExcept α M Z} : ((cast hZ f) : α → M) = (f : α → M) :=
  by rfl

@[simp]
theorem coe_cast' {hZ : ∀x, x ∈ Z ↔ x ∈ Z'} {f : FinExcept α M Z}
  : ((cast' hZ f) : α → M) = (f : α → M) :=
  by rfl

@[simp]
theorem support_cast {hZ : Z = Z'} {f : FinExcept α M Z} : (cast hZ f).support = f.support :=
  by rfl

@[simp]
theorem support_cast' {hZ : ∀x, x ∈ Z ↔ x ∈ Z'} {f : FinExcept α M Z}
  : (cast' hZ f).support = f.support :=
  by rfl

@[simp]
theorem cast_apply {hZ : Z = Z'} {f : FinExcept α M Z} {a : α} : (cast hZ f) a = f a :=
  by rfl

@[simp]
theorem cast'_apply {hZ : ∀x, x ∈ Z ↔ x ∈ Z'} {f : FinExcept α M Z} {a : α}
  : (cast' hZ f) a = f a :=
  by rfl

def of_subset [DecidablePred (· ∈ Z')] (hZ : Z ⊆ Z') (f : FinExcept α M Z) : FinExcept α M Z'
    where
  support := f.support.filter (f · ∉ Z')
  toFun := f
  mem_support_toFun a := by
    simp only [mem_filter, mem_support_iff, and_iff_right_iff_imp, not_imp_not]
    exact @hZ (f a)

@[simp]
theorem toFun_of_subset [DecidablePred (· ∈ Z')] {hZ : Z ⊆ Z'} {f : FinExcept α M Z}
  : (of_subset hZ f).toFun = f.toFun :=
  by rfl

@[simp]
theorem coe_of_subset [DecidablePred (· ∈ Z')] {hZ : Z ⊆ Z'} {f : FinExcept α M Z}
  : ((of_subset hZ f) : α → M) = (f : α → M) :=
  by rfl

@[simp]
theorem of_subset_apply [DecidablePred (· ∈ Z')] {hZ : Z ⊆ Z'} {f : FinExcept α M Z} {a : α}
  : (of_subset hZ f) a = f a :=
  by rfl

theorem support_of_subset [DecidablePred (· ∈ Z')] {hZ : Z ⊆ Z'} {f : FinExcept α M Z}
  : (of_subset hZ f).support = f.support.filter (f · ∉ Z') :=
  by rfl

end Basic

-- TODO: Top lemmas

-- TODO: Bot lemmas

-- TODO: Zero lemmas

-- TODO: One lemmas

-- TODO: Option lemmas
