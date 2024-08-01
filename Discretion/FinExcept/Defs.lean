/- Adapted from https://github.com/leanprover-community/mathlib4/blob/b856377d9cf6945a16d9abeaf713bcd10ea0d2db/Mathlib/Data/Finsupp/Defs.lean -/

import Discretion.OrderSupport
import Discretion.Utils

import Mathlib.Data.Set.Finite

-- TODO: clean up doc comments... we need a better name than "zero set"

open Finset Function

/-- `FinExcept α M Z`, is the type of functions `f : α → M` such that `f x ∈ Zf x` for all but
  finitely many `x`. -/
structure FinExcept (α : Type*) (M : Type*) (Zf : α → Set M) where
  /-- The support on which this function lies outside of `Z` -/
  support : Finset α
  /-- The underlying function -/
  toFun : α → M
  /-- The witness that the support of a `FinExcept` is indeed the exact locus where its
  underlying function lies outside of `Z`. -/
  mem_support_toFun : ∀ a, a ∈ support ↔ toFun a ∉ Zf a

@[inherit_doc]
notation:25 α " →ᶠ[" Z "]" M => FinExcept α M (λ_ => Z)

@[inherit_doc]
notation:25 α " →ᶠ[[" Zf "]]" M => FinExcept α M Zf

namespace FinExcept

section Basic

variable {α : Type u} {M : Type v} {Z Z' : Set M} {Zf Zf' : α → Set M}

instance instFunLike : FunLike (α →ᶠ[[Zf]] M) α M :=
  ⟨toFun, by
    rintro ⟨s, f, hf⟩ ⟨t, g, hg⟩ (rfl : f = g)
    congr
    ext a
    exact (hf _).trans (hg _).symm⟩

/-- Helper instance for when there are too many metavariables to apply the `DFunLike` instance
directly. -/
instance instCoeFun : CoeFun (α →ᶠ[[Zf]] M) fun _ => α → M :=
  inferInstance

@[ext]
theorem ext {f g : α →ᶠ[[Zf]] M} (h : ∀ a, f a = g a) : f = g :=
  DFunLike.ext _ _ h

@[simp, norm_cast]
theorem coe_mk (f : α → M) (s : Finset α) (h : ∀ a, a ∈ s ↔ f a ∉ Zf a)
  : ⇑(⟨s, f, h⟩ : α →ᶠ[[Zf]] M) = f :=
  rfl

-- @[simp]
-- theorem support_top : (⊤ : α →ᵀ M).support = ∅ :=
--   rfl

/-- `always z` is the function with value `z` everywhere -/
def always (z : Z) : α →ᶠ[Z] M where
  support := ∅
  toFun := fun _ => z
  mem_support_toFun := by simp

theorem always_apply {z : Z} {a : α} : (always z) a = z :=
  rfl

@[simp]
theorem support_always : (always z : α →ᶠ[Z] M).support = ∅ :=
  rfl

/-- `null z` is the function with value `z` everywhere -/
def null (z : M) : α →ᶠ[{z}] M where
  support := ∅
  toFun := fun _ => z
  mem_support_toFun := by simp

theorem null_apply {z : M} {a : α} : (null z) a = z :=
  rfl

instance instTop [Top M] : Top (α →ᶠ[{⊤}] M) where
  top := null ⊤

@[simp, norm_cast] lemma coe_top [Top M] : ⇑(⊤ : α →ᶠ[{⊤}] M) = ⊤ := rfl

theorem top_apply [Top M] {a : α} : (⊤ : α →ᶠ[{⊤}] M) a = ⊤ :=
  rfl

instance instBot [Bot M] : Bot (α →ᶠ[{⊥}] M) where
  bot := null ⊥

@[simp, norm_cast] lemma coe_bot [Bot M] : ⇑(⊥ : α →ᶠ[{⊥}] M) = ⊥ := rfl

theorem bot_apply [Bot M] {a : α} : (⊥ : α →ᶠ[{⊥}] M) a = ⊥ :=
  rfl

instance instZero [Zero M] : Zero (α →ᶠ[{0}] M) where
  zero := null 0

@[simp, norm_cast] lemma coe_zero [Zero M] : ⇑(0 : α →ᶠ[{0}] M) = 0 := rfl

theorem zero_apply [Zero M] {a : α} : (0 : α →ᶠ[{0}] M) a = 0 :=
  rfl

instance instOne [One M] : One (α →ᶠ[{1}] M) where
  one := null 1

@[simp, norm_cast] lemma coe_one [One M] : ⇑(1 : α →ᶠ[{1}] M) = 1 := rfl

theorem one_apply [One M] {a : α} : (1 : α →ᶠ[{1}] M) a = 1 :=
  rfl

@[simp]
theorem support_null : (null z : α →ᶠ[{z}] M).support = ∅ :=
  rfl

theorem always_eq_null {z : M} {z' : ({z} : Set M)}
  : (always z' : α →ᶠ[{z}] M) = null z := by
  cases z' with | mk z' p =>
    ext a
    cases p
    simp [always_apply, null_apply]

instance instInhabited [hz : ∀a, Inhabited (Zf a)] : Inhabited (α →ᶠ[[Zf]] M) := ⟨{
  support := ∅,
  toFun := fun a => (hz a).default,
  mem_support_toFun := by simp
}⟩

-- TODO: in particular, the set of stuff with empty support is Inhabited if Z is

@[simp, norm_cast] lemma coe_default [Inhabited M] : ⇑(default : α →ᶠ[{default}] M) = default := rfl

theorem default_apply {Z : Set M} [hz : Inhabited Z] {a : α}
  : (default : α →ᶠ[Z] M) a = hz.default :=
  rfl

@[simp]
theorem mem_support_iff {f : α →ᶠ[[Zf]] M} : ∀ {a : α}, a ∈ f.support ↔ f a ∉ Zf a :=
  @(f.mem_support_toFun)

-- TODO: generalize to families
@[simp, norm_cast]
theorem fun_support_eq (f : α →ᶠ[Z] M) : (f ⁻¹' Z)ᶜ = f.support :=
  Set.ext fun _x => mem_support_iff.symm

theorem not_mem_support_iff {f : α →ᶠ[[Zf]] M} {a} : a ∉ f.support ↔ f a ∈ Zf a :=
  by simp

theorem mem_support_iff_ne {f : α →ᶠ[{z}] M} {a} : a ∈ f.support ↔ f a ≠ z :=
  by simp

theorem not_mem_support_iff_eq {f : α →ᶠ[{z}] M} {a} : a ∉ f.support ↔ f a = z :=
  by simp

theorem ext_iff' {f g : α →ᶠ[[Zf]] M} [hZ : ∀a, Subsingleton (Zf a)]
  : f = g ↔ f.support = g.support ∧ ∀ x ∈ f.support, f x = g x :=
  ⟨fun h => h ▸ ⟨rfl, fun _ _ => rfl⟩, fun ⟨h₁, h₂⟩ =>
    ext fun a => by
      classical
      exact if h : a ∈ f.support then h₂ a h else by
        have hf : f a ∈ Zf a := not_mem_support_iff.mp h
        have hg : g a ∈ Zf a := by rwa [h₁, not_mem_support_iff] at h
        exact (Zf a).subsingleton_coe.mp (hZ a) hf hg⟩

-- TODO: Subsingleton Z -> f.support = ∅ -> g.support = ∅ -> f = g

-- TODO: i.e. the set of stuff with empty support is a Subsingleton

theorem support_eq_empty_iff_eq_default
  {f : α →ᶠ[Z] M} [hZ : Inhabited Z] [hZ' : Subsingleton Z]
  : f.support = ∅ ↔ f = default :=
  by
    have h : ∀z, z ∈ Z ↔ z = hZ.default := λz => ⟨
      λhz => Z.subsingleton_coe.mp hZ' hz (by simp),
      λhz => by simp [hz]⟩
    simp [Finset.ext_iff, DFunLike.ext_iff, default_apply, h]

theorem support_nonempty_iff_ne_default {f : α →ᶠ[Z] M} [Inhabited Z] [Subsingleton Z]
  : f.support.Nonempty ↔ f ≠ default := by
  simp only [support_eq_empty_iff_eq_default, Finset.nonempty_iff_ne_empty, Ne]

theorem card_support_eq_zero_iff_eq_default {f : α →ᶠ[Z] M} [Inhabited Z] [Subsingleton Z]
  : card f.support = 0 ↔ f = default := by simp [support_eq_empty_iff_eq_default]

theorem support_eq_empty {f : α →ᶠ[{z}] M} : f.support = ∅ ↔ f = null z :=
  support_eq_empty_iff_eq_default

theorem support_nonempty_iff {f : α →ᶠ[{z}] M} : f.support.Nonempty ↔ f ≠ null z := by
  simp only [support_eq_empty, Finset.nonempty_iff_ne_empty, Ne]

theorem card_support_eq_zero {f : α →ᶠ[{z}] M} : card f.support = 0 ↔ f = null z
  := by simp [support_eq_empty]

instance instDecidableEq [DecidableEq α] [DecidableEq M] [∀a, Subsingleton (Zf a)]
  : DecidableEq (α →ᶠ[[Zf]] M)
  := fun f g => decidable_of_iff (f.support = g.support ∧ ∀ a ∈ f.support, f a = g a) ext_iff'.symm

theorem support_subset_iff {s : Set α} {f : α →ᶠ[[Zf]] M} :
    ↑f.support ⊆ s ↔ ∀ a ∉ s, f a ∈ Zf a := by
  simp only [Set.subset_def, mem_coe, mem_support_iff]; exact forall_congr' fun a => not_imp_comm

theorem support_subset_iff_eq {s : Set α} {f : α →ᶠ[{z}] M} :
    ↑f.support ⊆ s ↔ ∀ a ∉ s, f a = z := by
  simp only [Set.subset_def, mem_coe, mem_support_iff]; exact forall_congr' fun a => not_imp_comm

-- TODO: this can actually be made computable, where membership in `Z` is...
/-- Given `Finite α`, `equivFunOnFinite` is the `Equiv` between `WhereFin α β p` and `α → β`.
  (All functions on a finite type are finitely supported.) -/
@[simps]
noncomputable def equivFunOnFinite [Finite α] : (α →ᶠ[Z] M) ≃ (α → M) where
  toFun := (⇑)
  invFun f := mk (f ⁻¹' Zᶜ).toFinite.toFinset f fun _a => Set.Finite.mem_toFinset _
  left_inv _f := ext fun _x => rfl
  right_inv _f := rfl

@[simp]
theorem equivFunOnFinite_symm_coe {α} [Finite α] (f : α →ᶠ[Z] M)
  : equivFunOnFinite.symm f = f :=
  equivFunOnFinite.symm_apply_apply f

/--
If `α` has a unique term, `FinExcept α β Z` is equivalent to `β`.
-/
@[simps!]
noncomputable def _root_.Equiv.finExceptUnique {ι : Type*} [Unique ι]
  : (FinExcept ι M (λ_ => Z)) ≃ M :=
  FinExcept.equivFunOnFinite.trans (Equiv.funUnique ι M)

@[ext]
theorem unique_ext [Unique α] {f g : α →ᶠ[[Zf]] M} (h : f default = g default) : f = g :=
  ext fun a => by rwa [Unique.eq_default a]

theorem unique_ext_iff [Unique α] {f g : α →ᶠ[[Zf]] M} : f = g ↔ f default = g default :=
  ⟨fun h => h ▸ rfl, unique_ext⟩

/--
Cast the zero set family of a `FinExcept`
-/
def cast (hZ : Zf = Zf') (f : α →ᶠ[[Zf]] M) : α →ᶠ[[Zf']] M where
  support := f.support
  toFun := f.toFun
  mem_support_toFun := hZ ▸ f.mem_support_toFun

/--
Cast the zero set of a `FinExcept`
-/
def cast_set (hZ : ∀x, x ∈ Z ↔ x ∈ Z') (f : α →ᶠ[Z] M) : α →ᶠ[Z'] M := cast (by ext; apply hZ) f

theorem cast_set_eq_cast (hZ : ∀x, x ∈ Z ↔ x ∈ Z') (f : α →ᶠ[Z] M)
  : cast_set hZ f = cast (by ext; apply hZ) f := rfl

@[simp]
theorem toFun_cast {hZ : Zf = Zf'} {f : α →ᶠ[[Zf]] M} : (cast hZ f).toFun = f.toFun :=
  by rfl

@[simp]
theorem toFun_cast_set {hZ : ∀x, x ∈ Z ↔ x ∈ Z'} {f : α →ᶠ[Z] M}
  : (cast_set hZ f).toFun = f.toFun :=
  by rfl

@[simp]
theorem coe_cast {hZ : Zf = Zf'} {f : α →ᶠ[[Zf]] M} : ((cast hZ f) : α → M) = (f : α → M) :=
  by rfl

@[simp]
theorem coe_cast_set {hZ : ∀x, x ∈ Z ↔ x ∈ Z'} {f : α →ᶠ[Z] M}
  : ((cast_set hZ f) : α → M) = (f : α → M) :=
  by rfl

@[simp]
theorem support_cast {hZ : Zf = Zf'} {f : α →ᶠ[[Zf]] M} : (cast hZ f).support = f.support :=
  by rfl

@[simp]
theorem support_cast_set {hZ : ∀x, x ∈ Z ↔ x ∈ Z'} {f : α →ᶠ[Z] M}
  : (cast_set hZ f).support = f.support :=
  by rfl

@[simp]
theorem cast_apply {hZ : Zf = Zf'} {f : α →ᶠ[[Zf]] M} {a : α} : (cast hZ f) a = f a :=
  by rfl

@[simp]
theorem cast_set_apply {hZ : ∀x, x ∈ Z ↔ x ∈ Z'} {f : α →ᶠ[Z] M} {a : α}
  : (cast_set hZ f) a = f a :=
  by rfl

-- TODO: of_subfamily variant

/--
Cast the zero set of a `FinExcept` to a superset of the zero set
-/
def of_subset [DecidablePred (· ∈ Z')] (hZ : Z ⊆ Z') (f : α →ᶠ[Z] M) : α →ᶠ[Z'] M
    where
  support := f.support.filter (f · ∉ Z')
  toFun := f
  mem_support_toFun a := by
    simp only [mem_filter, mem_support_iff, and_iff_right_iff_imp, not_imp_not]
    exact @hZ (f a)

@[simp]
theorem toFun_of_subset [DecidablePred (· ∈ Z')] {hZ : Z ⊆ Z'} {f : α →ᶠ[Z] M}
  : (of_subset hZ f).toFun = f.toFun :=
  by rfl

@[simp]
theorem coe_of_subset [DecidablePred (· ∈ Z')] {hZ : Z ⊆ Z'} {f : α →ᶠ[Z] M}
  : ((of_subset hZ f) : α → M) = (f : α → M) :=
  by rfl

@[simp]
theorem of_subset_apply [DecidablePred (· ∈ Z')] {hZ : Z ⊆ Z'} {f : α →ᶠ[Z] M} {a : α}
  : (of_subset hZ f) a = f a :=
  by rfl

theorem support_of_subset [DecidablePred (· ∈ Z')] {hZ : Z ⊆ Z'} {f : α →ᶠ[Z] M}
  : (of_subset hZ f).support = f.support.filter (f · ∉ Z') :=
  by rfl

end Basic

-- TODO: can have more generic "default" variants

/-! ### Declarations about `single` -/

section Single

variable [DecidableEq α] [DecidableEq β] [DecidableEq M] {a a' : α} {b : M}

/-- `single a b` is the finitely supported function with value `b` at `a` and `default` otherwise. -/
def single (z : M) (a : α) (b : M) : α →ᶠ[{z}] M
    where
  support := if b = z then ∅ else {a}
  toFun x := if x = a then b else z
  mem_support_toFun a' := by split <;> simp [*]

theorem single_apply : single z a b x = if x = a then b else z := rfl

theorem single_apply_left {f : α → β} (hf : Function.Injective f) (a c : α) (b : M) :
    single z (f a) b (f c) = single z a b c := by classical simp only [single_apply, hf.eq_iff]

@[simp]
theorem single_eq_same : (single z a b : α →ᶠ[{z}] M) a = b := by simp [single_apply]

-- TODO: flip inequality
@[simp]
theorem single_eq_of_ne (h : a ≠ a') : (single z a b : α →ᶠ[{z}] M) a' = z
  := by simp [single_apply, h.symm]

theorem single_eq_update (z : M) (a : α) (b : M) :
    ⇑(single z a b) = Function.update (λ_ => z) a b := by funext x; simp [update, single]

@[simp]
theorem single_null (z : M) (a : α) : (single z a z : α →ᶠ[{z}] M) = null z :=
  DFunLike.coe_injective <| by
    classical simpa only [single_eq_update] using Function.update_eq_self a (null z : α → M)

-- theorem single_of_single_apply (z: M) (a a' : α) (b : M) :
--     single z a ((single z a' b) a) = single z a' (single z a' b) a := by
--   classical
--   rw [single_apply, single_apply]
--   ext
--   split_ifs with h
--   · rw [h]
--   · rw [top_apply, single_apply, ite_self]

theorem support_single_ne_null {z : M} (a : α) (hb : b ≠ z) : (single z a b).support = {a} :=
  if_neg hb

theorem support_single_subset : (single z a b).support ⊆ {a} := by
  classical show ite _ _ _ ⊆ _; split_ifs <;> [exact empty_subset _; exact Subset.refl _]

theorem single_apply_mem (x) : single z a b x ∈ ({z, b} : Set M) := by
  rcases em (a = x) with (rfl | hx) <;> simp; simp [single_eq_of_ne hx]

theorem range_single_subset : Set.range (single z a b) ⊆ {z, b} :=
  Set.range_subset_iff.2 single_apply_mem

/-- `FinExcept.single z a b` is injective in `b`. For the statement that it is injective in `a`, see
`FinExcept.single_left_injective` -/
theorem single_injective (z : M) (a : α)
  : Function.Injective (single z a : M → α →ᶠ[{z}] M) := fun b₁ b₂ eq => by
  have : (single z a b₁ : α →ᶠ[{z}] M) a = (single z a b₂ : α →ᶠ[{z}] M) a := by rw [eq]
  rwa [single_eq_same, single_eq_same] at this

theorem single_apply_eq_null {a x : α} {b : M} : single z a b x = z ↔ x = a → b = z := by
  simp [single_apply]

theorem single_apply_ne_null {a x : α} {b : M} : single z a b x ≠ z ↔ x = a ∧ b ≠ z := by
  simp [single_apply_eq_null]

theorem mem_support_single (z : M) (a a' : α) (b : M)
  : a ∈ (single z a' b).support ↔ a = a' ∧ b ≠ z := by
  simp [single_apply_eq_null, not_or]

theorem eq_single_iff {f : α →ᶠ[{z}] M} {a b}
  : f = single z a b ↔ f.support ⊆ {a} ∧ f a = b := by
  refine ⟨fun h => h.symm ▸ ⟨support_single_subset, single_eq_same⟩, ?x⟩
  rintro ⟨h, rfl⟩
  ext x
  by_cases hx : a = x <;> simp only [hx, single_eq_same, single_eq_of_ne, Ne, not_false_iff]
  exact not_mem_support_iff.1 (mt (fun hx => (mem_singleton.1 (h hx)).symm) hx)

theorem single_eq_single_iff (z : M) (a₁ a₂ : α) (b₁ b₂ : M) :
    single z a₁ b₁ = single z a₂ b₂ ↔ a₁ = a₂ ∧ b₁ = b₂ ∨ b₁ = z ∧ b₂ = z := by
  constructor
  · intro eq
    by_cases h : a₁ = a₂
    · refine Or.inl ⟨h, ?x⟩
      rwa [h, (single_injective z a₂).eq_iff] at eq
    · rw [DFunLike.ext_iff] at eq
      have h₁ := eq a₁
      have h₂ := eq a₂
      simp only [single_eq_same, single_eq_of_ne h, single_eq_of_ne (Ne.symm h)] at h₁ h₂
      exact Or.inr ⟨h₁, h₂.symm⟩
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · rfl
    · rw [single_null, single_null]

/-- `Finsupp.single a b` is injective in `a`. For the statement that it is injective in `b`, see
`Finsupp.single_injective` -/
theorem single_left_injective (h : b ≠ z) : Function.Injective fun a : α => single z a b :=
  fun _a _a' H => (((single_eq_single_iff _ _ _ _ _).mp H).resolve_right fun hb => h hb.1).left

theorem single_left_inj (h : b ≠ z) : single z a b = single z a' b ↔ a = a' :=
  (single_left_injective h).eq_iff

theorem support_single_ne_bot (i : α) (h : b ≠ z) : (single z i b).support ≠ ⊥ := by
  simpa only [support_single_ne_null _ h] using singleton_ne_empty _

theorem support_single_disjoint {b' : M} (hb : b ≠ z) (hb' : b' ≠ z) {i j : α} :
    Disjoint (single z i b).support (single z j b').support ↔ i ≠ j := by
  rw [support_single_ne_null _ hb, support_single_ne_null _ hb', disjoint_singleton]

@[simp]
theorem single_eq_null : single z a b = (null z) ↔ b = z
  := by simp [DFunLike.ext_iff, single_apply, null_apply]

theorem single_swap (z : M) (a₁ a₂ : α) (b : M) : single z a₁ b a₂ = single z a₂ b a₁ := by
  simp only [single_apply, eq_comm]

theorem unique_single [Unique α] (x : α →ᶠ[{z}] M) : x = single z default (x default) :=
  ext <| Unique.forall_iff.2 single_eq_same.symm

@[simp]
theorem unique_single_eq_iff [Unique α] {b' : M} : single z a b = single z a' b' ↔ b = b' := by
  rw [unique_ext_iff, Unique.eq_default a, Unique.eq_default a', single_eq_same, single_eq_same]

theorem support_eq_singleton {f : α →ᶠ[{z}] M} {a : α} :
    f.support = {a} ↔ f a ≠ z ∧ f = single z a (f a) :=
  ⟨fun h =>
    ⟨mem_support_iff_ne.1 <| h.symm ▸ Finset.mem_singleton_self a,
      eq_single_iff.2 ⟨subset_of_eq h, rfl⟩⟩,
    fun h => h.2.symm ▸ support_single_ne_null _ h.1⟩

theorem support_eq_singleton' {f : α →ᶠ[{z}] M} {a : α} :
    f.support = {a} ↔ ∃ b ≠ z, f = single z a b :=
  ⟨fun h =>
    let h := support_eq_singleton.1 h
    ⟨_, h.1, h.2⟩,
    fun ⟨_b, hb, hf⟩ => hf.symm ▸ support_single_ne_null _ hb⟩

theorem card_support_eq_one {f : α →ᶠ[{z}] M}
  : card f.support = 1 ↔ ∃ a, f a ≠ z ∧ f = single z a (f a) :=
  by simp only [card_eq_one, support_eq_singleton]

theorem card_support_eq_one' {f : α →ᶠ[{z}] M} :
    card f.support = 1 ↔ ∃ a, ∃ b ≠ z, f = single z a b := by
  simp only [card_eq_one, support_eq_singleton']

theorem support_subset_singleton {f : α →ᶠ[{z}] M} {a : α}
  : f.support ⊆ {a} ↔ f = single z a (f a) :=
  ⟨fun h => eq_single_iff.mpr ⟨h, rfl⟩, fun h => (eq_single_iff.mp h).left⟩

theorem support_subset_singleton' {f : α →ᶠ[{z}] M} {a : α}
  : f.support ⊆ {a} ↔ ∃ b, f = single z a b :=
  ⟨fun h => ⟨f a, support_subset_singleton.mp h⟩, fun ⟨b, hb⟩ => by
    rw [hb, support_subset_singleton, single_eq_same]⟩

theorem card_support_le_one [Nonempty α] {f : α →ᶠ[{z}] M} :
    card f.support ≤ 1 ↔ ∃ a, f = single z a (f a) := by
  simp only [card_le_one_iff_subset_singleton, support_subset_singleton]

theorem card_support_le_one' [Nonempty α] {f : α →ᶠ[{z}] M} :
    card f.support ≤ 1 ↔ ∃ a b, f = single z a b := by
  simp only [card_le_one_iff_subset_singleton, support_subset_singleton']

end Single


/-! ### Declarations about `update` -/


section Update

variable
  {Z : Set M} [DecidablePred (· ∈ Z)] {z : M}
  {Zf : α → Set M} [∀a, DecidablePred (· ∈ Zf a)]
  [DecidableEq α] [DecidableEq β] [DecidableEq M]
  (f : α →ᶠ[[Zf]] M) (fz : α →ᶠ[{z}] M) (a : α) (b : M) (i : α)

/-- Replace the value of a `α →ᶠ[Z] M` at a given point `a : α` by a given value `b : M`.
If `b ∈ Z`, this amounts to removing `a` from the `Finsupp.support`.
Otherwise, if `a` was not in the `Finsupp.support`, it is added to it.

This is the finitely-supported version of `Function.update`. -/
def update (f : α →ᶠ[[Zf]] M) (a : α) (b : M) : α →ᶠ[[Zf]] M where
  support := if b ∈ Zf a then f.support.erase a else insert a f.support
  toFun := Function.update f a b
  mem_support_toFun i := by
    classical
    rw [Function.update]
    simp only [eq_rec_constant, dite_eq_ite, ne_eq]
    split_ifs with hb ha ha <;>
      try simp only [*, not_false_iff, iff_true, not_true, iff_false]
    · rw [Finset.mem_erase]
      simp
    · rw [Finset.mem_erase]
      simp [ha]
    · rw [Finset.mem_insert]
      simp [ha]
    · rw [Finset.mem_insert]
      simp [ha]

@[simp, norm_cast]
theorem coe_update [DecidableEq α] : (f.update a b : α → M) = Function.update f a b := rfl

@[simp]
theorem update_self : f.update a (f a) = f := by ext; simp

@[simp]
theorem null_update : update (null z) a b = single z a b := by
  ext
  rw [single_eq_update]
  rfl

theorem support_update :
    support (f.update a b) = if b ∈ Zf a then f.support.erase a else insert a f.support := rfl

@[simp]
theorem support_update_null : support (fz.update a z) = fz.support.erase a := by
  simp [update]

variable {b}

theorem support_update_not_mem (h : b ∉ Zf a) :
    support (f.update a b) = insert a f.support := by simp [update, h]

theorem support_update_ne_null (h : b ≠ z) :
    support (fz.update a b) = insert a fz.support := by simp [update, h]

theorem support_update_subset :
    support (f.update a b) ⊆ insert a f.support := by
  rw [support_update]
  split_ifs
  · exact (erase_subset _ _).trans (subset_insert _ _)
  · rfl

theorem update_comm (f : α →ᶠ[[Zf]] M) {a₁ a₂ : α} (h : a₁ ≠ a₂) (m₁ m₂ : M) :
    update (update f a₁ m₁) a₂ m₂ = update (update f a₂ m₂) a₁ m₁ :=
  DFunLike.coe_injective <| Function.update_comm h _ _ _

@[simp] theorem update_idem (f : α →ᶠ[[Zf]] M) (a : α) (b c : M) :
    update (update f a b) a c = update f a c :=
  DFunLike.coe_injective <| Function.update_idem _ _ _

end Update

/-! ### Declarations about `erase` -/

section Erase

variable {Zf : α → Set M} [hZ : ∀a, Inhabited (Zf a)] [∀a, DecidablePred (· ∈ Zf a)]
  {z : M} [DecidableEq α] [DecidableEq M]

/--
`erase a f` is the finitely supported function equal to `f` except at `a` where it is equal to
`default`. If `a` is not in the support of `f` then `erase a f = f`.
-/
def erase (a : α) (f : α →ᶠ[[Zf]] M) : α →ᶠ[[Zf]] M where
  support := f.support.erase a
  toFun a' := if a' = a then (hZ a).default else f a'
  mem_support_toFun a' := by
    rw [mem_erase, mem_support_iff]; dsimp
    split_ifs with h
    exact ⟨fun H _ => H.1 h, fun H => (H (h ▸ (hZ a).default.property)).elim⟩
    exact and_iff_right h

@[simp]
theorem support_erase [DecidableEq α] {a : α} {f : α →ᶠ[{z}] M} :
  (f.erase a).support = f.support.erase a := rfl

@[simp]
theorem erase_same {a : α} {f : α →ᶠ[[Zf]] M} : (f.erase a) a = (hZ a).default := by
  simp only [erase, coe_mk, ite_true]

theorem erase_same_eq {a : α} {f : α →ᶠ[{z}] M} : (f.erase a) a = z := erase_same

@[simp]
theorem erase_ne {a a' : α} {f : α →ᶠ[{z}] M} (h : a' ≠ a) : (f.erase a) a' = f a' := by
  simp only [erase, coe_mk, h, ite_false]

theorem erase_apply {a a' : α} {f : α →ᶠ[[Zf]] M} :
  f.erase a a' = if a' = a then ↑(hZ a).default else f a' := by rw [erase, coe_mk]

theorem erase_apply_eq {a a' : α} {f : α →ᶠ[{z}] M} : f.erase a a' = if a' = a then z else f a'
  := erase_apply

@[simp]
theorem erase_single {a : α} {b : M} : erase a (single z a b) = null z := by
  ext s; by_cases hs : s = a
  · rw [hs, erase_same]
    rfl
  · rw [erase_ne hs]
    exact single_eq_of_ne (Ne.symm hs)

theorem erase_single_ne {a a' : α} {b : M} (h : a ≠ a') : erase a (single z a' b) = single z a' b
  := by
  ext s; by_cases hs : s = a
  · rw [hs, erase_same_eq, single_eq_of_ne h.symm]
  · rw [erase_ne hs]

-- TODO: all this requires is that Zf a is always a subsingleton
@[simp]
theorem erase_of_not_mem_support {f : α →ᶠ[{z}] M} {a} (haf : a ∉ f.support) : erase a f = f := by
  ext b; by_cases hab : b = a
  · rwa [hab, erase_same_eq, eq_comm, ← not_mem_support_iff_eq]
  · rw [erase_ne hab]

@[simp, nolint simpNF] -- Porting note: simpNF linter claims simp can prove this, it can not
theorem erase_null (a : α) : erase a (null z : α →ᶠ[{z}] M) = null z := by
  rw [← support_eq_empty, support_erase, support_null, erase_empty]

theorem erase_eq_update_null (f : α →ᶠ[{z}] M) (a : α) : f.erase a = update f a z := by
  ext; simp [erase_apply, update_apply]

theorem erase_eq_update_default (f : α →ᶠ[[Zf]] M) (a : α) : f.erase a = update f a (hZ a).default
  := by ext; simp [erase_apply, update_apply]

-- The name matches `Finset.erase_insert_of_ne`
theorem erase_update_of_ne (f : α →ᶠ[[Zf]] M) {a a' : α} (ha : a ≠ a') (b : M) :
    erase a (update f a' b) = update (erase a f) a' b := by
  rw [erase_eq_update_default, erase_eq_update_default, update_comm _ ha]

-- not `simp` as `erase_of_not_mem_support` can prove this
theorem erase_idem (f : α →ᶠ[{z}] M) (a : α) :
    erase a (erase a f) = erase a f := by
  rw [erase_eq_update_null, erase_eq_update_null, update_idem]

@[simp] theorem update_erase_eq_update (f : α →ᶠ[{z}] M) (a : α) (b : M) :
    update (erase a f) a b = update f a b := by
  rw [erase_eq_update_null, update_idem]

@[simp] theorem erase_update_eq_erase (f : α →ᶠ[{z}] M) (a : α) (b : M) :
    erase a (update f a b) = erase a f := by
  rw [erase_eq_update_null, erase_eq_update_null, update_idem]

end Erase

/-! ### Declarations about `onFinset` -/

section OnFinset

-- TODO: generalize to families

-- TODO: add restriction

variable
  {Zf : α → Set M} [∀a, DecidablePred (· ∈ Zf a)]
  [DecidableEq α] [DecidableEq M] [Top M]

/-- `FinsuppTop.onFinset s f hf` is the finsupp function representing `f` restricted to the finset
`s`. The function must satisfy `∀x ∉ s, f s ∈ Zf x`. Use this when the set needs to be filtered
anyways, otherwise a better set representation is often available. -/
def onFinset (Zf : α → Set M) [∀a, DecidablePred (· ∈ Zf a)]
  (s : Finset α) (f : α → M) (hf : ∀ a, f a ∉ Zf a → a ∈ s) : α →ᶠ[[Zf]] M where
  support := s.filter (λx => f x ∉ Zf x)
  toFun := f
  mem_support_toFun := by simpa

@[simp]
theorem onFinset_apply {s : Finset α} {f : α → M} {hf a}
  : (onFinset Zf s f hf : α →ᶠ[[Zf]] M) a = f a :=
  rfl

@[simp]
theorem support_onFinset_subset {s : Finset α} {f : α →ᶠ[[Zf]] M} {hf} :
    (onFinset Zf s f hf).support ⊆ s := by
  classical convert filter_subset (λx => f x ∉ Zf x) s

-- @[simp] -- Porting note (#10618): simp can prove this
theorem mem_support_onFinset {s : Finset α} {f : α → M} (hf : ∀ a : α, f a ∉ Zf a → a ∈ s) {a : α} :
    a ∈ (onFinset Zf s f hf).support ↔ f a ∉ Zf a := by
  rw [mem_support_iff, onFinset_apply]

theorem support_onFinset {s : Finset α} {f : α → M}
    (hf : ∀ a : α, f a ∉ Zf a → a ∈ s) :
    (onFinset Zf s f hf).support = s.filter (λx => f x ∉ Zf x) := rfl

end OnFinset

section OfSupportFinite

/-- The natural `Finsupp` induced by the function `f` given that it has finite support. -/
noncomputable def ofSupportFinite (Z : Set M) (f : α → M) (hf : ((f ⁻¹' Z)ᶜ).Finite) : α →ᶠ[Z] M where
  support := hf.toFinset
  toFun := f
  mem_support_toFun _ := hf.mem_toFinset

theorem ofSupportFinite_coe {Z} {f : α → M} {hf : ((f ⁻¹' Z)ᶜ).Finite} :
    (ofSupportFinite Z f hf : α → M) = f :=
  rfl

instance instCanLift : CanLift (α → M) (α →ᶠ[Z] M) (⇑) fun f => ((f ⁻¹' Z)ᶜ).Finite where
  prf f hf := ⟨ofSupportFinite Z f hf, rfl⟩

end OfSupportFinite

/-! ### Declarations about `mapRange` -/


section MapRange

-- TODO: generalize to families

-- TODO: standardize notation

variable {Z : Set M} {Z' : Set N} {Z'' : Set P}
  [DecidablePred (· ∈ Z)] [DecidablePred (· ∈ Z')] [DecidablePred (· ∈ Z'')]
  [DecidableEq α] [DecidableEq β]
  [DecidableEq M] [DecidableEq N] [DecidableEq P]

/-- The composition of `f : M → N` and `g : α →ᶠ[Z] M` is `mapRange f hf g : α →ᶠ[Z'] N`,
which is well-defined when `∀z ∈ Z, f z ∈ Z'`.
-/
def mapRange (Z : Set M) (Z' : Set N) [DecidablePred (· ∈ Z')]
  (f : M → N) (hf : ∀z ∈ Z, f z ∈ Z') (g : α →ᶠ[Z] M) : α →ᶠ[Z'] N :=
  onFinset _ g.support (f ∘ g) λ a => by
    rw [mem_support_iff, not_imp_not, comp_apply]
    exact λ H => hf _ H

@[simp]
theorem mapRange_apply {f : M → N} {hf : ∀z ∈ Z, f z ∈ Z'} {g : α →ᶠ[Z] M} {a : α} :
    mapRange Z Z' f hf g a = f (g a) :=
  rfl

@[simp]
theorem mapRange_null {f : M → N} {hf}
  : mapRange {z} {z'} f hf (null z : α →ᶠ[{z}] M) = null z' :=
  ext λ _ => hf _ rfl

@[simp]
theorem mapRange_id (g : α →ᶠ[Z] M) : mapRange Z Z id (λ_ hz => hz) g = g :=
  ext fun _ => rfl

theorem mapRange_comp (f : N → P) (hf) (f₂ : M → N) (hf₂) (h)
    (g : α →ᶠ[Z] M) : mapRange _ _ (f ∘ f₂) h g = mapRange _ Z'' f hf (mapRange _ Z' f₂ hf₂ g) :=
  ext fun _ => rfl

theorem support_mapRange {f : M → N} {hf} {g : α →ᶠ[Z] M} :
    (mapRange _ Z' f hf g).support ⊆ g.support :=
  by simp [mapRange, support_onFinset]

@[simp]
theorem mapRange_single {f : M → N} {hf} {a : α} {b : M} :
    mapRange {z} {z'} f hf (single z a b) = single z' a (f b) := by
  ext
  simp only [mapRange_apply, single_apply]
  split
  · rfl
  · exact hf _ rfl

theorem support_mapRange_of_injective {e : M → N} (he0) (f : ι →ᶠ[{z}] M)
    (he : Function.Injective e) : (mapRange _ {z'} e he0 f).support = f.support := by
  ext
  simp only [mem_support_iff, Ne, mapRange_apply, Set.mem_singleton_iff]
  exact he.ne_iff' (he0 _ rfl)

/-- The composition of `f : M → N` and `g : α →ᶠ[{z}] M` is `mapRange f hf g : α →ᶠ[{z'}] N`,
which is well-defined when `f z = z'`.
-/
def mapRange' (f : M → N) (hf : f z = z') (g : α →ᶠ[{z}] M) : α →ᶠ[{z'}] N :=
  mapRange {z} {z'} f (by intro x hx; cases hx; exact hf) g

theorem mapRange'_eq_mapRange {f : M → N} {hf} {g : α →ᶠ[{z}] M} :
    mapRange' f hf g = mapRange {z} {z'} f (by intro x hx; cases hx; exact hf) g :=
  rfl

theorem mapRange'_apply {f : M → N} {hf : f z = z'} {g : α →ᶠ[{z}] M} {a : α} :
    mapRange' f hf g a = f (g a) :=
  rfl

@[simp]
theorem mapRange'_id (g : α →ᶠ[{z}] M) : mapRange' id rfl g = g :=
  ext fun _ => rfl

theorem mapRange'_comp (f : N → P) (hf : f z' = z'') (f₂ : M → N) (hf₂ : f₂ z = z') (h)
    (g : α →ᶠ[{z}] M) : mapRange' (f ∘ f₂) h g = mapRange' f hf (mapRange' f₂ hf₂ g) :=
  ext fun _ => rfl

theorem support_mapRange' {f : M → N} {hf : f z = z'} {g : α →ᶠ[{z}] M} :
    (mapRange' f hf g).support ⊆ g.support :=
  by simp [mapRange', mapRange, support_onFinset]

end MapRange

/-! ### Declarations about `embDomain` -/


section EmbDomain

variable [DecidableEq α] [DecidableEq β] [DecidableEq M] [DecidableEq N]

/-- Given `f : α ↪ β` and `v : α →ᶠ[{z}] M`, `Finsupp.embDomain f v : β →ᶠ[{z}] M`
is the finitely supported function whose value at `f a : β` is `v a`.
For a `b : β` outside the range of `f`, it is `z`. -/
def embDomain (f : α ↪ β) (v : α →ᶠ[{z}] M) : β →ᶠ[{z}] M where
  support := v.support.map f
  toFun a₂ :=
    if h : a₂ ∈ v.support.map f then
      v
        (v.support.choose (fun a₁ => f a₁ = a₂)
          (by
            rcases Finset.mem_map.1 h with ⟨a, ha, rfl⟩
            exact ExistsUnique.intro a ⟨ha, rfl⟩ fun b ⟨_, hb⟩ => f.injective hb))
    else z
  mem_support_toFun a₂ := by
    dsimp
    split_ifs with h
    · simp only [h, true_iff_iff, Ne]
      rw [← not_mem_support_iff, not_not]
      classical apply Finset.choose_mem
    · simp [h]

@[simp]
theorem support_embDomain (f : α ↪ β) (v : α →ᶠ[{z}] M)
  : (embDomain f v).support = v.support.map f :=
  rfl

@[simp]
theorem embDomain_null (f : α ↪ β) : (embDomain f (null z) : β →ᶠ[{z}] M) = null z :=
  rfl

@[simp]
theorem embDomain_apply (f : α ↪ β) (v : α →ᶠ[{z}] M) (a : α) : embDomain f v (f a) = v a := by
  classical
    change dite _ _ _ = _
    split_ifs with h <;> rw [Finset.mem_map' f] at h
    · refine congr_arg (v : α → M) (f.inj' ?x)
      exact Finset.choose_property (fun a₁ => f a₁ = f a) _ _
    · exact (not_mem_support_iff.1 h).symm

theorem embDomain_notin_range (f : α ↪ β) (v : α →ᶠ[{z}] M) (a : β) (h : a ∉ Set.range f) :
    embDomain f v a = z := by
  classical
    refine dif_neg (mt (fun h => ?x) h)
    rcases Finset.mem_map.1 h with ⟨a, _h, rfl⟩
    exact Set.mem_range_self a

theorem embDomain_injective (f : α ↪ β)
  : Function.Injective (embDomain f : (α →ᶠ[{z}] M) → β →ᶠ[{z}] M) :=
  fun l₁ l₂ h => ext fun a => by simpa only [embDomain_apply] using DFunLike.ext_iff.1 h (f a)

@[simp]
theorem embDomain_inj {f : α ↪ β} {l₁ l₂ : α →ᶠ[{z}] M} : embDomain f l₁ = embDomain f l₂ ↔ l₁ = l₂ :=
  (embDomain_injective f).eq_iff

@[simp]
theorem embDomain_eq_null {f : α ↪ β} {l : α →ᶠ[{z}] M} : embDomain f l = null z ↔ l = null z :=
  (embDomain_injective f).eq_iff' <| embDomain_null f

theorem embDomain_mapRange' (f : α ↪ β) (g : M → N) (p : α →ᶠ[{z}] M) (hg : g z = z') :
    embDomain f (mapRange' g hg p) = mapRange' g hg (embDomain f p) := by
  ext a
  by_cases h : a ∈ Set.range f
  · rcases h with ⟨a', rfl⟩
    rw [mapRange'_apply, embDomain_apply, embDomain_apply, mapRange'_apply]
  · rw [mapRange'_apply, embDomain_notin_range, embDomain_notin_range, ← hg] <;> assumption

theorem single_of_embDomain_single (l : α →ᶠ[{z}] M) (f : α ↪ β) (a : β) (b : M) (hb : b ≠ z)
    (h : l.embDomain f = single z a b) : ∃ x, l = single z x b ∧ f x = a := by
  classical
    have h_map_support : Finset.map f l.support = {a} := by
      rw [← support_embDomain, h, support_single_ne_null _ hb]
    have ha : a ∈ Finset.map f l.support := by simp only [h_map_support, Finset.mem_singleton]
    rcases Finset.mem_map.1 ha with ⟨c, _hc₁, hc₂⟩
    use c
    constructor
    · ext d
      rw [← embDomain_apply f l, h]
      by_cases h_cases : c = d
      · simp only [Eq.symm h_cases, hc₂, single_eq_same]
      · rw [single_apply, single_apply, if_neg, if_neg (Ne.symm h_cases)]
        by_contra hfd
        exact h_cases (f.injective (hc₂.trans hfd.symm))
    · exact hc₂

end EmbDomain

/-! ### Declarations about `zipWith` -/


section ZipWith

variable {ZM : α → Set M} {ZN : α → Set N} {ZP : α → Set P} [∀a, DecidablePred (· ∈ ZP a)]
  [Dα : DecidableEq α] [DecidableEq M]
  [DecidableEq N] [DecidableEq P] [Top M] [Top N] [Top P]

/-- Given finitely supported functions `g₁ : α →ᶠ[ZM] M` and `g₂ : α →ᶠ[ZN] N` and
function `f : M → N → P`, `Finsupp.zipWith f hf g₁ g₂` is the finitely supported function
`α →ᵀ P` satisfying `zipWith f hf g₁ g₂ a = f (g₁ a) (g₂ a)`, which is well-defined when
`∀m ∈ ZM, ∀n ∈ ZN, f m n ∈ ZP`. -/
def zipWith (ZP : α → Set P) [∀a, DecidablePred (· ∈ ZP a)] (f : M → N → P)
  (hf : ∀a, ∀m ∈ ZM a, ∀n ∈ ZN a, f m n ∈ ZP a) (g₁ : α →ᶠ[[ZM]] M) (g₂ : α →ᶠ[[ZN]] N)
  : α →ᶠ[[ZP]] P :=
  onFinset _
    (g₁.support ∪ g₂.support)
    (fun a => f (g₁ a) (g₂ a))
    fun a (H : f _ _ ∉ ZP a) => by
      classical
      rw [mem_union, mem_support_iff, mem_support_iff, ← not_and_or]
      rintro ⟨h₁, h₂⟩; exact H (hf _ _ h₁ _ h₂)

@[simp]
theorem zipWith_apply {f : M → N → P} {hf} {g₁ : α →ᶠ[[ZM]] M} {g₂ : α →ᶠ[[ZN]] N} {a : α} :
    zipWith ZP f hf g₁ g₂ a = f (g₁ a) (g₂ a) :=
  rfl

theorem support_zipWith {f : M → N → P} {hf} {g₁ : α →ᶠ[[ZM]] M} {g₂ : α →ᶠ[[ZN]] N}
  : (zipWith ZP f hf g₁ g₂).support ⊆ g₁.support ∪ g₂.support := by simp [zipWith, support_onFinset]

/-- Given finitely supported functions `g₁ : α →ᶠ[{m}] M` and `g₂ : α →ᶠ[{n}] N` and
function `f : M → N → P`, `Finsupp.zipWith' f hf g₁ g₂` is the finitely supported function
`α →ᵀ P` satisfying `zipWith' f hf g₁ g₂ a = f (g₁ a) (g₂ a)`, which is well-defined when
`f m n = p`. -/
def zipWith' (f : M → N → P) (hf : f m n = p) (g₁ : α →ᶠ[{m}] M) (g₂ : α →ᶠ[{n}] N) : α →ᶠ[{p}] P :=
  onFinset _
    (g₁.support ∪ g₂.support)
    (fun a => f (g₁ a) (g₂ a))
    fun a (H : f (g₁ a) (g₂ a) ∉ {p}) => by
      classical
      rw [mem_union, mem_support_iff, mem_support_iff, ← not_and_or]
      rintro ⟨h₁, h₂⟩; simp only [Set.mem_singleton_iff] at *; rw [h₁, h₂, hf] at H;
      exact H (Set.mem_singleton p)

@[simp]
theorem zipWith'_apply {f : M → N → P} {hf : f m n = p} {g₁ : α →ᶠ[{m}] M} {g₂ : α →ᶠ[{n}] N} {a : α}
  : zipWith' f hf g₁ g₂ a = f (g₁ a) (g₂ a) :=
  rfl

theorem zipWith'_eq_zipWith {f : M → N → P} {hf : f m n = p} {g₁ : α →ᶠ[{m}] M} {g₂ : α →ᶠ[{n}] N} :
    zipWith' f hf g₁ g₂ = zipWith _ f (by intro _ m hm n hn; cases hm; cases hn; exact hf) g₁ g₂
    := rfl

theorem support_zipWith' {f : M → N → P} {hf : f m n = p} {g₁ : α →ᶠ[{m}] M} {g₂ : α →ᶠ[{n}] N}
  : (zipWith' f hf g₁ g₂).support ⊆ g₁.support ∪ g₂.support := by simp [zipWith', support_onFinset]

@[simp]
theorem zipWith'_single_single (f : M → N → P) (hf : f zm zn = zp) (a : α) (m : M) (n : N) :
    zipWith' f hf (single zm a m) (single zn a n) = single zp a (f m n) := by
  ext a'
  rw [zipWith'_apply]
  obtain rfl | ha' := eq_or_ne a a'
  · rw [single_eq_same, single_eq_same, single_eq_same]
  · rw [single_eq_of_ne ha', single_eq_of_ne ha', single_eq_of_ne ha', hf]

@[simp]
theorem zipWith_single_single (f : M → N → P) (hf) (a : α) (m : M) (n : N) :
    zipWith _ f hf (single zm a m) (single zn a n) = single zp a (f m n) := by
    rw [← zipWith'_eq_zipWith, zipWith'_single_single]
    exact hf a _ rfl _ rfl

end ZipWith

end FinExcept

-- TODO: Top lemmas

-- TODO: Bot lemmas

-- TODO: Zero lemmas

-- TODO: One lemmas

-- TODO: Option lemmas
