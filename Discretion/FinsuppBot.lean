/- Adapted from https://github.com/leanprover-community/mathlib4/blob/b856377d9cf6945a16d9abeaf713bcd10ea0d2db/Mathlib/Data/Finsupp/Defs.lean -/

import Discretion.OrderSupport

import Mathlib.Data.Set.Finite

open Finset Function

/-- `FinsuppBot α M`, denoted `α →ᴮ M`, is the type of functions `f : α → M` such that
  `f x = ⊥` for all but finitely many `x`. -/
structure FinsuppBot (α : Type*) (M : Type*) [Bot M] where
  /-- The support of a finitely supported function (aka `FinsuppBot`). -/
  support : Finset α
  /-- The underlying function of a bundled finitely supported function (aka `FinsuppBot`). -/
  toFun : α → M
  /-- The witness that the support of a `FinsuppBot` is indeed the exact locus where its
  underlying function is not `⊥`. -/
  mem_support_toFun : ∀ a, a ∈ support ↔ toFun a ≠ ⊥


@[inherit_doc]
infixr:25 " →ᴮ " => FinsuppBot

namespace FinsuppBot

section Basic

variable [Bot M]

instance instFunLike : FunLike (α →ᴮ M) α M :=
  ⟨toFun, by
    rintro ⟨s, f, hf⟩ ⟨t, g, hg⟩ (rfl : f = g)
    congr
    ext a
    exact (hf _).trans (hg _).symm⟩

/-- Helper instance for when there are too many metavariables to apply the `DFunLike` instance
directly. -/
instance instCoeFun : CoeFun (α →ᴮ M) fun _ => α → M :=
  inferInstance

@[ext]
theorem ext {f g : α →ᴮ M} (h : ∀ a, f a = g a) : f = g :=
  DFunLike.ext _ _ h

@[simp, norm_cast]
theorem coe_mk (f : α → M) (s : Finset α) (h : ∀ a, a ∈ s ↔ f a ≠ ⊥) : ⇑(⟨s, f, h⟩ : α →ᴮ M) = f :=
  rfl

instance instBot : Bot (α →ᴮ M) :=
  ⟨⟨∅, ⊥, fun _ => ⟨fun h ↦ (not_mem_empty _ h).elim, fun H => (H rfl).elim⟩⟩⟩

@[simp, norm_cast] lemma coe_bot : ⇑(⊥ : α →ᴮ M) = ⊥ := rfl

theorem bot_apply {a : α} : (⊥ : α →ᴮ M) a = ⊥ :=
  rfl

@[simp]
theorem support_bot : (⊥ : α →ᴮ M).support = ∅ :=
  rfl

instance instInhabited : Inhabited (α →ᴮ M) :=
  ⟨⊥⟩

@[simp]
theorem mem_support_iff {f : α →ᴮ M} : ∀ {a : α}, a ∈ f.support ↔ f a ≠ ⊥ :=
  @(f.mem_support_toFun)

@[simp, norm_cast]
theorem fun_support_eq (f : α →ᴮ M) : Function.supSupport f = f.support :=
  Set.ext fun _x => mem_support_iff.symm

theorem not_mem_support_iff {f : α →ᴮ M} {a} : a ∉ f.support ↔ f a = ⊥ :=
  not_iff_comm.1 mem_support_iff.symm

@[simp, norm_cast]
theorem coe_eq_bot {f : α →ᴮ M} : (f : α → M) = ⊥ ↔ f = ⊥ := by rw [← coe_bot, DFunLike.coe_fn_eq]

theorem ext_iff' {f g : α →ᴮ M} : f = g ↔ f.support = g.support ∧ ∀ x ∈ f.support, f x = g x :=
  ⟨fun h => h ▸ ⟨rfl, fun _ _ => rfl⟩, fun ⟨h₁, h₂⟩ =>
    ext fun a => by
      classical
      exact if h : a ∈ f.support then h₂ a h else by
        have hf : f a = ⊥ := not_mem_support_iff.1 h
        have hg : g a = ⊥ := by rwa [h₁, not_mem_support_iff] at h
        rw [hf, hg]⟩

@[simp]
theorem support_eq_empty {f : α →ᴮ M} : f.support = ∅ ↔ f = ⊥ :=
  by simp [Finset.ext_iff, DFunLike.ext_iff]

theorem support_nonempty_iff {f : α →ᴮ M} : f.support.Nonempty ↔ f ≠ ⊥ := by
  simp only [support_eq_empty, Finset.nonempty_iff_ne_empty, Ne]

theorem card_support_eq_zero {f : α →ᴮ M} : card f.support = 0 ↔ f = ⊥ := by simp

instance instDecidableEq [DecidableEq α] [DecidableEq M] : DecidableEq (α →ᴮ M) := fun f g =>
  decidable_of_iff (f.support = g.support ∧ ∀ a ∈ f.support, f a = g a) ext_iff'.symm

theorem support_subset_iff {s : Set α} {f : α →ᴮ M} :
    ↑f.support ⊆ s ↔ ∀ a ∉ s, f a = ⊥ := by
  simp only [Set.subset_def, mem_coe, mem_support_iff]; exact forall_congr' fun a => not_imp_comm

-- TODO: this can actually be made computable!
/-- Given `Finite α`, `equivFunOnFinite` is the `Equiv` between `α →ᴮ β` and `α → β`.
  (All functions on a finite type are finitely supported.) -/
@[simps]
noncomputable def equivFunOnFinite [Finite α] : (α →ᴮ M) ≃ (α → M) where
  toFun := (⇑)
  invFun f := mk (Function.supSupport f).toFinite.toFinset f fun _a => Set.Finite.mem_toFinset _
  left_inv _f := ext fun _x => rfl
  right_inv _f := rfl

@[simp]
theorem equivFunOnFinite_symm_coe {α} [Finite α] (f : α →ᴮ M) : equivFunOnFinite.symm f = f :=
  equivFunOnFinite.symm_apply_apply f

/--
If `α` has a unique term, the type of finitely supported functions `α →ᴮ β` is equivalent to `β`.
-/
@[simps!]
noncomputable def _root_.Equiv.finsuppBotUnique {ι : Type*} [Unique ι] : (ι →ᴮ M) ≃ M :=
  FinsuppBot.equivFunOnFinite.trans (Equiv.funUnique ι M)

@[ext]
theorem unique_ext [Unique α] {f g : α →ᴮ M} (h : f default = g default) : f = g :=
  ext fun a => by rwa [Unique.eq_default a]

theorem unique_ext_iff [Unique α] {f g : α →ᴮ M} : f = g ↔ f default = g default :=
  ⟨fun h => h ▸ rfl, unique_ext⟩

end Basic

/-! ### Declarations about `single` -/

section Single

-- TODO: weaken a bit later...
variable [Bot M] [DecidableEq α] [DecidableEq β] [DecidableEq M] {a a' : α} {b : M}

/-- `single a b` is the finitely supported function with value `b` at `a` and ⊥ otherwise. -/
-- NOTE: we flipped the inequality here to get defeq w/ Function.update
def single (a : α) (b : M) : α →ᴮ M
    where
  support := if b = ⊥ then ∅ else {a}
  toFun x := if x = a then b else ⊥
  mem_support_toFun a' := by split <;> simp [*]

theorem single_apply : single a b x = if x = a then b else ⊥ := rfl

theorem single_apply_left {f : α → β} (hf : Function.Injective f) (x z : α) (y : M) :
    single (f x) y (f z) = single x y z := by classical simp only [single_apply, hf.eq_iff]

@[simp]
theorem single_eq_same : (single a b : α →ᴮ M) a = b := by simp [single_apply]

-- TODO: flip inequality
@[simp]
theorem single_eq_of_ne (h : a ≠ a') : (single a b : α →ᴮ M) a' = ⊥
  := by simp [single_apply, h.symm]

theorem single_eq_update [DecidableEq α] (a : α) (b : M) :
    ⇑(single a b) = Function.update (⊥ : _) a b := by funext x; simp [update, single]

@[simp]
theorem single_bot (a : α) : (single a ⊥ : α →ᴮ M) = ⊥ :=
  DFunLike.coe_injective <| by
    classical simpa only [single_eq_update, coe_bot] using Function.update_eq_self a (⊥ : α → M)

theorem single_of_single_apply (a a' : α) (b : M) :
    single a ((single a' b) a) = single a' (single a' b) a := by
  classical
  rw [single_apply, single_apply]
  ext
  split_ifs with h
  · rw [h]
  · rw [bot_apply, single_apply, ite_self]

theorem support_single_ne_bot (a : α) (hb : b ≠ ⊥) : (single a b).support = {a} :=
  if_neg hb

theorem support_single_subset : (single a b).support ⊆ {a} := by
  classical show ite _ _ _ ⊆ _; split_ifs <;> [exact empty_subset _; exact Subset.refl _]

theorem single_apply_mem (x) : single a b x ∈ ({⊥, b} : Set M) := by
  rcases em (a = x) with (rfl | hx) <;> [simp; simp [single_eq_of_ne hx]]

theorem range_single_subset : Set.range (single a b) ⊆ {⊥, b} :=
  Set.range_subset_iff.2 single_apply_mem

/-- `FinsuppBot.single a b` is injective in `b`. For the statement that it is injective in `a`, see
`FinsuppBot.single_left_injective` -/
theorem single_injective (a : α) : Function.Injective (single a : M → α →ᴮ M) := fun b₁ b₂ eq => by
  have : (single a b₁ : α →ᴮ M) a = (single a b₂ : α →ᴮ M) a := by rw [eq]
  rwa [single_eq_same, single_eq_same] at this

theorem single_apply_eq_bot {a x : α} {b : M} : single a b x = ⊥ ↔ x = a → b = ⊥ := by
  simp [single_apply]

theorem single_apply_ne_bot {a x : α} {b : M} : single a b x ≠ ⊥ ↔ x = a ∧ b ≠ ⊥ := by
  simp [single_apply_eq_bot]

theorem mem_support_single (a a' : α) (b : M) : a ∈ (single a' b).support ↔ a = a' ∧ b ≠ ⊥ := by
  simp [single_apply_eq_bot, not_or]

theorem eq_single_iff {f : α →ᴮ M} {a b} : f = single a b ↔ f.support ⊆ {a} ∧ f a = b := by
  refine' ⟨fun h => h.symm ▸ ⟨support_single_subset, single_eq_same⟩, _⟩
  rintro ⟨h, rfl⟩
  ext x
  by_cases hx : a = x <;> simp only [hx, single_eq_same, single_eq_of_ne, Ne, not_false_iff]
  exact not_mem_support_iff.1 (mt (fun hx => (mem_singleton.1 (h hx)).symm) hx)

theorem single_eq_single_iff (a₁ a₂ : α) (b₁ b₂ : M) :
    single a₁ b₁ = single a₂ b₂ ↔ a₁ = a₂ ∧ b₁ = b₂ ∨ b₁ = ⊥ ∧ b₂ = ⊥ := by
  constructor
  · intro eq
    by_cases h : a₁ = a₂
    · refine' Or.inl ⟨h, _⟩
      rwa [h, (single_injective a₂).eq_iff] at eq
    · rw [DFunLike.ext_iff] at eq
      have h₁ := eq a₁
      have h₂ := eq a₂
      simp only [single_eq_same, single_eq_of_ne h, single_eq_of_ne (Ne.symm h)] at h₁ h₂
      exact Or.inr ⟨h₁, h₂.symm⟩
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · rfl
    · rw [single_bot, single_bot]

/-- `Finsupp.single a b` is injective in `a`. For the statement that it is injective in `b`, see
`Finsupp.single_injective` -/
theorem single_left_injective (h : b ≠ ⊥) : Function.Injective fun a : α => single a b :=
  fun _a _a' H => (((single_eq_single_iff _ _ _ _).mp H).resolve_right fun hb => h hb.1).left

theorem single_left_inj (h : b ≠ ⊥) : single a b = single a' b ↔ a = a' :=
  (single_left_injective h).eq_iff

theorem support_single_ne_bot' (i : α) (h : b ≠ ⊥) : (single i b).support ≠ ⊥ := by
  simpa only [support_single_ne_bot _ h] using singleton_ne_empty _

theorem support_single_disjoint {b' : M} (hb : b ≠ ⊥) (hb' : b' ≠ ⊥) {i j : α} :
    Disjoint (single i b).support (single j b').support ↔ i ≠ j := by
  rw [support_single_ne_bot _ hb, support_single_ne_bot _ hb', disjoint_singleton]

@[simp]
theorem single_eq_bot : single a b = ⊥ ↔ b = ⊥ := by simp [DFunLike.ext_iff, single_apply]

theorem single_swap (a₁ a₂ : α) (b : M) : single a₁ b a₂ = single a₂ b a₁ := by
  simp only [single_apply, eq_comm]

theorem unique_single [Unique α] (x : α →ᴮ M) : x = single default (x default) :=
  ext <| Unique.forall_iff.2 single_eq_same.symm

@[simp]
theorem unique_single_eq_iff [Unique α] {b' : M} : single a b = single a' b' ↔ b = b' := by
  rw [unique_ext_iff, Unique.eq_default a, Unique.eq_default a', single_eq_same, single_eq_same]

theorem support_eq_singleton {f : α →ᴮ M} {a : α} :
    f.support = {a} ↔ f a ≠ ⊥ ∧ f = single a (f a) :=
  ⟨fun h =>
    ⟨mem_support_iff.1 <| h.symm ▸ Finset.mem_singleton_self a,
      eq_single_iff.2 ⟨subset_of_eq h, rfl⟩⟩,
    fun h => h.2.symm ▸ support_single_ne_bot _ h.1⟩

theorem support_eq_singleton' {f : α →ᴮ M} {a : α} :
    f.support = {a} ↔ ∃ b ≠ ⊥, f = single a b :=
  ⟨fun h =>
    let h := support_eq_singleton.1 h
    ⟨_, h.1, h.2⟩,
    fun ⟨_b, hb, hf⟩ => hf.symm ▸ support_single_ne_bot _ hb⟩

theorem card_support_eq_one {f : α →ᴮ M} : card f.support = 1 ↔ ∃ a, f a ≠ ⊥ ∧ f = single a (f a) :=
  by simp only [card_eq_one, support_eq_singleton]

theorem card_support_eq_one' {f : α →ᴮ M} :
    card f.support = 1 ↔ ∃ a, ∃ b ≠ ⊥, f = single a b := by
  simp only [card_eq_one, support_eq_singleton']

theorem support_subset_singleton {f : α →ᴮ M} {a : α} : f.support ⊆ {a} ↔ f = single a (f a) :=
  ⟨fun h => eq_single_iff.mpr ⟨h, rfl⟩, fun h => (eq_single_iff.mp h).left⟩

theorem support_subset_singleton' {f : α →ᴮ M} {a : α} : f.support ⊆ {a} ↔ ∃ b, f = single a b :=
  ⟨fun h => ⟨f a, support_subset_singleton.mp h⟩, fun ⟨b, hb⟩ => by
    rw [hb, support_subset_singleton, single_eq_same]⟩

theorem card_support_le_one [Nonempty α] {f : α →ᴮ M} :
    card f.support ≤ 1 ↔ ∃ a, f = single a (f a) := by
  simp only [card_le_one_iff_subset_singleton, support_subset_singleton]

theorem card_support_le_one' [Nonempty α] {f : α →ᴮ M} :
    card f.support ≤ 1 ↔ ∃ a b, f = single a b := by
  simp only [card_le_one_iff_subset_singleton, support_subset_singleton']

end Single

instance instNontrivial [Bot M] [Nonempty α] [Nontrivial M] : Nontrivial (α →ᴮ M) := by
  classical
  inhabit α
  rcases exists_ne (⊥ : M) with ⟨x, hx⟩
  exact nontrivial_of_ne (single default x) ⊥ (mt single_eq_bot.1 hx)


/-! ### Declarations about `update` -/


section Update

variable [Bot M] [DecidableEq α] [DecidableEq β] [DecidableEq M]
  (f : α →ᴮ M) (a : α) (b : M) (i : α)

/-- Replace the value of a `α →₀ M` at a given point `a : α` by a given value `b : M`.
If `b = 0`, this amounts to removing `a` from the `Finsupp.support`.
Otherwise, if `a` was not in the `Finsupp.support`, it is added to it.

This is the finitely-supported version of `Function.update`. -/
def update (f : α →ᴮ M) (a : α) (b : M) : α →ᴮ M where
  support := if b = ⊥ then f.support.erase a else insert a f.support
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
theorem bot_update : update ⊥ a b = single a b := by
  ext
  rw [single_eq_update]
  rfl

theorem support_update :
    support (f.update a b) = if b = ⊥ then f.support.erase a else insert a f.support := rfl

@[simp]
theorem support_update_bot : support (f.update a ⊥) = f.support.erase a := by
  simp [update]

variable {b}

theorem support_update_ne_bot (h : b ≠ ⊥) :
    support (f.update a b) = insert a f.support := by simp [update, h]

theorem support_update_subset :
    support (f.update a b) ⊆ insert a f.support := by
  rw [support_update]
  split_ifs
  · exact (erase_subset _ _).trans (subset_insert _ _)
  · rfl

theorem update_comm (f : α →ᴮ M) {a₁ a₂ : α} (h : a₁ ≠ a₂) (m₁ m₂ : M) :
    update (update f a₁ m₁) a₂ m₂ = update (update f a₂ m₂) a₁ m₁ :=
  DFunLike.coe_injective <| Function.update_comm h _ _ _

@[simp] theorem update_idem (f : α →ᴮ M) (a : α) (b c : M) :
    update (update f a b) a c = update f a c :=
  DFunLike.coe_injective <| Function.update_idem _ _ _

end Update

/-! ### Declarations about `erase` -/

section Erase

variable [DecidableEq α] [DecidableEq M] [Bot M]

/--
`erase a f` is the finitely supported function equal to `f` except at `a` where it is equal to `⊥`.
If `a` is not in the support of `f` then `erase a f = f`.
-/
def erase (a : α) (f : α →ᴮ M) : α →ᴮ M where
  support := f.support.erase a
  toFun a' := if a' = a then ⊥ else f a'
  mem_support_toFun a' := by
    rw [mem_erase, mem_support_iff]; dsimp
    split_ifs with h
    exact ⟨fun H _ => H.1 h, fun H => (H rfl).elim⟩
    exact and_iff_right h

@[simp]
theorem support_erase [DecidableEq α] {a : α} {f : α →ᴮ M} :
  (f.erase a).support = f.support.erase a := rfl

@[simp]
theorem erase_same {a : α} {f : α →ᴮ M} : (f.erase a) a = ⊥ := by
  simp only [erase, coe_mk, ite_true]

@[simp]
theorem erase_ne {a a' : α} {f : α →ᴮ M} (h : a' ≠ a) : (f.erase a) a' = f a' := by
  simp only [erase, coe_mk, h, ite_false]

theorem erase_apply {a a' : α} {f : α →ᴮ M} :
    f.erase a a' = if a' = a then ⊥ else f a' := by
  rw [erase, coe_mk]

@[simp]
theorem erase_single {a : α} {b : M} : erase a (single a b) = ⊥ := by
  ext s; by_cases hs : s = a
  · rw [hs, erase_same]
    rfl
  · rw [erase_ne hs]
    exact single_eq_of_ne (Ne.symm hs)

theorem erase_single_ne {a a' : α} {b : M} (h : a ≠ a') : erase a (single a' b) = single a' b := by
  ext s; by_cases hs : s = a
  · rw [hs, erase_same, single_eq_of_ne h.symm]
  · rw [erase_ne hs]

@[simp]
theorem erase_of_not_mem_support {f : α →ᴮ M} {a} (haf : a ∉ f.support) : erase a f = f := by
  ext b; by_cases hab : b = a
  · rwa [hab, erase_same, eq_comm, ← not_mem_support_iff]
  · rw [erase_ne hab]

@[simp, nolint simpNF] -- Porting note: simpNF linter claims simp can prove this, it can not
theorem erase_bot (a : α) : erase a (⊥ : α →ᴮ M) = ⊥ := by
  rw [← support_eq_empty, support_erase, support_bot, erase_empty]

theorem erase_eq_update_bot (f : α →ᴮ M) (a : α) : f.erase a = update f a ⊥ := by
  ext; simp [erase_apply, update_apply]

-- The name matches `Finset.erase_insert_of_ne`
theorem erase_update_of_ne (f : α →ᴮ M) {a a' : α} (ha : a ≠ a') (b : M) :
    erase a (update f a' b) = update (erase a f) a' b := by
  rw [erase_eq_update_bot, erase_eq_update_bot, update_comm _ ha]

-- not `simp` as `erase_of_not_mem_support` can prove this
theorem erase_idem (f : α →ᴮ M) (a : α) :
    erase a (erase a f) = erase a f := by
  rw [erase_eq_update_bot, erase_eq_update_bot, update_idem]

@[simp] theorem update_erase_eq_update (f : α →ᴮ M) (a : α) (b : M) :
    update (erase a f) a b = update f a b := by
  rw [erase_eq_update_bot, update_idem]

@[simp] theorem erase_update_eq_erase (f : α →ᴮ M) (a : α) (b : M) :
    erase a (update f a b) = erase a f := by
  rw [erase_eq_update_bot, erase_eq_update_bot, update_idem]

end Erase

/-! ### Declarations about `onFinset` -/

section OnFinset

variable [DecidableEq α] [DecidableEq M] [Bot M]

/-- `FinsuppBot.onFinset s f hf` is the finsupp function representing `f` restricted to the finset
`s`. The function must be `⊥` outside of `s`. Use this when the set needs to be filtered anyways,
otherwise a better set representation is often available. -/
def onFinset (s : Finset α) (f : α → M) (hf : ∀ a, f a ≠ ⊥ → a ∈ s) : α →ᴮ M where
  support := s.filter (f · ≠ ⊥)
  toFun := f
  mem_support_toFun := by simpa

@[simp]
theorem onFinset_apply {s : Finset α} {f : α → M} {hf a} : (onFinset s f hf : α →ᴮ M) a = f a :=
  rfl

@[simp]
theorem support_onFinset_subset {s : Finset α} {f : α → M} {hf} :
    (onFinset s f hf).support ⊆ s := by
  classical convert filter_subset (f · ≠ ⊥) s

-- @[simp] -- Porting note (#10618): simp can prove this
theorem mem_support_onFinset {s : Finset α} {f : α → M} (hf : ∀ a : α, f a ≠ ⊥ → a ∈ s) {a : α} :
    a ∈ (onFinset s f hf).support ↔ f a ≠ ⊥ := by
  rw [mem_support_iff, onFinset_apply]

theorem support_onFinset {s : Finset α} {f : α → M}
    (hf : ∀ a : α, f a ≠ ⊥ → a ∈ s) :
    (onFinset s f hf).support = s.filter fun a => f a ≠ ⊥ := rfl

end OnFinset

section OfSupportFinite

variable [Bot M]

/-- The natural `Finsupp` induced by the function `f` given that it has finite support. -/
noncomputable def ofSupportFinite (f : α → M) (hf : (Function.supSupport f).Finite) : α →ᴮ M where
  support := hf.toFinset
  toFun := f
  mem_support_toFun _ := hf.mem_toFinset

theorem ofSupportFinite_coe {f : α → M} {hf : (Function.supSupport f).Finite} :
    (ofSupportFinite f hf : α → M) = f :=
  rfl

instance instCanLift : CanLift (α → M) (α →ᴮ M) (⇑) fun f => (Function.supSupport f).Finite where
  prf f hf := ⟨ofSupportFinite f hf, rfl⟩

end OfSupportFinite

/-! ### Declarations about `mapRange` -/


section MapRange

variable
  [DecidableEq α] [DecidableEq β]
  [DecidableEq M] [DecidableEq N] [DecidableEq P] [Bot M] [Bot N] [Bot P]

/-- The composition of `f : M → N` and `g : α →ᴮ M` is `mapRange f hf g : α →₀ N`,
which is well-defined when `f ⊥ = ⊥`.
-/
def mapRange (f : M → N) (hf : f ⊥ = ⊥) (g : α →ᴮ M) : α →ᴮ N :=
  onFinset g.support (f ∘ g) fun a => by
    rw [mem_support_iff, not_imp_not]; exact fun H => (congr_arg f H).trans hf

@[simp]
theorem mapRange_apply {f : M → N} {hf : f ⊥ = ⊥} {g : α →ᴮ M} {a : α} :
    mapRange f hf g a = f (g a) :=
  rfl

@[simp]
theorem mapRange_bot {f : M → N} {hf : f ⊥ = ⊥} : mapRange f hf (⊥ : α →ᴮ M) = ⊥ :=
  ext fun _ => by simp only [hf, bot_apply, mapRange_apply]

@[simp]
theorem mapRange_id (g : α →ᴮ M) : mapRange id rfl g = g :=
  ext fun _ => rfl

theorem mapRange_comp (f : N → P) (hf : f ⊥ = ⊥) (f₂ : M → N) (hf₂ : f₂ ⊥ = ⊥) (h : (f ∘ f₂) ⊥ = ⊥)
    (g : α →ᴮ M) : mapRange (f ∘ f₂) h g = mapRange f hf (mapRange f₂ hf₂ g) :=
  ext fun _ => rfl

theorem support_mapRange {f : M → N} {hf : f ⊥ = ⊥} {g : α →ᴮ M} :
    (mapRange f hf g).support ⊆ g.support :=
  support_onFinset_subset

@[simp]
theorem mapRange_single {f : M → N} {hf : f ⊥ = ⊥} {a : α} {b : M} :
    mapRange f hf (single a b) = single a (f b) := by
  ext
  simp only [mapRange_apply, single_apply]
  split <;> simp [*]

theorem support_mapRange_of_injective {e : M → N} (he0 : e ⊥ = ⊥) (f : ι →ᴮ M)
    (he : Function.Injective e) : (mapRange e he0 f).support = f.support := by
  ext
  simp only [mem_support_iff, Ne, mapRange_apply]
  exact he.ne_iff' he0

end MapRange

/-! ### Declarations about `embDomain` -/


section EmbDomain

variable [DecidableEq α] [DecidableEq β] [DecidableEq M] [DecidableEq N] [Bot M] [Bot N]

/-- Given `f : α ↪ β` and `v : α →ᴮ M`, `Finsupp.embDomain f v : β →ᴮ M`
is the finitely supported function whose value at `f a : β` is `v a`.
For a `b : β` outside the range of `f`, it is `⊥`. -/
def embDomain (f : α ↪ β) (v : α →ᴮ M) : β →ᴮ M where
  support := v.support.map f
  toFun a₂ :=
    if h : a₂ ∈ v.support.map f then
      v
        (v.support.choose (fun a₁ => f a₁ = a₂)
          (by
            rcases Finset.mem_map.1 h with ⟨a, ha, rfl⟩
            exact ExistsUnique.intro a ⟨ha, rfl⟩ fun b ⟨_, hb⟩ => f.injective hb))
    else ⊥
  mem_support_toFun a₂ := by
    dsimp
    split_ifs with h
    · simp only [h, true_iff_iff, Ne]
      rw [← not_mem_support_iff, not_not]
      classical apply Finset.choose_mem
    · simp only [h, Ne, ne_self_iff_false, not_true_eq_false]

@[simp]
theorem support_embDomain (f : α ↪ β) (v : α →ᴮ M) : (embDomain f v).support = v.support.map f :=
  rfl

@[simp]
theorem embDomain_bot (f : α ↪ β) : (embDomain f ⊥ : β →ᴮ M) = ⊥ :=
  rfl

@[simp]
theorem embDomain_apply (f : α ↪ β) (v : α →ᴮ M) (a : α) : embDomain f v (f a) = v a := by
  classical
    change dite _ _ _ = _
    split_ifs with h <;> rw [Finset.mem_map' f] at h
    · refine' congr_arg (v : α → M) (f.inj' _)
      exact Finset.choose_property (fun a₁ => f a₁ = f a) _ _
    · exact (not_mem_support_iff.1 h).symm

theorem embDomain_notin_range (f : α ↪ β) (v : α →ᴮ M) (a : β) (h : a ∉ Set.range f) :
    embDomain f v a = ⊥ := by
  classical
    refine' dif_neg (mt (fun h => _) h)
    rcases Finset.mem_map.1 h with ⟨a, _h, rfl⟩
    exact Set.mem_range_self a

theorem embDomain_injective (f : α ↪ β) : Function.Injective (embDomain f : (α →ᴮ M) → β →ᴮ M) :=
  fun l₁ l₂ h => ext fun a => by simpa only [embDomain_apply] using DFunLike.ext_iff.1 h (f a)

@[simp]
theorem embDomain_inj {f : α ↪ β} {l₁ l₂ : α →ᴮ M} : embDomain f l₁ = embDomain f l₂ ↔ l₁ = l₂ :=
  (embDomain_injective f).eq_iff

@[simp]
theorem embDomain_eq_zero {f : α ↪ β} {l : α →ᴮ M} : embDomain f l = ⊥ ↔ l = ⊥ :=
  (embDomain_injective f).eq_iff' <| embDomain_bot f

theorem embDomain_mapRange (f : α ↪ β) (g : M → N) (p : α →ᴮ M) (hg : g ⊥ = ⊥) :
    embDomain f (mapRange g hg p) = mapRange g hg (embDomain f p) := by
  ext a
  by_cases h : a ∈ Set.range f
  · rcases h with ⟨a', rfl⟩
    rw [mapRange_apply, embDomain_apply, embDomain_apply, mapRange_apply]
  · rw [mapRange_apply, embDomain_notin_range, embDomain_notin_range, ← hg] <;> assumption

theorem single_of_embDomain_single (l : α →ᴮ M) (f : α ↪ β) (a : β) (b : M) (hb : b ≠ ⊥)
    (h : l.embDomain f = single a b) : ∃ x, l = single x b ∧ f x = a := by
  classical
    have h_map_support : Finset.map f l.support = {a} := by
      rw [← support_embDomain, h, support_single_ne_bot _ hb]
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

variable [Dα : DecidableEq α] [DecidableEq M]
  [DecidableEq N] [DecidableEq P] [Bot M] [Bot N] [Bot P]

/-- Given finitely supported functions `g₁ : α →ᴮ M` and `g₂ : α →ᴮ N` and function `f : M → N → P`,
`Finsupp.zipWith f hf g₁ g₂` is the finitely supported function `α →ᴮ P` satisfying
`zipWith f hf g₁ g₂ a = f (g₁ a) (g₂ a)`, which is well-defined when `f ⊥ ⊥ = ⊥`. -/
def zipWith (f : M → N → P) (hf : f ⊥ ⊥ = ⊥) (g₁ : α →ᴮ M) (g₂ : α →ᴮ N) : α →ᴮ P :=
  onFinset
    (g₁.support ∪ g₂.support)
    (fun a => f (g₁ a) (g₂ a))
    fun a (H : f _ _ ≠ ⊥) => by
      classical
      rw [mem_union, mem_support_iff, mem_support_iff, ← not_and_or]
      rintro ⟨h₁, h₂⟩; rw [h₁, h₂] at H; exact H hf

@[simp]
theorem zipWith_apply {f : M → N → P} {hf : f ⊥ ⊥ = ⊥} {g₁ : α →ᴮ M} {g₂ : α →ᴮ N} {a : α} :
    zipWith f hf g₁ g₂ a = f (g₁ a) (g₂ a) :=
  rfl

theorem support_zipWith {f : M → N → P} {hf : f ⊥ ⊥ = ⊥} {g₁ : α →ᴮ M}
    {g₂ : α →ᴮ N} : (zipWith f hf g₁ g₂).support ⊆ g₁.support ∪ g₂.support := by simp [zipWith]

@[simp]
theorem zipWith_single_single (f : M → N → P) (hf : f ⊥ ⊥ = ⊥) (a : α) (m : M) (n : N) :
    zipWith f hf (single a m) (single a n) = single a (f m n) := by
  ext a'
  rw [zipWith_apply]
  obtain rfl | ha' := eq_or_ne a a'
  · rw [single_eq_same, single_eq_same, single_eq_same]
  · rw [single_eq_of_ne ha', single_eq_of_ne ha', single_eq_of_ne ha', hf]

end ZipWith

-- TODO: lattice lore

-- TODO: discrete lattice lore

end FinsuppBot
