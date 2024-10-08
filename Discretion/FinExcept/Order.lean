-- File based on https://github.com/leanprover-community/mathlib4/blob/b856377d9cf6945a16d9abeaf713bcd10ea0d2db/Mathlib/Data/Finsupp/Order.lean#L48-L49

import Discretion.FinExcept.Defs

open Finset

namespace FinExcept

section LE
variable [LE α] {f g : ι →ᶠ[[Zf]] α}

instance instLEFinExcept : LE (ι →ᶠ[[Zf]] α) :=
  ⟨fun f g => ∀ i, f i ≤ g i⟩

lemma le_def : f ≤ g ↔ ∀ i, f i ≤ g i := Iff.rfl

@[simp, norm_cast] lemma coe_le_coe : ⇑f ≤ g ↔ f ≤ g := Iff.rfl

/-- The order on `FinExcept`s over a partial order embeds into the order on functions -/
def orderEmbeddingToFun : (ι →ᶠ[[Zf]] α) ↪o (ι → α) where
  toFun f := f
  inj' f g h :=
    FinExcept.ext fun i => by
      dsimp at h
      rw [h]
  map_rel_iff' := coe_le_coe

@[simp]
theorem orderEmbeddingToFun_apply {f : ι →ᶠ[[Zf]] α} {i : ι} : orderEmbeddingToFun f i = f i :=
  rfl

end LE

section Preorder
variable {Zf : ι → Set α} [Preorder α] {f g : ι →ᶠ[[Zf]] α}

instance preorder : Preorder (ι →ᶠ[[Zf]] α) :=
  { instLEFinExcept with
    le_refl := fun f i => le_rfl
    le_trans := fun f g h hfg hgh i => (hfg i).trans (hgh i) }

lemma lt_def : f < g ↔ f ≤ g ∧ ∃ i, f i < g i := Pi.lt_def
@[simp, norm_cast] lemma coe_lt_coe : ⇑f < g ↔ f < g := Iff.rfl

lemma coe_mono : Monotone (toFun : (ι →ᶠ[[Zf]] α) → ι → α) := fun _ _ ↦ id

lemma coe_strictMono : Monotone (FinExcept.toFun : (ι →ᶠ[[Zf]] α) → ι → α) := fun _ _ ↦ id

end Preorder

instance partialorder [PartialOrder α] : PartialOrder (ι →ᶠ[[Zf]] α) :=
  { FinExcept.preorder with le_antisymm :=
      fun _f _g hfg hgf => ext fun i => (hfg i).antisymm (hgf i) }

-- TODO: these can be generalized to nonsingletons if the zero sets themselves are semilattices
-- TODO: need to add an instance that says partially ordered subsingletons are complete lattices
-- TODO: should every subsingleton be equipped with a partial order, for that matter? linear?
--       this would have to be a low-priority instance to avoid conflict... as should the above,
--       for that matter

instance semilatticeInf [DecidableEq ι]
  {Zf : ι → Set α} [hZ: ∀a, Subsingleton (Zf a)] [∀a, DecidablePred (· ∈ Zf a)] [SemilatticeInf α]
  : SemilatticeInf (ι →ᶠ[[Zf]] α) :=
  { partialorder with
    inf := zipWith Zf (· ⊓ ·) (λa m hm n hn => by
      simp only
      rw [(Zf a).subsingleton_coe.mp (hZ a) hm hn, inf_idem]
      exact hn)
    inf_le_left := fun _f _g _i => inf_le_left
    inf_le_right := fun _f _g _i => inf_le_right
    le_inf := fun _f _g _i h1 h2 s => le_inf (h1 s) (h2 s) }

@[simp]
theorem inf_apply [SemilatticeInf α] [DecidableEq α] [DecidableEq ι]
  {i : ι} {f g : ι →ᶠ[{z}] α} : (f ⊓ g) i = f i ⊓ g i :=
  rfl

instance semilatticeSup [DecidableEq ι]
  {Zf : ι → Set α} [hZ: ∀a, Subsingleton (Zf a)] [∀a, DecidablePred (· ∈ Zf a)] [SemilatticeSup α]
  : SemilatticeSup (ι →ᶠ[[Zf]] α) :=
  { partialorder with
    sup := zipWith Zf (· ⊔ ·) (λa m hm n hn => by
      simp only
      rw [(Zf a).subsingleton_coe.mp (hZ a) hm hn, sup_idem]
      exact hn)
    le_sup_left := fun _f _g _i => le_sup_left
    le_sup_right := fun _f _g _i => le_sup_right
    sup_le := fun _f _g _h hf hg i => sup_le (hf i) (hg i) }

@[simp]
theorem sup_apply [SemilatticeSup α] [DecidableEq α] [DecidableEq ι]
  {i : ι} {f g : ι →ᶠ[{z}] α} : (f ⊔ g) i = f i ⊔ g i :=
  rfl

instance lattice [DecidableEq ι]
  {Zf : ι → Set α} [∀a, Subsingleton (Zf a)] [∀a, DecidablePred (· ∈ Zf a)] [Lattice α]
  : Lattice (ι →ᶠ[[Zf]] α) :=
  { semilatticeInf, semilatticeSup with }

-- TODO: distributivity lore? completion lore?

section Lattice

variable [DecidableEq ι] [DecidableEq α] [Lattice α] (f g : ι →ᶠ[{z}] α)

theorem support_inf_union_support_sup : (f ⊓ g).support ∪ (f ⊔ g).support = f.support ∪ g.support :=
  coe_injective <| compl_injective <| by ext; simp [inf_eq_and_sup_eq_iff]

theorem support_sup_union_support_inf : (f ⊔ g).support ∪ (f ⊓ g).support = f.support ∪ g.support :=
  (union_comm _ _).trans <| support_inf_union_support_sup _ _

end Lattice

section OrderTop
variable [LE α] [OrderTop α]

instance orderTop : OrderTop (ι →ᶠ[{⊤}] α) where
  le_top := by simp [le_def, top_apply]

theorem le_iff_top' (f g : ι →ᶠ[{⊤}] α) {s : Finset ι} (hf : g.support ⊆ s)
  : f ≤ g ↔ ∀ i ∈ s, f i ≤ g i :=
  ⟨fun h s _hs => h s, fun h s => by
    classical exact
        if H : s ∈ g.support then h s (hf H) else (not_mem_support_iff.1 H).symm ▸ le_top⟩

theorem le_iff_top (f g : ι →ᶠ[{⊤}] α) : f ≤ g ↔ ∀ i ∈ g.support, f i ≤ g i :=
  le_iff_top' f g <| Subset.refl _

instance decidableLETop [DecidableRel (@LE.le α _)]
  : DecidableRel (@LE.le (ι →ᶠ[{⊤}] α) _) := fun f g =>
  decidable_of_iff _ (le_iff_top f g).symm

variable [DecidableEq ι]

@[simp]
theorem le_single_iff_top [DecidableEq α] {i : ι} {x : α} {f : ι →ᶠ[{⊤}] α}
  : f ≤ single ⊤ i x ↔ f i ≤ x :=
  (le_iff_top' _ _ support_single_subset).trans <| by simp

end OrderTop

section Preorder
variable [DecidableEq α] [Preorder α] [OrderTop α]

instance decidableLTTop [DecidableRel (@LE.le α _)] : DecidableRel (@LT.lt (ι →ᶠ[{⊤}] α) _) :=
  decidableLTOfDecidableLE

end Preorder

section PartialOrder

variable [PartialOrder α] [OrderTop α]

lemma support_antitone : Antitone (support (α := ι) (M := α) (Zf := λ_ => {⊤})) :=
  fun f g h a ha ↦ by
    rw [mem_support_iff] at ha ⊢
    intro hg
    exact ha <| le_antisymm le_top (le_trans (le_of_eq hg.symm) (h a))

end PartialOrder

section OrderBot
variable [LE α] [OrderBot α]

instance orderBot : OrderBot (ι →ᶠ[{⊥}] α) where
  bot_le := by simp [le_def, bot_apply]

theorem le_iff_bot' (f g : ι →ᶠ[{⊥}] α) {s : Finset ι} (hf : f.support ⊆ s)
  : f ≤ g ↔ ∀ i ∈ s, f i ≤ g i :=
  ⟨fun h s _hs => h s, fun h s => by
    classical exact
        if H : s ∈ f.support then h s (hf H) else (not_mem_support_iff.1 H).symm ▸ bot_le⟩

theorem le_iff_bot (f g : ι →ᶠ[{⊥}] α) : f ≤ g ↔ ∀ i ∈ f.support, f i ≤ g i :=
  le_iff_bot' f g <| Subset.refl _

instance decidableLEBot [DecidableRel (@LE.le α _)] : DecidableRel (@LE.le (ι →ᶠ[{⊥}] α) _)
  := fun f g => decidable_of_iff _ (le_iff_bot f g).symm

variable [DecidableEq α] [DecidableEq ι]

@[simp]
theorem single_le_iff_bot {i : ι} {x : α} {f : ι →ᶠ[{⊥}] α} : single ⊥ i x ≤ f ↔ x ≤ f i :=
  (le_iff_bot' _ _ support_single_subset).trans <| by simp

end OrderBot

section Preorder
variable [DecidableEq α] [Preorder α] [OrderBot α]

instance decidableLTBot [DecidableRel (@LE.le α _)] : DecidableRel (@LT.lt (ι →ᶠ[{⊥}] α) _) :=
  decidableLTOfDecidableLE

end Preorder

section PartialOrder

variable [PartialOrder α] [OrderBot α]

lemma support_monotone : Monotone (support (α := ι) (M := α) (Zf := λ_ => {⊥})) :=
  fun f g h a ha ↦ by
    rw [mem_support_iff] at ha ⊢
    intro hg
    exact ha <| le_antisymm (le_trans (h a) (le_of_eq hg)) bot_le

end PartialOrder
