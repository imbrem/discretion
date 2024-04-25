-- File based on https://github.com/leanprover-community/mathlib4/blob/b856377d9cf6945a16d9abeaf713bcd10ea0d2db/Mathlib/Data/Finsupp/Order.lean#L48-L49

import Discretion.FinsuppTop.Defs

open Finset

namespace FinsuppTop

section Top

variable [DecidableEq ι] [DecidableEq α] [Top α]

section LE
variable [LE α] {f g : ι →ᵀ α}

instance instLEFinsuppTop : LE (ι →ᵀ α) :=
  ⟨fun f g => ∀ i, f i ≤ g i⟩

lemma le_def : f ≤ g ↔ ∀ i, f i ≤ g i := Iff.rfl

@[simp, norm_cast] lemma coe_le_coe : ⇑f ≤ g ↔ f ≤ g := Iff.rfl

/-- The order on `FinsuppTop`s over a partial order embeds into the order on functions -/
def orderEmbeddingToFun : (ι →ᵀ α) ↪o (ι → α) where
  toFun f := f
  inj' f g h :=
    FinsuppTop.ext fun i => by
      dsimp at h
      rw [h]
  map_rel_iff' := coe_le_coe

@[simp]
theorem orderEmbeddingToFun_apply {f : ι →ᵀ α} {i : ι} : orderEmbeddingToFun f i = f i :=
  rfl

end LE

section Preorder
variable [Preorder α] {f g : ι →ᵀ α}

instance preorder : Preorder (ι →ᵀ α) :=
  { FinsuppTop.instLEFinsuppTop with
    le_refl := fun f i => le_rfl
    le_trans := fun f g h hfg hgh i => (hfg i).trans (hgh i) }

lemma lt_def : f < g ↔ f ≤ g ∧ ∃ i, f i < g i := Pi.lt_def
@[simp, norm_cast] lemma coe_lt_coe : ⇑f < g ↔ f < g := Iff.rfl

lemma coe_mono : Monotone (FinsuppTop.toFun : (ι →ᵀ α) → ι → α) := fun _ _ ↦ id
#align finsupp.monotone_to_fun FinsuppTop.coe_mono

lemma coe_strictMono : Monotone (FinsuppTop.toFun : (ι →ᵀ α) → ι → α) := fun _ _ ↦ id

end Preorder

instance partialorder [PartialOrder α] : PartialOrder (ι →ᵀ α) :=
  { FinsuppTop.preorder with le_antisymm :=
      fun _f _g hfg hgf => ext fun i => (hfg i).antisymm (hgf i) }

instance semilatticeInf [SemilatticeInf α] : SemilatticeInf (ι →ᵀ α) :=
  { FinsuppTop.partialorder with
    inf := zipWith (· ⊓ ·) (inf_idem _)
    inf_le_left := fun _f _g _i => inf_le_left
    inf_le_right := fun _f _g _i => inf_le_right
    le_inf := fun _f _g _i h1 h2 s => le_inf (h1 s) (h2 s) }

@[simp]
theorem inf_apply [SemilatticeInf α] {i : ι} {f g : ι →ᵀ α} : (f ⊓ g) i = f i ⊓ g i :=
  rfl

instance semilatticeSup [SemilatticeSup α] : SemilatticeSup (ι →ᵀ α) :=
  { FinsuppTop.partialorder with
    sup := zipWith (· ⊔ ·) (sup_idem _)
    le_sup_left := fun _f _g _i => le_sup_left
    le_sup_right := fun _f _g _i => le_sup_right
    sup_le := fun _f _g _h hf hg i => sup_le (hf i) (hg i) }

@[simp]
theorem sup_apply [SemilatticeSup α] {i : ι} {f g : ι →ᵀ α} : (f ⊔ g) i = f i ⊔ g i :=
  rfl

instance lattice [Lattice α] : Lattice (ι →ᵀ α) :=
  { FinsuppTop.semilatticeInf, FinsuppTop.semilatticeSup with }


section Lattice

variable [Lattice α] (f g : ι →ᵀ α)

theorem support_inf_union_support_sup : (f ⊓ g).support ∪ (f ⊔ g).support = f.support ∪ g.support :=
  coe_injective <| compl_injective <| by ext; simp [inf_eq_and_sup_eq_iff]

theorem support_sup_union_support_inf : (f ⊔ g).support ∪ (f ⊓ g).support = f.support ∪ g.support :=
  (union_comm _ _).trans <| support_inf_union_support_sup _ _

end Lattice

end Top

section OrderTop
variable [DecidableEq α] [LE α] [OrderTop α]

instance orderTop : OrderTop (ι →ᵀ α) where
  le_top := by simp [le_def, top_apply]

theorem le_iff' (f g : ι →ᵀ α) {s : Finset ι} (hf : g.support ⊆ s) : f ≤ g ↔ ∀ i ∈ s, f i ≤ g i :=
  ⟨fun h s _hs => h s, fun h s => by
    classical exact
        if H : s ∈ g.support then h s (hf H) else (not_mem_support_iff.1 H).symm ▸ le_top⟩

theorem le_iff (f g : ι →ᵀ α) : f ≤ g ↔ ∀ i ∈ g.support, f i ≤ g i :=
  le_iff' f g <| Subset.refl _

instance decidableLE [DecidableRel (@LE.le α _)] : DecidableRel (@LE.le (ι →ᵀ α) _) := fun f g =>
  decidable_of_iff _ (le_iff f g).symm

variable [DecidableEq ι]

@[simp]
theorem le_single_iff {i : ι} {x : α} {f : ι →ᵀ α} : f ≤ single i x ↔ f i ≤ x :=
  (le_iff' _ _ support_single_subset).trans <| by simp

end OrderTop

section Preorder
variable [DecidableEq α] [Preorder α] [OrderTop α]

instance decidableLT [DecidableRel (@LE.le α _)] : DecidableRel (@LT.lt (ι →ᵀ α) _) :=
  decidableLTOfDecidableLE

end Preorder

section PartialOrder

variable [DecidableEq α] [PartialOrder α] [OrderTop α]

lemma support_monotone : Antitone (support (α := ι) (M := α)) :=
  fun f g h a ha ↦ by
    rw [mem_support_iff] at ha ⊢
    intro hg
    exact ha $ le_antisymm le_top (hg ▸ h a)

end PartialOrder
