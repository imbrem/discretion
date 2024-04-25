-- File based on https://github.com/leanprover-community/mathlib4/blob/b856377d9cf6945a16d9abeaf713bcd10ea0d2db/Mathlib/Data/Finsupp/Order.lean#L48-L49

import Discretion.FinsuppDefault.Defs

open Finset

namespace FinsuppDefault

section Inhabited

variable [DecidableEq ι] [DecidableEq α] [Inhabited α]

section LE
variable [LE α] {f g : ι →ᴰ α}

instance instLEFinsuppDefault : LE (ι →ᴰ α) :=
  ⟨fun f g => ∀ i, f i ≤ g i⟩

lemma le_def : f ≤ g ↔ ∀ i, f i ≤ g i := Iff.rfl

@[simp, norm_cast] lemma coe_le_coe : ⇑f ≤ g ↔ f ≤ g := Iff.rfl

/-- The order on `Finsupp`s over a partial order embeds into the order on functions -/
def orderEmbeddingToFun : (ι →ᴰ α) ↪o (ι → α) where
  toFun f := f
  inj' f g h :=
    FinsuppDefault.ext fun i => by
      dsimp at h
      rw [h]
  map_rel_iff' := coe_le_coe

@[simp]
theorem orderEmbeddingToFun_apply {f : ι →ᴰ α} {i : ι} : orderEmbeddingToFun f i = f i :=
  rfl

end LE

section Preorder
variable [Preorder α] {f g : ι →ᴰ α}

instance preorder : Preorder (ι →ᴰ α) :=
  { FinsuppDefault.instLEFinsuppDefault with
    le_refl := fun f i => le_rfl
    le_trans := fun f g h hfg hgh i => (hfg i).trans (hgh i) }

lemma lt_def : f < g ↔ f ≤ g ∧ ∃ i, f i < g i := Pi.lt_def
@[simp, norm_cast] lemma coe_lt_coe : ⇑f < g ↔ f < g := Iff.rfl

lemma coe_mono : Monotone (FinsuppDefault.toFun : (ι →ᴰ α) → ι → α) := fun _ _ ↦ id
#align finsupp.monotone_to_fun FinsuppDefault.coe_mono

lemma coe_strictMono : Monotone (FinsuppDefault.toFun : (ι →ᴰ α) → ι → α) := fun _ _ ↦ id

end Preorder

instance partialorder [PartialOrder α] : PartialOrder (ι →ᴰ α) where
  le_antisymm f g h1 h2 := by ext; exact le_antisymm (h1 _) (h2 _)

instance semilatticeInf [SemilatticeInf α] : SemilatticeInf (ι →ᴰ α) :=
  { FinsuppDefault.partialorder with
    inf := zipWith (· ⊓ ·) (inf_idem _)
    inf_le_left := fun _f _g _i => inf_le_left
    inf_le_right := fun _f _g _i => inf_le_right
    le_inf := fun _f _g _i h1 h2 s => le_inf (h1 s) (h2 s) }

@[simp]
theorem inf_apply [SemilatticeInf α] {i : ι} {f g : ι →ᴰ α} : (f ⊓ g) i = f i ⊓ g i :=
  rfl

instance semilatticeSup [SemilatticeSup α] : SemilatticeSup (ι →ᴰ α) :=
  { FinsuppDefault.partialorder with
    sup := zipWith (· ⊔ ·) (sup_idem _)
    le_sup_left := fun _f _g _i => le_sup_left
    le_sup_right := fun _f _g _i => le_sup_right
    sup_le := fun _f _g _h hf hg i => sup_le (hf i) (hg i) }

@[simp]
theorem sup_apply [SemilatticeSup α] {i : ι} {f g : ι →ᴰ α} : (f ⊔ g) i = f i ⊔ g i :=
  rfl

instance lattice [Lattice α] : Lattice (ι →ᴰ α) :=
  { FinsuppDefault.semilatticeInf, FinsuppDefault.semilatticeSup with }


section Lattice

variable [Lattice α] (f g : ι →ᴰ α)

theorem support_inf_union_support_sup : (f ⊓ g).support ∪ (f ⊔ g).support = f.support ∪ g.support :=
  coe_injective <| compl_injective <| by ext; simp [inf_eq_and_sup_eq_iff]

theorem support_sup_union_support_inf : (f ⊔ g).support ∪ (f ⊓ g).support = f.support ∪ g.support :=
  (union_comm _ _).trans <| support_inf_union_support_sup _ _

end Lattice

end Inhabited

-- TODO: default is incomparable...

-- section OrderDefault
-- variable [DecidableEq α] [LE α] [OrderDefault α]

-- instance orderDefault : OrderDefault (ι →ᴰ α) where
--   Default_le := by simp [le_def, Default_apply]

-- theorem le_iff' (f g : ι →ᴰ α) {s : Finset ι} (hf : f.support ⊆ s) : f ≤ g ↔ ∀ i ∈ s, f i ≤ g i :=
--   ⟨fun h s _hs => h s, fun h s => by
--     classical exact
--         if H : s ∈ f.support then h s (hf H) else (not_mem_support_iff.1 H).symm ▸ Default_le⟩

-- theorem le_iff (f g : ι →ᴰ α) : f ≤ g ↔ ∀ i ∈ f.support, f i ≤ g i :=
--   le_iff' f g <| Subset.refl _

-- instance decidableLE [DecidableRel (@LE.le α _)] : DecidableRel (@LE.le (ι →ᴰ α) _) := fun f g =>
--   decidable_of_iff _ (le_iff f g).symm

-- variable [DecidableEq ι]

-- @[simp]
-- theorem single_le_iff {i : ι} {x : α} {f : ι →ᴰ α} : single i x ≤ f ↔ x ≤ f i :=
--   (le_iff' _ _ support_single_subset).trans <| by simp

-- end OrderDefault

-- section Preorder
-- variable [DecidableEq α] [Preorder α] [OrderDefault α]

-- instance decidableLT [DecidableRel (@LE.le α _)] : DecidableRel (@LT.lt (ι →ᴰ α) _) :=
--   decidableLTOfDecidableLE

-- end Preorder

-- section PartialOrder

-- variable [DecidableEq α] [PartialOrder α] [OrderDefault α]

-- lemma support_monotone : Monotone (support (α := ι) (M := α)) :=
--   fun f g h a ha ↦ by
--     rw [mem_support_iff] at ha ⊢
--     intro hg
--     exact ha $ le_antisymm (hg ▸ h a) Default_le

-- end PartialOrder
