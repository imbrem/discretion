import Discretion.Quant.Basic

open HasQuant

open HasPQuant

class IsAff [HasQuant α] (A : α) : Prop where
  del_le_quant : .del ≤ quant A

attribute [simp] IsAff.del_le_quant

theorem IsAff.is_aff_iff [HasQuant α] (a : α) : IsAff a ↔ .del ≤ quant a
  := ⟨λ h => h.del_le_quant, λ h => ⟨h⟩⟩

class IsRel [HasQuant α] (A : α) : Prop where
  copy_le_quant : .copy ≤ quant A

attribute [simp] IsRel.copy_le_quant

theorem IsRel.is_rel_iff [HasQuant α] (a : α) : IsRel a ↔ .copy ≤ quant a
  := ⟨λ h => h.copy_le_quant, λ h => ⟨h⟩⟩

class IsAdd [HasPQuant α] (a : α) : Prop where
  add_le_pquant : .add ≤ pquant a

attribute [simp] IsAdd.add_le_pquant

class IsRem [HasPQuant α] (a : α) : Prop where
  rem_le_pquant : .rem ≤ pquant a

attribute [simp] IsRem.rem_le_pquant

class IsDup [HasPQuant α] (a : α) : Prop where
  dup_le_pquant : .copy ≤ pquant a

attribute [simp] IsDup.dup_le_pquant

class IsFuse [HasPQuant α] (a : α) : Prop where
  fuse_le_pquant : .fuse ≤ pquant a

attribute [simp] IsFuse.fuse_le_pquant

theorem IsAff.add_rem [HasPQuant α] (a : α) [ha : IsAdd a] [ha' : IsRem a] : IsAff a where
  del_le_quant := by simp [quant, PQuant.q]; exact ⟨ha'.rem_le_pquant.1, ha.add_le_pquant.2⟩

theorem IsRel.dup_fuse [HasPQuant α] (a : α) [ha : IsDup a] [ha' : IsFuse a] : IsRel a where
  copy_le_quant := by simp [quant, PQuant.q]; exact ⟨ha.dup_le_pquant.1, ha'.fuse_le_pquant.2⟩

@[simp]
theorem IsAff.del_le_pquant [HasPQuant α] (a : α) [ha : IsAff a] : .del ≤ pquant a
  := le_trans (PQuant.coe_mono ha.del_le_quant) (PQuant.q_le _)

@[simp]
theorem IsRel.copy_le_pquant [HasPQuant α] (a : α) [ha : IsRel a] : .copy ≤ pquant a
  := le_trans (PQuant.coe_mono ha.copy_le_quant) (PQuant.q_le _)

instance IsAff.add [HasPQuant α] (a : α) [ha : IsAff a] : IsAdd a where
  add_le_pquant := le_trans (by decide) ha.del_le_pquant

instance IsAff.rem [HasPQuant α] (a : α) [ha : IsAff a] : IsRem a where
  rem_le_pquant := le_trans (by decide) ha.del_le_pquant

instance IsRel.dup [HasPQuant α] (a : α) [ha : IsRel a] : IsDup a where
  dup_le_pquant := le_trans (by decide) ha.copy_le_pquant

instance IsRel.fuse [HasPQuant α] (a : α) [ha : IsRel a] : IsFuse a where
  fuse_le_pquant := le_trans (by decide) ha.copy_le_pquant

instance IsAff.instBot [LE α] [Bot α] [OrderedPQuant α] : IsAff (⊥ : α)
  := ⟨by simp only [quant, OrderedPQuant.pquant_bot]; decide⟩

instance IsRel.instBot [LE α] [Bot α] [OrderedPQuant α] : IsRel (⊥ : α)
  := ⟨by simp only [quant, OrderedPQuant.pquant_bot]; decide⟩
