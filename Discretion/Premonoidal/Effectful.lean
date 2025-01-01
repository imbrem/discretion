import Mathlib.Order.BoundedOrder.Basic

import Discretion.Premonoidal.Braided
import Discretion.Premonoidal.Distributive
import Discretion.Premonoidal.Predicate.Basic
import Discretion.Premonoidal.Property.Braided
import Discretion.Premonoidal.Property.Commutative
import Discretion.Premonoidal.Quant
import Discretion.Premonoidal.CopyDrop

import Discretion.Poset2.Basic

namespace CategoryTheory

open MonoidalCategory

open Monoidal

open MorphismProperty

open HasCommRel

-- TODO: Effectful ==> EffectfulCategory; then Effectful is purely an algebra on E?

class Effectful
  (C : Type v) [Category C] [MonoidalCategoryStruct C] [BraidedCategoryStruct C]
  (E : Type u) [PartialOrder E] [BoundedOrder E] [HasCommRel E]
  : Type _ where
  eff : E →o MorphismProperty C
  eff_top : eff ⊤ = ⊤
  eff_braided : ∀e, (eff e).IsBraided
  eff_commutes : ∀e₁ e₂, e₁ ‖ e₂ → Commutes (eff e₁) (eff e₂)

attribute [simp] Effectful.eff_top

open HasPQuant HasQuant

class PSubEffectful
  (C : Type v)
  [Category C] [MonoidalCategoryStruct C] [BraidedCategoryStruct C] [∀X Y : C, LE (X ⟶ Y)]
  [HasQuant C] [CopyDrop C]
  (E : Type u) [PartialOrder E] [BoundedOrder E] [HasCommRel E] [HasPQuant E]
  extends Effectful C E where
  eff_has_copy_drop : ∀e : E, (eff e).HasCopyDrop
  eff_fusable : ∀e : E, .fuse ≤ pquant e → (eff e).Fusable
  eff_duplicable : ∀e : E, .dup ≤ pquant e → (eff e).Duplicable
  eff_addable : ∀e : E, .add ≤ pquant e → (eff e).Addable
  eff_removable : ∀e : E, .rem ≤ pquant e → (eff e).Removable

class SubEffectful
  (C : Type v)
  [Category C] [MonoidalCategoryStruct C] [BraidedCategoryStruct C]
  [HasQuant C] [CopyDrop C]
  (E : Type u) [PartialOrder E] [BoundedOrder E] [HasCommRel E] [HasQuant E]
  extends Effectful C E where
  eff_copyable : ∀e : E, .copy ≤ quant e → (eff e).Copyable
  eff_discardable : ∀e : E, .del ≤ quant e → (eff e).Discardable

instance SubEffectful.ofPSubEffectful
  {C : Type v}
  [Category C] [MonoidalCategoryStruct C] [BraidedCategoryStruct C]
  [HasQuant C] [CopyDrop C] [∀X Y : C, PartialOrder (X ⟶ Y)]
  {E : Type u} [PartialOrder E] [BoundedOrder E] [HasCommRel E] [HasPQuant E]
  [PSubEffectful C E]
  : SubEffectful C E where
  eff_copyable e h :=
    let fusable := PSubEffectful.eff_fusable e
      (PQuant.fuse_le_copy.trans ((PQuant.coe_mono h).trans (PQuant.q_le _)))
    let duplicable := PSubEffectful.eff_duplicable e
      (PQuant.dup_le_copy.trans ((PQuant.coe_mono h).trans (PQuant.q_le _)))
    Copyable.of_fusable_duplicable (hF := fusable) (hD := duplicable)
  eff_discardable e h :=
    let addable := PSubEffectful.eff_addable e
      (PQuant.add_le_del.trans ((PQuant.coe_mono h).trans (PQuant.q_le _)))
    let removable := PSubEffectful.eff_removable e
      (PQuant.rem_le_del.trans ((PQuant.coe_mono h).trans (PQuant.q_le _)))
    Discardable.of_addable_removable (hA := addable) (hR := removable)

-- TODO: every subeffectful category has a coherent comonoid supply, since monoidal is rel + aff

class OPGSCategory.{v, u}
  (C : Type v) [Category C] [∀X Y : C, PartialOrder (X ⟶ Y)]
  (E : Type u) [EffectSystem E]
  extends
  CompMonotone C, -- Is a 2-poset
  MonoidalCategoryStruct C, IsPremonoidal C, WhiskeringMonotone C, -- Is premonoidal
  BraidedCategoryStruct C, IsSymmetric C, -- Is symmetric
  CopyQuant C, ComonoidSupply C, -- Has a comonoid supply
  PSubEffectful C E -- Is subeffectful w.r.t. E
  where

instance OPGSCategory.instMk
  {C : Type v} [Category C] [∀X Y : C, PartialOrder (X ⟶ Y)]
  {E : Type u} [EffectSystem E]
  [CompMonotone C] [MonoidalCategoryStruct C] [IsPremonoidal C] [WhiskeringMonotone C]
  [BraidedCategoryStruct C] [IsSymmetric C] [CopyQuant C] [ComonoidSupply C]
  [PSubEffectful C E]
  : OPGSCategory C E where

-- TODO: actually _define_ some OPGS categories

namespace Monoidal
