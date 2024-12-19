import Mathlib.Order.BoundedOrder.Basic

import Discretion.Premonoidal.Braided
import Discretion.Premonoidal.Distributive
import Discretion.Premonoidal.Predicate.Basic
import Discretion.Premonoidal.Property.Braided
import Discretion.Premonoidal.Property.Commutative
import Discretion.Premonoidal.Quant
import Discretion.Premonoidal.CopyDrop

namespace CategoryTheory

open MonoidalCategory

open Monoidal

open MorphismProperty

open EffectSystem

-- TODO: Effectful ==> EffectfulCategory; then Effectful is purely an algebra on E?

class Effectful
  (C : Type v) [Category C] [MonoidalCategoryStruct C] [BraidedCategoryStruct C]
  (E : Type u) [PartialOrder E] [BoundedOrder E] [EffectSystem E]
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
  (E : Type u) [PartialOrder E] [BoundedOrder E] [EffectSystem E] [HasPQuant E]
  extends Effectful C E where
  eff_fusable : ∀e : E, .fuse ≤ pquant e → (eff e).Fusable
  eff_duplicable : ∀e : E, .dup ≤ pquant e → (eff e).Duplicable
  eff_addable : ∀e : E, .add ≤ pquant e → (eff e).Addable
  eff_removable : ∀e : E, .rem ≤ pquant e → (eff e).Removable

-- TODO: PSubEffectful ==> SubEffectful for PartialOrder (X ⟶ Y)

-- TODO: hierarchy dance

-- TODO: every subeffectful category has a coherent comonoid supply, since monoidal is rel + aff

class SubEffectful
  (C : Type v)
  [Category C] [MonoidalCategoryStruct C] [BraidedCategoryStruct C]
  [HasQuant C] [CopyDrop C]
  (E : Type u) [PartialOrder E] [BoundedOrder E] [EffectSystem E] [HasQuant E]
  extends Effectful C E where
  eff_copyable : ∀e : E, .copy ≤ quant e → (eff e).Copyable
  eff_discardable : ∀e : E, .del ≤ quant e → (eff e).Discardable

namespace Monoidal
