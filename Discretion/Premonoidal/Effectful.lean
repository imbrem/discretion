import Mathlib.Order.BoundedOrder.Basic

import Discretion.Premonoidal.Braided
import Discretion.Premonoidal.Distributive
import Discretion.Premonoidal.Predicate.Basic
import Discretion.Premonoidal.Property.Braided

namespace CategoryTheory

open MonoidalCategory

open Monoidal

open MorphismProperty

class EffectSystem (C : Type v) [Category C] (E : Type u) [BoundedOrder E]
  : Type _ where
  eff : E →o MorphismProperty C
  eff_multiplicative : ∀e, IsMultiplicative (eff e)

namespace EffectSystem

variable {E : Type u} [PartialOrder E]

-- class IsMonoidal
--   (C : Type v)
--   [Category C] [MonoidalCategoryStruct C] [BraidedCategoryStruct C] [EffectSystem C E]
--   (e : E)
--   : Prop where
--   eff_monoidal : (eff (C := C) e).IsMonoidal

-- class IsBraided
--   (C : Type v)
--   [Category C] [MonoidalCategoryStruct C] [BraidedCategoryStruct C] [EffectSystem C E]
--   (e : E)
--   extends IsMonoidal C e : Prop where
--   eff_braided : (eff (C := C) e).ContainsBraidings

class Monoidal
  (C : Type v)
  [Category C] [MonoidalCategoryStruct C] [BraidedCategoryStruct C]
  (E : Type u) [PartialOrder E] [EffectSystem C E]
  : Prop where
  eff_monoidal : ∀e : E, (eff (C := C) e).IsMonoidal

class Braided
  (C : Type v)
  [Category C] [MonoidalCategoryStruct C] [BraidedCategoryStruct C]
  (E : Type u) [PartialOrder E] [EffectSystem C E]
  extends Monoidal C E : Prop where
  eff_braided : ∀e: E, (eff (C := C) e).ContainsBraidings

class IsCentral
  (C : Type v)
  [Category C] [MonoidalCategoryStruct C] [EffectSystem C E]
  (e : E)
  : Prop where
  eff_central : (eff (C := C) e).Central

end EffectSystem

namespace Monoidal
