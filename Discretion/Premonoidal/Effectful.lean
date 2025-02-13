import Mathlib.Order.BoundedOrder.Basic

import Discretion.Premonoidal.Braided
import Discretion.Premonoidal.Distributive
import Discretion.Premonoidal.Predicate.Basic
import Discretion.Premonoidal.Property.Braided
import Discretion.Premonoidal.Property.Commutative
import Discretion.Premonoidal.Quant
import Discretion.EffectSystem.Basic

import Discretion.Poset2.Basic

namespace CategoryTheory

open MonoidalCategory

open Monoidal

open MorphismProperty

open HasCommRel

class EffectfulCategory
  (C : Type v) [Category C] [MonoidalCategoryStruct C] [BraidedCategoryStruct C]
  (E : Type u) [EffectSystem E] where
  eff : E →o MorphismProperty C
  eff_top : eff ⊤ = ⊤
  eff_monoidal : ∀e, (eff e).IsMonoidal
  eff_braided : ∀e, (eff e).IsBraided
  eff_comm : ∀{e e' : E}, e ⇌ e' → Commutes (eff e) (eff e')

abbrev EffectfulCategory.pure [Category C] [MonoidalCategoryStruct C] [BraidedCategoryStruct C]
  (E : Type u) [EffectSystem E] [EC : EffectfulCategory C E] : MorphismProperty C
  := EC.eff ⊥

namespace Monoidal
