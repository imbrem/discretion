import Discretion.Distributive.Property
import Discretion.Poset2.ChosenFiniteProducts
import Discretion.Poset2.Effectful

namespace CategoryTheory

open ChosenFiniteCoproducts

open DistributiveCategory

open Monoidal

class Distributive2 (C : Type u)
  [Category C] [MonoidalCategoryStruct C] [BraidedCategoryStruct C] [ChosenFiniteCoproducts C]
  (E : Type v) [EffectSystem E] extends Effectful2 C E, DistributiveCategory C, DescMono C where
  eff_distributive: ∀e, (eff e).Distributive

variable  {C : Type u}
          [Category C] [MonoidalCategoryStruct C] [BraidedCategoryStruct C]
          [ChosenFiniteCoproducts C] {E : Type v} [EffectSystem E] [D2 : Distributive2 C E]

instance EffectfulCategory.HasEff.inl {e : E} {X Y : C} : HasEff e (inl X Y) where
  has_eff := (D2.eff_distributive e).inl_mem X Y

instance EffectfulCategory.HasEff.inr {e : E} {X Y : C} : HasEff e (inr X Y) where
  has_eff := (D2.eff_distributive e).inr_mem X Y

instance EffectfulCategory.HasEff.desc
  {e : E} {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z)
  [hf : HasEff e f] [hg : HasEff e g] : HasEff e (desc f g) where
  has_eff := (D2.eff_distributive e).coprod_desc_mem hf.has_eff hg.has_eff

instance EffectfulCategory.HasEff.addHom
  {e : E} {X Y X' Y' : C} (f : X ⟶ X') (g : Y ⟶ Y')
  [hf : HasEff e f] [hg : HasEff e g] : HasEff e (f ⊕ₕ g)
  := desc _ _

instance EffectfulCategory.HasEff.distl
  {e : E} {X Y Z : C} : HasEff e ((∂L X Y Z).hom : _ ⟶ _)
  := desc _ _

instance EffectfulCategory.HasEff.distr
  {e : E} {X Y Z : C} : HasEff e ((∂R X Y Z).hom : _ ⟶ _)
  := desc _ _

instance EffectfulCategory.HasEff.distl_inv
  {e : E} {X Y Z : C} : HasEff e ((∂L X Y Z).inv : _ ⟶ _) where
  has_eff := (D2.eff_distributive e).distl_inv_mem

instance EffectfulCategory.HasEff.distr_inv
  {e : E} {X Y Z : C} : HasEff e ((∂R X Y Z).inv : _ ⟶ _) where
  has_eff := (D2.eff_distributive e).distr_inv_mem

end CategoryTheory
