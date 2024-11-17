import Mathlib.CategoryTheory.MorphismProperty.Composition
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts

namespace CategoryTheory.MorphismProperty

open Limits

variable {C} [Category C]

class ContainsProjections (W : MorphismProperty C) : Prop where
  fst_mem : ∀{X Y : C} [HasBinaryProduct X Y], W (prod.fst : X ⨯ Y ⟶ X)
  mem_mem : ∀{X Y : C} [HasBinaryProduct X Y], W (prod.snd : X ⨯ Y ⟶ Y)

theorem fst_mem {W : MorphismProperty C} [ContainsProjections W] {X Y : C} [HasBinaryProduct X Y]
  : W (prod.fst : X ⨯ Y ⟶ X) := ContainsProjections.fst_mem

theorem snd_mem {W : MorphismProperty C} [ContainsProjections W] {X Y : C} [HasBinaryProduct X Y]
  : W (prod.snd : X ⨯ Y ⟶ Y) := ContainsProjections.mem_mem

class ContainsProdLift (W : MorphismProperty C) : Prop where
  prod_lift_mem : ∀{X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} [HasBinaryProduct Y Z],
    W f → W g → W (prod.lift f g)

theorem prod_lift_mem {W : MorphismProperty C} [ContainsProdLift W] {X Y Z : C}
  {f : X ⟶ Y} {g : X ⟶ Z} [HasBinaryProduct Y Z] (hf : W f) (hg : W g) : W (prod.lift f g)
  := ContainsProdLift.prod_lift_mem hf hg

class ContainsProducts (W : MorphismProperty C)
  extends ContainsProjections W, ContainsProdLift W, IsMultiplicative W : Prop

theorem prod_map_mem {W : MorphismProperty C} [ContainsProducts W]
  {X Y X' Y' : C} {f : X ⟶ X'} {g : Y ⟶ Y'} [HasBinaryProduct X Y] [HasBinaryProduct X' Y']
  (hf : W f) (hg : W g) : W (prod.map f g) := by
  rw [<-prod.lift_fst_comp_snd_comp]
  apply prod_lift_mem <;> apply comp_mem <;> first | assumption | apply fst_mem | apply snd_mem

class ContainsInjections (W : MorphismProperty C) : Prop where
  inl_mem : ∀{X Y : C} [HasBinaryCoproduct X Y], W (coprod.inl : X ⟶ X ⨿ Y)
  inr_mem : ∀{X Y : C} [HasBinaryCoproduct X Y], W (coprod.inr : Y ⟶ X ⨿ Y)

theorem inl_mem {W : MorphismProperty C} [ContainsInjections W] {X Y : C} [HasBinaryCoproduct X Y]
  : W (coprod.inl : X ⟶ X ⨿ Y) := ContainsInjections.inl_mem

theorem inr_mem {W : MorphismProperty C} [ContainsInjections W] {X Y : C} [HasBinaryCoproduct X Y]
  : W (coprod.inr : Y ⟶ X ⨿ Y) := ContainsInjections.inr_mem

class ContainsCoprodDesc (W : MorphismProperty C) : Prop where
  coprod_desc_mem : ∀{X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} [HasBinaryCoproduct X Y],
    W f → W g → W (coprod.desc f g)

theorem coprod_desc_mem {W : MorphismProperty C} [ContainsCoprodDesc W] {X Y Z : C}
  {f : X ⟶ Z} {g : Y ⟶ Z} [HasBinaryCoproduct X Y] (hf : W f) (hg : W g) : W (coprod.desc f g)
  := ContainsCoprodDesc.coprod_desc_mem hf hg

theorem codiag_mem {W : MorphismProperty C} [ContainsCoprodDesc W] [ContainsIdentities W]
  {X : C} [HasBinaryCoproduct X X]
  : W (codiag X) := coprod_desc_mem (id_mem _ _) (id_mem _ _)

class ContainsCoproducts (W : MorphismProperty C)
  extends ContainsInjections W, ContainsCoprodDesc W, IsMultiplicative W : Prop

theorem coprod_map_mem {W : MorphismProperty C} [ContainsCoproducts W]
  {X Y X' Y' : C} {f : X ⟶ X'} {g : Y ⟶ Y'} [HasBinaryCoproduct X Y] [HasBinaryCoproduct X' Y']
  (hf : W f) (hg : W g) : W (coprod.map f g) := by
  rw [<-coprod.desc_comp_inl_comp_inr]
  apply coprod_desc_mem <;> apply comp_mem <;> first | assumption | apply inl_mem | apply inr_mem

-- TODO: inf and sup instances; top instances
