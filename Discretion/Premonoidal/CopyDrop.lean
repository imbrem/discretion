import Discretion.Premonoidal.Braided
import Discretion.Premonoidal.Predicate.Basic
import Discretion.Premonoidal.Property.Braided
import Discretion.Premonoidal.Quant
import Discretion.Premonoidal.BraidedHelpers
import Discretion.Poset2.Basic
import Mathlib.CategoryTheory.Monoidal.Subcategory

namespace CategoryTheory

open MonoidalCategory

open Monoidal

class CopyDrop (C : Type u) [Category C] [MonoidalCategoryStruct C] [HasQuant C] where
  copy : ∀ (X : C) [IsRelevant X], (X ⟶ X ⊗ X)
  drop : ∀ (X : C) [IsAffine X], (X ⟶ 𝟙_ C)

namespace Monoidal

scoped notation "Δ_" => CopyDrop.copy

scoped notation "!_" => CopyDrop.drop

end Monoidal

section CopyDrop

variable {C : Type u} [Category C] [HasQuant C] [MonoidalCategoryStruct C] [CopyDrop C]

class IsCopyable {X Y : C} (f : X ⟶ Y) where
  copy_hom_ltimes : [IsRelevant X] → [IsRelevant Y] → f ≫ Δ_ Y = Δ_ X ≫ (f ⋉ f)
  copy_hom_rtimes : [IsRelevant X] → [IsRelevant Y] → f ≫ Δ_ Y = Δ_ X ≫ (f ⋊ f)

instance IsCopyable.id {X : C} [IsPremonoidal C] : IsCopyable (𝟙 X) := ⟨by simp, by simp⟩

class IsDroppable {X Y : C} (f : X ⟶ Y) where
  drop_hom : [IsAffine X] → [IsAffine Y] → f ≫ !_ Y = !_ X

instance IsDroppable.id {X : C} : IsDroppable (𝟙 X) := ⟨by simp⟩

instance IsDroppable.comp {X Y Z : C} [IsAffine Y]
  (f : X ⟶ Y) (g : Y ⟶ Z) [IsDroppable f] [IsDroppable g] : IsDroppable (f ≫ g)
  := ⟨by simp [drop_hom]⟩

theorem IsDroppable.comp_of_imp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)
  [IsDroppable f] [IsDroppable g] (h : IsAffine X → IsAffine Y) : IsDroppable (f ≫ g)
  := open Classical in if hX : IsAffine X then
    have _ := h hX; comp f g
  else
    ⟨by simp [hX]⟩

class IsDiscardable {X Y : C} (f : X ⟶ Y) extends IsDroppable f where
  copy_drop_left_res : [IsRelevant X] → [IsAffine Y] → Δ_ X ≫ (f ≫ !_ Y) ▷ X = (λ_ X).inv

class IsPure {X Y : C} (f : X ⟶ Y) extends IsCopyable f, IsDiscardable f, Central f : Prop

instance {X Y : C} {f : X ⟶ Y} [IsCopyable f] [IsDiscardable f] [Central f] : IsPure f := ⟨⟩

namespace Monoidal

theorem copy_hom_ltimes {X Y : C} [IsRelevant X] [IsRelevant Y] (f : X ⟶ Y) [IsCopyable f]
  : f ≫ Δ_ Y = Δ_ X ≫ (f ⋉ f) := IsCopyable.copy_hom_ltimes

theorem copy_hom_rtimes {X Y : C} [IsRelevant X] [IsRelevant Y] (f : X ⟶ Y) [IsCopyable f]
  : f ≫ Δ_ Y = Δ_ X ≫ (f ⋊ f) := IsCopyable.copy_hom_rtimes

@[simp]
theorem drop_hom {X Y : C} [IsAffine X] [IsAffine Y] (f : X ⟶ Y) [IsDroppable f]
  : f ≫ !_ Y = !_ X := IsDroppable.drop_hom

@[simp]
theorem copy_drop_left_res {X Y : C} [IsRelevant X] [IsAffine Y] (f : X ⟶ Y) [IsDiscardable f]
  : Δ_ X ≫ (f ≫ !_ Y) ▷ X = (λ_ X).inv := IsDiscardable.copy_drop_left_res

end Monoidal

section LE

variable [∀X Y : C, LE (X ⟶ Y)]

class IsFusable {X Y : C} (f : X ⟶ Y) where
  copy_hom_le_ltimes : [IsRelevant X] → [IsRelevant Y] → f ≫ Δ_ Y ≤ Δ_ X ≫ (f ⋉ f)
  copy_hom_le_rtimes : [IsRelevant X] → [IsRelevant Y] → f ≫ Δ_ Y ≤ Δ_ X ≫ (f ⋊ f)

class IsDuplicable {X Y : C} (f : X ⟶ Y) where
  ltimes_le_copy_hom : [IsRelevant X] → [IsRelevant Y] → Δ_ X ≫ (f ⋉ f) ≤ f ≫ Δ_ Y
  rtimes_le_copy_hom : [IsRelevant X] → [IsRelevant Y] → Δ_ X ≫ (f ⋊ f) ≤ f ≫ Δ_ Y

class IsAddable {X Y : C} (f : X ⟶ Y) where
  drop_hom_le : [IsAffine X] → [IsAffine Y] → f ≫ !_ Y ≤ !_ X
  copy_drop_left_res_le : [IsRelevant X] → [IsAffine Y] → Δ_ X ≫ (f ≫ !_ Y) ▷ X ≤ (λ_ X).inv

class IsRemovable {X Y : C} (f : X ⟶ Y) where
  le_drop_hom : [IsAffine X] → [IsAffine Y] → !_ X ≤ f ≫ !_ Y
  le_copy_drop_left_res : [IsRelevant X] → [IsAffine Y] → (λ_ X).inv ≤ (Δ_ X ≫ (f ≫ !_ Y) ▷ X)

namespace Monoidal

@[simp]
theorem copy_hom_le_ltimes {X Y : C} [IsRelevant X] [IsRelevant Y] (f : X ⟶ Y) [IsFusable f]
  : f ≫ Δ_ Y ≤ Δ_ X ≫ (f ⋉ f) := IsFusable.copy_hom_le_ltimes

@[simp]
theorem copy_hom_le_rtimes {X Y : C} [IsRelevant X] [IsRelevant Y] (f : X ⟶ Y) [IsFusable f]
  : f ≫ Δ_ Y ≤ Δ_ X ≫ (f ⋊ f) := IsFusable.copy_hom_le_rtimes

@[simp]
theorem ltimes_le_copy_hom {X Y : C} [IsRelevant X] [IsRelevant Y] (f : X ⟶ Y) [IsDuplicable f]
  : Δ_ X ≫ (f ⋉ f) ≤ f ≫ Δ_ Y := IsDuplicable.ltimes_le_copy_hom

@[simp]
theorem rtimes_le_copy_hom {X Y : C} [IsRelevant X] [IsRelevant Y] (f : X ⟶ Y) [IsDuplicable f]
  : Δ_ X ≫ (f ⋊ f) ≤ f ≫ Δ_ Y := IsDuplicable.rtimes_le_copy_hom

@[simp]
theorem drop_hom_le {X Y : C} [IsAffine X] [IsAffine Y] (f : X ⟶ Y) [IsAddable f]
  : f ≫ !_ Y ≤ !_ X := IsAddable.drop_hom_le

@[simp]
theorem copy_drop_left_res_le {X Y : C} [IsRelevant X] [IsAffine Y] (f : X ⟶ Y) [IsAddable f]
  : Δ_ X ≫ (f ≫ !_ Y) ▷ X ≤ (λ_ X).inv := IsAddable.copy_drop_left_res_le

@[simp]
theorem le_drop_hom {X Y : C} [IsAffine X] [IsAffine Y] (f : X ⟶ Y) [IsRemovable f]
  : !_ X ≤ f ≫ !_ Y := IsRemovable.le_drop_hom

@[simp]
theorem le_copy_drop_left_res {X Y : C} [IsRelevant X] [IsAffine Y] (f : X ⟶ Y) [IsRemovable f]
  : (λ_ X).inv ≤ (Δ_ X ≫ (f ≫ !_ Y) ▷ X) := IsRemovable.le_copy_drop_left_res

end Monoidal

end LE

section PartialOrder

variable [∀X Y : C, PartialOrder (X ⟶ Y)]

instance IsCopyable.of_fusable_duplicable {X Y : C} (f : X ⟶ Y) [IsFusable f] [IsDuplicable f]
  : IsCopyable f := ⟨le_antisymm (by simp) (by simp), le_antisymm (by simp) (by simp)⟩

instance IsDroppable.of_addable_removable {X Y : C} (f : X ⟶ Y)
  [IsAddable f] [IsRemovable f] : IsDroppable f := ⟨le_antisymm (by simp) (by simp)⟩

instance IsDiscardable.of_addable_removable {X Y : C} (f : X ⟶ Y)
  [IsAddable f] [IsRemovable f] : IsDiscardable f := ⟨le_antisymm (by simp) (by simp)⟩

end PartialOrder

section Preorder

variable [∀X Y : C, Preorder (X ⟶ Y)]

instance IsCopyable.fusable {X Y : C} (f : X ⟶ Y) [IsCopyable f] : IsFusable f
  := ⟨by simp [copy_hom_ltimes], by simp [copy_hom_rtimes]⟩

instance IsCopyable.duplicable {X Y : C} (f : X ⟶ Y) [IsCopyable f] : IsDuplicable f
  := ⟨by simp [copy_hom_ltimes], by simp [copy_hom_rtimes]⟩

instance IsDiscardable.addable {X Y : C} (f : X ⟶ Y) [IsDiscardable f] : IsAddable f
  := ⟨by simp, by simp⟩

instance IsDiscardable.removable {X Y : C} (f : X ⟶ Y) [IsDiscardable f] : IsRemovable f
  := ⟨by simp, by simp⟩

end Preorder

namespace MorphismProperty

def copyable (C) [Category C] [HasQuant C] [MonoidalCategoryStruct C] [CopyDrop C]
  : MorphismProperty C := λ _ _ f => IsCopyable f

def droppable (C) [Category C] [HasQuant C] [MonoidalCategoryStruct C] [CopyDrop C]
  : MorphismProperty C := λ _ _ f => IsDroppable f

def discardable (C) [Category C] [HasQuant C] [MonoidalCategoryStruct C] [CopyDrop C]
  : MorphismProperty C := λ _ _ f => IsDiscardable f

def fusable (C)
  [Category C] [HasQuant C] [MonoidalCategoryStruct C] [CopyDrop C] [∀X Y : C, LE (X ⟶ Y)]
  : MorphismProperty C := λ _ _ f => IsFusable f

def duplicable (C)
  [Category C] [HasQuant C] [MonoidalCategoryStruct C] [CopyDrop C] [∀X Y : C, LE (X ⟶ Y)]
  : MorphismProperty C := λ _ _ f => IsDuplicable f

def introducable (C)
  [Category C] [HasQuant C] [MonoidalCategoryStruct C] [CopyDrop C] [∀X Y : C, LE (X ⟶ Y)]
  : MorphismProperty C := λ _ _ f => IsAddable f

def deletable (C)
  [Category C] [HasQuant C] [MonoidalCategoryStruct C] [CopyDrop C] [∀X Y : C, LE (X ⟶ Y)]
  : MorphismProperty C := λ _ _ f => IsRemovable f

class Copyable (W : MorphismProperty C) : Prop where
  mem_is_copyable : ∀ {f : X ⟶ Y}, W f → IsCopyable f

class Droppable (W : MorphismProperty C) : Prop where
  mem_is_droppable : ∀ {f : X ⟶ Y}, W f → IsDroppable f

class Discardable (W : MorphismProperty C) : Prop where
  mem_is_discardable : ∀ {f : X ⟶ Y}, W f → IsDiscardable f

-- TODO: monotonicity, inf, sup...

class IsPure (W : MorphismProperty C)
  extends Central W, Copyable W, Droppable W, Discardable W : Prop

theorem mem_is_copyable {W : MorphismProperty C} [Copyable W] {f : X ⟶ Y}
  : W f → IsCopyable f := Copyable.mem_is_copyable

theorem mem_is_droppable {W : MorphismProperty C} [Droppable W] {f : X ⟶ Y}
  : W f → IsDroppable f := Droppable.mem_is_droppable

theorem mem_is_discardable {W : MorphismProperty C} [Discardable W] {f : X ⟶ Y}
  : W f → IsDiscardable f := Discardable.mem_is_discardable

theorem mem_is_pure {W : MorphismProperty C} [IsPure W] {f : X ⟶ Y} (hf : W f)
: CategoryTheory.IsPure f :=
  have _ := mem_is_copyable hf;
  have _ := mem_is_discardable hf;
  have _ := mem_central hf;
  inferInstance

section LE

variable [∀X Y : C, LE (X ⟶ Y)]

class Fusable (W : MorphismProperty C) : Prop where
  mem_is_fusable : ∀ {f : X ⟶ Y}, W f → CategoryTheory.IsFusable f

class Duplicable (W : MorphismProperty C) : Prop where
  mem_is_duplicable : ∀ {f : X ⟶ Y}, W f → CategoryTheory.IsDuplicable f

class Addable (W : MorphismProperty C) : Prop where
  mem_is_introduable : ∀ {f : X ⟶ Y}, W f → IsAddable f

class Removable (W : MorphismProperty C) : Prop where
  mem_is_deletable : ∀ {f : X ⟶ Y}, W f → CategoryTheory.IsRemovable f

-- TODO: monotonicity, inf, sup...

theorem mem_is_fusable {W : MorphismProperty C} [Fusable W] {f : X ⟶ Y}
  : W f → IsFusable f := Fusable.mem_is_fusable

theorem mem_is_duplicable {W : MorphismProperty C} [Duplicable W] {f : X ⟶ Y}
  : W f → IsDuplicable f := Duplicable.mem_is_duplicable

theorem mem_is_introducable {W : MorphismProperty C} [Addable W] {f : X ⟶ Y}
  : W f → IsAddable f := Addable.mem_is_introduable

theorem mem_is_deletable {W : MorphismProperty C} [Removable W] {f : X ⟶ Y}
  : W f → IsRemovable f := Removable.mem_is_deletable

end LE

section PartialOrder

variable [∀X Y : C, PartialOrder (X ⟶ Y)]

instance Copyable.of_fusable_duplicable {W : MorphismProperty C} [Fusable W] [Duplicable W]
  : Copyable W
  := ⟨λhf => have _ := mem_is_fusable hf; have _ := mem_is_duplicable hf; inferInstance⟩

instance Droppable.of_addable_removable
  {W : MorphismProperty C} [Addable W] [Removable W] : Droppable W
  := ⟨λhf => have _ := mem_is_introducable hf; have _ := mem_is_deletable hf; inferInstance⟩

instance Discardable.of_addable_removable
  {W : MorphismProperty C} [Addable W] [Removable W] : Discardable W
  := ⟨λhf => have _ := mem_is_introducable hf; have _ := mem_is_deletable hf; inferInstance⟩

end PartialOrder

section Preorder

variable [∀X Y : C, Preorder (X ⟶ Y)]

instance Copyable.fusable {W : MorphismProperty C} [Copyable W] : Fusable W
  := ⟨λhf => have _ := mem_is_copyable hf; inferInstance⟩

instance Copyable.duplicable {W : MorphismProperty C} [Copyable W] : Duplicable W
  := ⟨λhf => have _ := mem_is_copyable hf; inferInstance⟩

instance Discardable.addable {W : MorphismProperty C} [Discardable W] : Addable W
  := ⟨λhf => have _ := mem_is_discardable hf; inferInstance⟩

instance Discardable.removable {W : MorphismProperty C} [Discardable W] : Removable W
  := ⟨λhf => have _ := mem_is_discardable hf; inferInstance⟩

end Preorder

end MorphismProperty

end CopyDrop

class ComonoidSupply (C : Type u) [Category C]
  [MonoidalCategoryStruct C] [BraidedCategoryStruct C] [MonoidalQuant C]
  extends CopyDrop C where
  copy_central : ∀ (X : C) [IsRelevant X], Central (copy X) := by infer_instance
  drop_central : ∀ (X : C) [IsAffine X], Central (drop X) := by infer_instance
  copy_swap : ∀ (X : C) [IsRelevant X], copy X ≫ σ_ X X = copy X
  copy_copy_left : ∀(X : C) [IsRelevant X],
    copy X ≫ (copy X ▷ X) = copy X ≫ (X ◁ copy X) ≫ (α_ _ _ _).inv
  copy_drop_left : ∀ (X : C) [IsRelevant X] [IsAffine X],
    copy X ≫ (drop X ▷ X) = (λ_ X).inv
  copy_unit : copy (𝟙_ C) = (λ_ (𝟙_ C)).inv
  drop_unit : drop (𝟙_ C) = 𝟙 _
  copy_tensor : ∀ {X Y : C} [IsRelevant X] [IsRelevant Y],
    copy (X ⊗ Y) = (copy X ⊗ copy Y) ≫ swap_inner X X Y Y
  drop_tensor : ∀ {X Y : C} [IsAffine X] [IsAffine Y],
    drop (X ⊗ Y) = (drop X ⊗ drop Y) ≫ (λ_ _).hom

section ComonoidSupply

variable {C : Type u}
  [Category C] [HasQuant C] [MonoidalCategoryStruct C] [BraidedCategoryStruct C] [CopyDrop C]

-- TODO: if X is both affine and relevant, then droppable ==> discardable

-- TODO: ordered versions of the above?

-- TODO: monoidal morphisms are discardable if their monoidal components are

-- TODO: so in particular, so is swap_inner...

-- TODO: monoidal morphisms are duplicable if their monoidal components are

-- TODO: so in particular, so is swap_inner...

-- TODO: a comonoid supply is "coherent" if the symmetric monoidal subcategory is pure

-- TODO: if everything is affine / quantities are strict, then monoidal morphisms are discardable

-- TODO: if everything is relevant / quantities are strict, then monoidal morphisms are duplicable

-- TODO: if everything is affine + relevant, then the comonoid supply is "coherent"

end ComonoidSupply
