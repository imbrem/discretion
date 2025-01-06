import Mathlib.CategoryTheory.Monoidal.Free.Basic
import Discretion.Wk.Quant
import Discretion.Premonoidal.Predicate.Basic

namespace CategoryTheory

open MonoidalCategory

open HasQuant

-- TODO: quant monotonic functions (id, comp)

-- TODO: list quantities

class MonoidalQuant (C : Type u) [Category C] [MonoidalCategoryStruct C] extends HasQuant C where
  le_quant_tensor : ∀{X Y : C}, quant X ⊓ quant Y ≤ quant (X ⊗ Y)
  quant_unit : quant (𝟙_ C) = ⊤

class CopyQuant (C : Type u) [Category C] [MonoidalCategoryStruct C]
  extends MonoidalQuant C
  where
  quant_tensor_of_copy : ∀{X : C}, .copy ≤ quant X → quant (X ⊗ X) = quant X
  quant_tensor_eq_of_eqv : ∀{X Y : C}, Monoidal.SymmEqv X Y → quant X = quant Y

-- TODO: show that in any CopyQuant, quant (X ⊗ (X ⊗ X)) = quant X for X copy (done on paper)

theorem HasQuant.quant_tensor_eq_of_eqv_of_quant_tensor
  {C : Type u} [Category C] [MonoidalCategoryStruct C] [HasQuant C]
  (quant_unit : quant (𝟙_ C) = ⊤)
  (quant_tensor : ∀{X Y : C}, quant (X ⊗ Y) = quant X ⊓ quant Y)
  {X Y : C} : Monoidal.SymmEqv X Y → quant X = quant Y
  | ⟨h⟩ => by induction h with
  | refl => rfl
  | trans _ _ If Ig => exact If.trans Ig
  | tensor_left _ If => simp [quant_tensor, *]
  | tensor_right _ If => simp [quant_tensor, *]
  | base h =>
    cases h
    <;> simp only [quant_tensor, quant_unit, top_inf_eq, inf_top_eq]
    <;> first | rw [inf_assoc] | rw [inf_comm]

class StrictQuant (C : Type u) [Category C] [MonoidalCategoryStruct C]
  extends CopyQuant C where
  quant_tensor : ∀{X Y : C}, quant (X ⊗ Y) = quant X ⊓ quant Y
  le_quant_tensor := quant_tensor ▸ le_refl _
  quant_tensor_of_copy _ := quant_tensor.trans (inf_idem (quant _))
  quant_tensor_eq_of_eqv := HasQuant.quant_tensor_eq_of_eqv_of_quant_tensor quant_unit quant_tensor

open HasQuant

variable {C}

section HasQuant

variable [HasQuant C]

class IsRelevant (X : C) : Prop where
  copy_le_quant : .copy ≤ quant X

class IsAffine (X : C) : Prop where
  del_le_quant : .del ≤ quant X

class IsNonlinear (X : C) : Prop where
  quant_eq_top : quant X = ⊤

theorem IsNonlinear.copy_le_quant {X : C} [IsNonlinear X] : .copy ≤ quant X
  := by rw [IsNonlinear.quant_eq_top]; decide

theorem IsNonlinear.del_le_quant {X : C} [IsNonlinear X] : .del ≤ quant X
  := by rw [IsNonlinear.quant_eq_top]; decide

instance IsNonlinear.of_relevant_affine {X : C} [IsRelevant X] [IsAffine X] : IsNonlinear X where
  quant_eq_top := by
    convert sup_le IsRelevant.copy_le_quant (IsAffine.del_le_quant (X := X)) using 0
    generalize quant X = q
    cases q <;> decide

instance IsNonlinear.relevant {X : C} [IsNonlinear X] : IsRelevant X where
  copy_le_quant := IsNonlinear.copy_le_quant

instance IsNonlinear.affine {X : C} [IsNonlinear X] : IsAffine X where
  del_le_quant := IsNonlinear.del_le_quant

end HasQuant

section MonoidalQuant

open MonoidalQuant

variable [Category C] [MonoidalCategoryStruct C] [MonoidalQuant C]

instance IsNonlinear.unit : IsNonlinear (𝟙_ C) where
  quant_eq_top := quant_unit

instance IsRelevant.unit : IsRelevant (𝟙_ C) := inferInstance

instance IsAffine.unit : IsAffine (𝟙_ C) := inferInstance

instance IsRelevant.tensor {X Y : C} [IsRelevant X] [IsRelevant Y] : IsRelevant (X ⊗ Y) where
  copy_le_quant := le_trans (le_inf copy_le_quant copy_le_quant) le_quant_tensor

instance IsAffine.tensor {X Y : C} [IsAffine X] [IsAffine Y] : IsAffine (X ⊗ Y) where
  del_le_quant := le_trans (le_inf del_le_quant del_le_quant) le_quant_tensor

instance IsNonlinear.tensor {X Y : C} [IsNonlinear X] [IsNonlinear Y] : IsNonlinear (X ⊗ Y)
  := inferInstance

end MonoidalQuant

section CopyQuant

variable [Category C] [MonoidalCategoryStruct C] [CopyQuant C]

theorem IsAffine.of_copy {X : C} [IsRelevant X] [IsAffine (X ⊗ X)] : IsAffine X where
  del_le_quant := by
    rw [<-CopyQuant.quant_tensor_of_copy]
    exact IsAffine.del_le_quant
    exact IsRelevant.copy_le_quant

end CopyQuant

section WqCtx

variable [HasQuant τ]

inductive WqCtx : (Γ : List τ) → Vector' EQuant Γ.length → Prop
  | nil : WqCtx [] .nil
  | cons_zero (A) : ∀{Γ qΓ}, WqCtx Γ qΓ → WqCtx (A :: Γ) (qΓ.cons 0)
  | cons_coe (A) (q : Quant) (hq : q ≤ quant A) : ∀{Γ qΓ}, WqCtx Γ qΓ → WqCtx (A :: Γ) (qΓ.cons q)

attribute [class] WqCtx

attribute [instance] WqCtx.nil

theorem WqCtx.cons_quant (A) {Γ qΓ} (h : WqCtx Γ qΓ)
  : WqCtx (τ := τ) (A::Γ) (qΓ.cons (quant A)) := h.cons_coe A (quant A) (le_refl _)

theorem WqCtx.cons_one (A) {Γ qΓ} (h : WqCtx Γ qΓ)
  : WqCtx (τ := τ) (A::Γ) (qΓ.cons 1) := h.cons_coe A 1 (by simp)

instance WqCtx.instConsZero (A) {Γ qΓ} [h : WqCtx Γ qΓ] : WqCtx (τ := τ) (A::Γ) (qΓ.cons 0)
  := cons_zero A h

instance WqCtx.instConsOne (A) {Γ qΓ} [h : WqCtx Γ qΓ] : WqCtx (τ := τ) (A::Γ) (qΓ.cons 1)
  := h.cons_one A

instance WqCtx.instConsQuant (A) {Γ qΓ} [h : WqCtx Γ qΓ] : WqCtx (τ := τ) (A::Γ) (qΓ.cons (quant A))
  := h.cons_quant A

theorem WqCtx.cons_le (A) (q : EQuant) (hq : q ≤ quant A) {Γ qΓ} (h : WqCtx Γ qΓ)
  : WqCtx (τ := τ) (A::Γ) (qΓ.cons q) := match q with
  | 0 => cons_zero A h
  | (q : Quant) => cons_coe A q hq h

theorem WqCtx.cons_nonlinear (A) [IsNonlinear A] (q) {Γ qΓ} (h : WqCtx Γ qΓ)
  : WqCtx (τ := τ) (A::Γ) (qΓ.cons q) := h.cons_le A q (by rw [IsNonlinear.quant_eq_top]; simp)

instance WqCtx.instConsNonlinear (A) [IsNonlinear A] (q) {Γ qΓ} [h : WqCtx Γ qΓ]
  : WqCtx (τ := τ) (A::Γ) (qΓ.cons q)
  := h.cons_nonlinear A q

theorem WqCtx.cons_copy (A) [IsRelevant A] {Γ qΓ} (h : WqCtx Γ qΓ)
  : WqCtx (τ := τ) (A::Γ) (qΓ.cons .copy) := h.cons_le A .copy IsRelevant.copy_le_quant

theorem WqCtx.cons_del (A) [IsAffine A] {Γ qΓ} (h : WqCtx Γ qΓ)
  : WqCtx (τ := τ) (A::Γ) (qΓ.cons .del) := h.cons_le A .del IsAffine.del_le_quant

instance WqCtx.instConsCopy (A) [IsRelevant A] {Γ qΓ} [h : WqCtx Γ qΓ]
  : WqCtx (τ := τ) (A::Γ) (qΓ.cons .copy)
  := h.cons_copy A

instance WqCtx.instConsDel (A) [IsAffine A] {Γ qΓ} [h : WqCtx Γ qΓ]
  : WqCtx (τ := τ) (A::Γ) (qΓ.cons .del)
  := h.cons_del A

theorem WqCtx.tail {Γ : List τ} {qΓ : Vector' _ _}
  (h : WqCtx (A::Γ) (qΓ.cons qa)) : WqCtx Γ qΓ := by cases h <;> assumption

theorem WqCtx.CoeHead {Γ : List τ} {qΓ : Vector' _ _}
  (h : WqCtx (A::Γ) (qΓ.cons qa)) : qa = 0 ∨ qa ≤ quant A := by cases h <;> simp [*]

theorem WqCtx.cons_zero_iff {Γ : List τ} {qΓ : Vector' _ _}
  : WqCtx (A::Γ) (qΓ.cons 0) ↔ WqCtx Γ qΓ := ⟨tail, cons_zero A⟩

theorem WqCtx.head_coe {Γ : List τ} {qΓ : Vector' _ _} {qa : Quant}
  (h : WqCtx (A::Γ) (qΓ.cons qa)) : qa ≤ quant A := by cases h; simp [*]

theorem WqCtx.head {Γ : List τ} {qΓ : Vector' _ _} {qa : EQuant}
  (h : WqCtx (A::Γ) (qΓ.cons qa)) : qa = 0 ∨ qa ≤ quant A := match qa with
  | 0 => Or.inl rfl
  | (qa : Quant) => Or.inr h.head_coe

theorem WqCtx.cons_le_quant_iff {Γ : List τ} {qΓ : Vector' _ _} {qa : EQuant}
  (h : qa ≤ quant A) : WqCtx (A::Γ) (qΓ.cons qa) ↔ WqCtx Γ qΓ := ⟨tail, cons_le A qa h⟩

theorem WqCtx.cons_quant_iff {Γ : List τ} {qΓ : Vector' _ _} {qa : Quant}
  : WqCtx (A::Γ) (qΓ.cons qa) ↔ qa ≤ quant A ∧ WqCtx Γ qΓ
  := ⟨λh => ⟨h.head_coe, h.tail⟩, λ⟨hq, h⟩ => h.cons_coe _ _ hq⟩

theorem WqCtx.cons_iff {Γ : List τ} {qΓ : Vector' _ _} {qa : EQuant}
  : WqCtx (A::Γ) (qΓ.cons qa) ↔ (qa = 0 ∨ qa ≤ quant A) ∧ WqCtx Γ qΓ
  := ⟨λh => ⟨h.head, h.tail⟩, λ⟨hq, h⟩ => by
    cases hq with | inl hq => cases hq; exact h.cons_zero _ | inr hq => exact h.cons_le _ _ hq
  ⟩

end WqCtx

open HasPQuant

class HasCommRel (ε : Type u) [PartialOrder ε] [BoundedOrder ε] : Sort _ where
  commutes : ε → ε → Prop
  commutes_symm : ∀e₁ e₂, commutes e₁ e₂ → commutes e₂ e₁
  commutes_anti_right : ∀e₁ e₂ e₂', e₂ ≤ e₂' → commutes e₁ e₂' → commutes e₁ e₂
  central_bot : commutes ⊥ ⊤

namespace HasCommRel

scoped infixr:50 " ‖ " => commutes

end HasCommRel

open HasCommRel

variable {ε} [PartialOrder ε] [BoundedOrder ε] [HasCommRel ε]

theorem commutes_symm  {l r : ε} : l ‖ r → r ‖ l := HasCommRel.commutes_symm l r

theorem commutes_anti_right {l r r' : ε} (hr : r ≤ r') : l ‖ r' → l ‖ r
  := HasCommRel.commutes_anti_right l r r' hr

theorem commutes_anti_left {l l' r : ε} (hl : l ≤ l') (hlr : l' ‖ r) : l ‖ r
  := commutes_symm <| commutes_anti_right hl (commutes_symm hlr)

theorem commutes_anti {l l' r r' : ε} (hl : l ≤ l') (hr : r ≤ r') (hlr : l' ‖ r') : l ‖ r
  := commutes_anti_right hr (commutes_anti_left hl hlr)

theorem central_bot : (⊥ : ε) ‖ ⊤ := HasCommRel.central_bot

theorem commutes_bot_left {r : ε} : (⊥ : ε) ‖ r := commutes_anti_right le_top central_bot

theorem commutes_bot_right {l : ε} : l ‖ (⊥ : ε) := commutes_symm commutes_bot_left

class EffectSystem (ε : Type u)
  extends PartialOrder ε, BoundedOrder ε, HasCommRel ε, OrderedPQuant ε

instance EffectSystem.instMk {ε}
  [PartialOrder ε] [BoundedOrder ε] [HasCommRel ε] [OrderedPQuant ε]
  : EffectSystem ε where
