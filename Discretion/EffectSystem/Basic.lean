import Discretion.Quant.Basic

class HasCommRel (ε : Type u) [PartialOrder ε] [OrderBot ε] : Sort _ where
  right_mover : ε → ε → Prop
  right_mover_anti : ∀{e₁ e₂ e₁' e₂'}, e₁ ≤ e₁' → e₂ ≤ e₂' → right_mover e₁' e₂' → right_mover e₁ e₂
  right_mover_bot : ∀e, right_mover ⊥ e
  right_mover_rel_bot : ∀e, right_mover e ⊥

namespace HasCommRel

variable {ε} [PartialOrder ε] [BoundedOrder ε] [HasCommRel ε]

scoped infixr:50 " ⇀ " => right_mover

abbrev left_mover (l r : ε) : Prop := r ⇀ l

scoped infixr:50 " ↽ " => left_mover

theorem left_mover_bot (e : ε) : ⊥ ↽ e := right_mover_rel_bot e

theorem left_mover_rel_bot (e : ε) : e ↽ ⊥ := right_mover_bot e

theorem left_mover_anti {e₁ e₂ e₁' e₂' : ε} (h₁ : e₁ ≤ e₁') (h₂ : e₂ ≤ e₂') : e₁' ↽ e₂' → e₁ ↽ e₂
  := right_mover_anti h₂ h₁

abbrev commutes (l r : ε) : Prop := l ⇀ r ∧ l ↽ r

scoped infixr:50 " ⇌ " => commutes

theorem commutes_def {l r : ε} : l ⇌ r ↔ l ⇀ r ∧ r ⇀ l := Iff.rfl

theorem commutes_anti {l r l' r' : ε} (h₁ : l ≤ l') (h₂ : r ≤ r') (hc : l' ⇌ r') : l ⇌ r :=
  ⟨right_mover_anti h₁ h₂ hc.1, left_mover_anti h₁ h₂ hc.2⟩

theorem commutes_symm_iff {l r : ε} : l ⇌ r ↔ r ⇌ l := by simp [commutes_def, and_comm]

theorem commutes_symm {l r : ε} : l ⇌ r → r ⇌ l := commutes_symm_iff.mp

theorem commutes_bot_left {r : ε} : (⊥ : ε) ⇌ r := ⟨right_mover_bot r, left_mover_bot r⟩

theorem commutes_bot_right {l : ε} : l ⇌ (⊥ : ε) := commutes_symm commutes_bot_left

theorem right_mover_self_iff {e : ε} : e ⇀ e ↔ e ⇌ e := by simp [commutes_def]

theorem left_mover_self_iff {e : ε} : e ↽ e ↔ e ⇌ e := right_mover_self_iff

end HasCommRel

class EffectSystem (ε : Type u)
  extends PartialOrder ε, BoundedOrder ε, HasCommRel ε, OrderedPQuant ε

instance EffectSystem.instMk {ε}
  [PartialOrder ε] [BoundedOrder ε] [HasCommRel ε] [OrderedPQuant ε]
  : EffectSystem ε where

class IterEffectSystem (ε : Type u)
  extends EffectSystem ε where
  iterative : Set ε
  iterative_is_upper : IsUpperSet iterative
  top_iterative : ⊤ ∈ iterative

attribute [simp] IterEffectSystem.top_iterative
