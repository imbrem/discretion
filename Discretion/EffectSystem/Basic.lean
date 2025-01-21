import Discretion.Wk.Quant

class HasCommRel (ε : Type u) [PartialOrder ε] [OrderBot ε] : Sort _ where
  slides : ε → ε → Prop
  slides_anti : ∀{e₁ e₂ e₁' e₂'}, e₁ ≤ e₁' → e₂ ≤ e₂' → slides e₁' e₂' → slides e₁ e₂
  slides_bot_left : ∀e, slides ⊥ e
  slides_bot_right : ∀e, slides e ⊥

namespace HasCommRel

variable {ε} [PartialOrder ε] [BoundedOrder ε] [HasCommRel ε]

scoped infixr:50 " >‖> " => slides

def commutes (l r : ε) : Prop := slides l r ∧ slides r l

scoped infixr:50 " ‖ " => commutes

theorem commutes_def {l r : ε} : l ‖ r ↔ l >‖> r ∧ r >‖> l := Iff.rfl

theorem commutes_symm_iff {l r : ε} : l ‖ r ↔ r ‖ l := by simp [commutes_def, and_comm]

theorem commutes_symm {l r : ε} : l ‖ r → r ‖ l := commutes_symm_iff.mp

theorem commutes_bot_left {r : ε} : (⊥ : ε) ‖ r := ⟨slides_bot_left r, slides_bot_right r⟩

theorem commutes_bot_right {l : ε} : l ‖ (⊥ : ε) := commutes_symm commutes_bot_left

theorem slides_self_iff {e : ε} : e >‖> e ↔ e ‖ e := by simp [commutes_def]

class EffectSystem (ε : Type u)
  extends PartialOrder ε, BoundedOrder ε, HasCommRel ε, OrderedPQuant ε

instance EffectSystem.instMk {ε}
  [PartialOrder ε] [BoundedOrder ε] [HasCommRel ε] [OrderedPQuant ε]
  : EffectSystem ε where
