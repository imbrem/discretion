import Mathlib.CategoryTheory.Monoidal.Free.Basic
import Discretion.Wk.List
import Discretion.Premonoidal.Property.Coherence
import Mathlib.Order.Fin.Basic

open CategoryTheory

open CategoryTheory.MonoidalCategory

namespace SEC

scoped notation "Ty" => CategoryTheory.FreeMonoidalCategory

scoped notation "tyOf" => CategoryTheory.FreeMonoidalCategory.of

class HasQuant (τ : Type u) where
  quant : τ → Quant

def quant {τ} [HasQuant τ] (a : τ) : Quant := HasQuant.quant a

def freeMonQuant {τ} [HasQuant τ] : Ty τ → Quant
  | .of X => quant X
  | .unit => ⊤
  | .tensor A B => freeMonQuant A ⊓ freeMonQuant B

def projectMonQuant {τ} [HasQuant τ] [Category τ] [MonoidalCategoryStruct τ] : HasQuant (Ty τ) where
  quant := quant ∘ FreeMonoidalCategory.projectObj' id

def HasQuant.freeMon (τ) [HasQuant τ] : HasQuant (Ty τ) where
  quant := freeMonQuant

def HasQuant.constQ (τ) (q : Quant) : HasQuant τ where
  quant _ := q

def HasQuant.intuitionistic (τ) : HasQuant τ := constQ τ ⊤

def HasQuant.relevant (τ) : HasQuant τ := constQ τ .copy

def HasQuant.affine (τ) : HasQuant τ := constQ τ .del

def HasQuant.linear (τ) : HasQuant τ := constQ τ 1

-- TODO: parametrize by type v?
class FreeSignature (τ : Type u) extends HasQuant (Ty τ) where
  quant_mono : ∀{A B}, quant A ⊓ quant B ≤ quant (A ⊗ B)
  Inst : Ty τ → Ty τ → Type

def FreeSignature.freeMon (τ) [HasQuant τ] : FreeSignature τ where
  toHasQuant := HasQuant.freeMon τ
  quant_mono := λ{A B} => le_refl (freeMonQuant A ⊓ freeMonQuant B)
  Inst _ _ := Empty

structure Untyped.Inst (τ : Type u) [FreeSignature τ] where
  src : Ty τ
  trg : Ty τ
  op : FreeSignature.Inst src trg

section FreeSignature

variable {τ} [FreeSignature τ]

def FreeSignature.eQuantV : ∀Γ : List (Ty τ), Vector' EQuant Γ.length
  | [] => .nil
  | A::Γ => (eQuantV Γ).cons (quant A)

def FreeSignature.Inst.erase {τ} [FreeSignature τ] {A B : Ty τ} (op : Inst A B) : Untyped.Inst τ
  := ⟨_, _, op⟩

class Untyped.IsFn (f : Untyped.Inst τ) (A B : outParam (Ty τ)) where
  src_eq : f.src = A
  trg_eq : f.trg = B

instance Untyped.IsFn.refl (f : Untyped.Inst τ) : Untyped.IsFn f f.src f.trg
  := ⟨rfl, rfl⟩

class HasPQuant (τ : Type u) [LE τ] [Bot τ] where
  pquant : τ → PQuant
  pquant_bot : pquant (⊥ : τ) = ⊤
  pquant_anti : ∀lo hi : τ, lo ≤ hi → pquant hi ≤ pquant lo

class EffectSignature (τ : Type u) [FreeSignature τ] (ε : Type v) where
  eff : ∀A B : Ty τ, FreeSignature.Inst A B → ε

variable {ε : Type v} [EffectSignature τ ε]

def FreeSignature.Inst.eff {A B : Ty τ} (f : FreeSignature.Inst A B) : ε
  := EffectSignature.eff A B f

def Untyped.Inst.eff (f : Untyped.Inst τ) : ε := f.op.eff

end FreeSignature

section HasPQuant

variable {τ} [LE τ] [Bot τ] [HasPQuant τ]

def pquant (a : τ) : PQuant := HasPQuant.pquant a

theorem pquant_bot {τ} [LE τ] [Bot τ] [HasPQuant τ] : pquant (⊥ : τ) = ⊤
  := HasPQuant.pquant_bot

theorem pquant_anti {τ} [LE τ] [Bot τ] [HasPQuant τ] {lo hi : τ} (h : lo ≤ hi)
  : pquant hi ≤ pquant lo := HasPQuant.pquant_anti lo hi h

end HasPQuant

section HasPQuants

def HasPQuant.intuitionistic (τ) [LE τ] [Bot τ] : HasPQuant τ where
  pquant _ := ⊤
  pquant_bot := rfl
  pquant_anti _ _ _ := le_refl _

variable (τ) [PartialOrder τ] [OrderBot τ] [DecidableEq τ]

def HasPQuant.relevant : HasPQuant τ where
  pquant t := if t = ⊥ then ⊤ else .copy
  pquant_bot := by simp
  pquant_anti lo hi h := by
    if h' : lo = ⊥ then simp[h']
    else if h'' : hi = ⊥ then cases h''; simp [*] at h
    else simp [*]

def HasPQuant.affine : HasPQuant τ where
  pquant t := if t = ⊥ then ⊤ else .del
  pquant_bot := by simp
  pquant_anti lo hi h := by
    if h' : lo = ⊥ then simp[h']
    else if h'' : hi = ⊥ then cases h''; simp [*] at h
    else simp [*]

def HasPQuant.linear : HasPQuant τ where
  pquant t := if t = ⊥ then ⊤ else 1
  pquant_bot := by simp
  pquant_anti lo hi h := by
    if h' : lo = ⊥ then simp[h']
    else if h'' : hi = ⊥ then cases h''; simp [*] at h
    else simp [*]

end HasPQuants

class EffectSystem (ε : Type u) [PartialOrder ε] [BoundedOrder ε] : Sort _ where
  commutes : ε → ε → Prop
  commutes_symm : ∀e₁ e₂, commutes e₁ e₂ → commutes e₂ e₁
  commutes_anti_right : ∀e₁ e₂ e₂', e₂ ≤ e₂' → commutes e₁ e₂' → commutes e₁ e₂
  central_bot : commutes ⊥ ⊤

scoped infixr:50 " ‖ " => EffectSystem.commutes

section EffectSystem

variable {ε} [PartialOrder ε] [BoundedOrder ε] [EffectSystem ε]

theorem commutes_symm  {l r : ε} : l ‖ r → r ‖ l := EffectSystem.commutes_symm l r

theorem commutes_anti_right {l r r' : ε} (hr : r ≤ r') : l ‖ r' → l ‖ r
  := EffectSystem.commutes_anti_right l r r' hr

theorem commutes_anti_left {l l' r : ε} (hl : l ≤ l') (hlr : l' ‖ r) : l ‖ r
  := commutes_symm <| commutes_anti_right hl (commutes_symm hlr)

theorem commutes_anti {l l' r r' : ε} (hl : l ≤ l') (hr : r ≤ r') (hlr : l' ‖ r') : l ‖ r
  := commutes_anti_right hr (commutes_anti_left hl hlr)

theorem central_bot : (⊥ : ε) ‖ ⊤ := EffectSystem.central_bot

theorem commutes_bot_left {r : ε} : (⊥ : ε) ‖ r := commutes_anti_right le_top central_bot

theorem commutes_bot_right {l : ε} : l ‖ (⊥ : ε) := commutes_symm commutes_bot_left

end EffectSystem

class SubEffectSystem (ε : Type u) [PartialOrder ε] [BoundedOrder ε]
  extends EffectSystem ε, HasPQuant ε

section SubEffectSystems

variable (ε) [PartialOrder ε] [BoundedOrder ε] [EffectSystem ε]

def EffectSystem.monoidal : EffectSystem ε where
  commutes _ _ := True
  commutes_symm := by tauto
  commutes_anti_right := by tauto
  central_bot := trivial

def EffectSystem.comparable : EffectSystem ε where
  commutes := Relation.EqvGen (· ≤ ·)
  commutes_symm := Relation.EqvGen.symm
  commutes_anti_right _ _ _ h h' := h'.trans _ _ _ ((Relation.EqvGen.rel _ _ h).symm _ _)
  central_bot := .rel _ _ bot_le

def EffectSystem.minimal : EffectSystem ε where
  commutes a b := a = ⊥ ∨ b = ⊥
  commutes_symm := by tauto
  commutes_anti_right := by aesop
  central_bot := by tauto

def SubEffectSystem.cartesian : SubEffectSystem ε where
  toEffectSystem := EffectSystem.monoidal ε
  toHasPQuant := HasPQuant.intuitionistic ε

variable [DecidableEq ε]

def SubEffectSystem.monoidal : SubEffectSystem ε where
  toEffectSystem := EffectSystem.monoidal ε
  toHasPQuant := HasPQuant.linear ε

def SubEffectSystem.premonoidal : SubEffectSystem ε where
  toEffectSystem := EffectSystem.minimal ε
  toHasPQuant := HasPQuant.linear ε

def SubEffectSystem.markov : SubEffectSystem ε where
  toEffectSystem := EffectSystem.monoidal ε
  toHasPQuant := HasPQuant.affine ε

end SubEffectSystems

instance SubEffectSystem.unit : EffectSystem Unit := EffectSystem.monoidal Unit

instance EffectSystem.quant : EffectSystem Quant := EffectSystem.monoidal Quant

instance EffectSystem.pquant : EffectSystem PQuant := EffectSystem.monoidal PQuant
