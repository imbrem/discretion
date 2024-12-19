import Mathlib.CategoryTheory.Monoidal.Free.Basic
import Discretion.Wk.List
import Discretion.Premonoidal.Property.Coherence
import Discretion.Premonoidal.Quant
import Mathlib.Order.Fin.Basic

open CategoryTheory

open CategoryTheory.MonoidalCategory

namespace SEC

scoped notation "Ty" => CategoryTheory.FreeMonoidalCategory

export HasQuant (quant)

export HasPQuant (pquant)

def freeMonQuant {τ} [HasQuant τ] : Ty τ → Quant
  | .of X => quant X
  | .unit => ⊤
  | .tensor A B => freeMonQuant A ⊓ freeMonQuant B

def projectMonQuant {τ} [HasQuant τ] [Category τ] [MonoidalCategoryStruct τ] : HasQuant (Ty τ) where
  quant := quant ∘ FreeMonoidalCategory.projectObj' id

def MonoidalQuant.freeMon (τ) [HasQuant τ] : MonoidalQuant (Ty τ) where
  quant := freeMonQuant
  le_quant_tensor := λ{A B} => le_refl (freeMonQuant A ⊓ freeMonQuant B)
  quant_unit := rfl

def HasQuant.constQ (τ) (q : Quant) : HasQuant τ where
  quant _ := q

def HasQuant.intuitionistic (τ) : HasQuant τ := constQ τ ⊤

def HasQuant.relevant (τ) : HasQuant τ := constQ τ .copy

def HasQuant.affine (τ) : HasQuant τ := constQ τ .del

def HasQuant.linear (τ) : HasQuant τ := constQ τ 1

-- TODO: parametrize by type v?
class FreeSignature (τ : Type u) extends MonoidalQuant (Ty τ) where
  Inst : Ty τ → Ty τ → Type

def FreeSignature.freeMon (τ) [HasQuant τ] : FreeSignature τ where
  toMonoidalQuant := MonoidalQuant.freeMon τ
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
