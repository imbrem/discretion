import Mathlib.CategoryTheory.Monoidal.Free.Basic
import Discretion.Wk.List

open CategoryTheory.MonoidalCategory

namespace SEC

scoped notation "Ty" => CategoryTheory.FreeMonoidalCategory

scoped notation "tyOf" => CategoryTheory.FreeMonoidalCategory.of

-- TODO: parametrize by type v?
class FreeSignature (τ : Type u) where
  quant : Ty τ → Quant
  quant_mono : ∀{A B}, quant A ⊓ quant B ≤ quant (A ⊗ B)
  Inst : Ty τ → Ty τ → Type

structure Untyped.Inst (τ : Type u) [FreeSignature τ] where
  src : Ty τ
  trg : Ty τ
  op : FreeSignature.Inst src trg

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

class EffectSignature (τ : Type u) [FreeSignature τ] (ε : Type v) where
  eff : ∀A B : Ty τ, FreeSignature.Inst A B → ε

variable {ε : Type v} [EffectSignature τ ε]

def FreeSignature.Inst.eff {A B : Ty τ} (f : FreeSignature.Inst A B) : ε
  := EffectSignature.eff A B f

def Untyped.Inst.eff (f : Untyped.Inst τ) : ε := f.op.eff
