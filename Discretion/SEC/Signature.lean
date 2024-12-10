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

def FreeSignature.Inst.erase {τ} [FreeSignature τ] {A B : Ty τ} (op : Inst A B) : Untyped.Inst τ
  := ⟨_, _, op⟩

class Untyped.IsFn (f : Untyped.Inst τ) (A B : outParam (Ty τ)) where
  src_eq : f.src = A
  trg_eq : f.trg = B

instance Untyped.IsFn.refl (f : Untyped.Inst τ) : Untyped.IsFn f f.src f.trg
  := ⟨rfl, rfl⟩
