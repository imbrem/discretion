import Discretion.SEC.Signature
import Discretion.Premonoidal.Effectful

open CategoryTheory

open CategoryTheory.MonoidalCategory

namespace SEC

class FreeSignature.Model
  (τ : Type u) [FreeSignature τ]
  (C : Type v) [Category C] [MonoidalCategoryStruct C] [HasQuant C]
  where
  baseDen : τ → C
  opDen : ∀{A B : Ty τ}, FreeSignature.Inst A B → (A.projectObj' baseDen ⟶ B.projectObj' baseDen)

scoped notation "tyDen"
  => CategoryTheory.FreeMonoidalCategory.projectObj' FreeSignature.Model.baseDen

namespace FreeSignature.Model

variable {τ : Type u} [FreeSignature τ]
         {C : Type v} [Category C] [MonoidalCategoryStruct C] [HasQuant C]
         [FreeSignature.Model τ C]

def ctxDen : List (Ty τ) → C
  | [] => 𝟙_ C
  | A :: Γ => tyDen A ⊗ ctxDen Γ

-- TODO: effect model
