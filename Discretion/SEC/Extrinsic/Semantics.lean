import Discretion.SEC.Model
import Discretion.SEC.Extrinsic.Typing

open CategoryTheory

open CategoryTheory.MonoidalCategory

namespace SEC

namespace Term

variable
  {τ} [FreeSignature τ]
  {C} [Category C] [MonoidalCategoryStruct C] [HasQuant C]
  [FreeSignature.Model τ C]

open FreeSignature.Model

-- def WfqD.den {Γ qΓ a A} [WqCtx Γ qΓ] : WfqD (τ := τ) Γ qΓ a A → (ctxDen (C := C) Γ qΓ ⟶ tyDen A)
--   | .var h => sorry
--   | .op hA hB ha => sorry
--   | .let₁ hq ha hb => sorry
--   | .unit h => sorry
--   | .pair hq ha hb => sorry
--   | .let₂ hq ha hb => sorry
