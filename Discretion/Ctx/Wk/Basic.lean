import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Hom.Defs

class WkPreCat.{v} (α : Type u) where
  Wk : α → α → Type v
  one (n : α) : Wk n n
  comp {n m k} : Wk n m → Wk m k → Wk n k

namespace WkPreCat

notation "𝟙ʷ" => WkPreCat.one

infixr:10 "->>ʷ" => WkPreCat.Wk

infixr:80 "≫ʷ" => WkPreCat.comp

def castWk [WkPreCat α] {n n' m m' : α}
  (hn : n = n') (hm : m = m') (ρ : n ->>ʷ m) : n' ->>ʷ m' := hm ▸ hn ▸ ρ

def wkEq [WkPreCat α] {n m : α} (h : n = m) : n ->>ʷ m := castWk rfl h (𝟙ʷ n)

end WkPreCat

open WkPreCat

class WkSetoid (α : Type u) [WkPreCat α] where
  wkSetoid (n m : α) : Setoid (n ->>ʷ m)

instance WkPreCat.setoid (n m : α) [WkPreCat α] [WkSetoid α] : Setoid (n ->>ʷ m)
  := WkSetoid.wkSetoid n m

class WkWeakCat (α : Type u) [WkPreCat α] extends WkSetoid α where
  one_comp_eqv {n m : α} (ρ : n ->>ʷ m) : 𝟙ʷ n ≫ʷ ρ ≈ ρ
  comp_one {n m : α} (ρ : n ->>ʷ m) : ρ ≫ʷ 𝟙ʷ m ≈ ρ
  comp_assoc {n m k l : α}
    (ρ : n ->>ʷ m) (σ : m ->>ʷ k) (τ : k ->>ʷ l)
    : (ρ ≫ʷ σ) ≫ʷ τ ≈ ρ ≫ʷ (σ ≫ʷ τ)

class WkCat (α : Type u) extends WkPreCat α where
  one_comp {n m : α} (ρ : n ->>ʷ m) : 𝟙ʷ n ≫ʷ ρ = ρ
  comp_one {n m : α} (ρ : n ->>ʷ m) : ρ ≫ʷ 𝟙ʷ m = ρ
  comp_assoc {n m k l : α}
    (ρ : n ->>ʷ m) (σ : m ->>ʷ k) (τ : k ->>ʷ l)
    : (ρ ≫ʷ σ) ≫ʷ τ = ρ ≫ʷ (σ ≫ʷ τ)

class WkPreLift (α : Type u) (β : Type w) [WkPreCat α] where
  liftObj : α → β → α
  liftWk {n m : α} (ρ : n ->>ʷ m) : ∀x : β, liftObj n x ->>ʷ liftObj m x

namespace WkPreCat

infixl:70 "↑,ʷ" => WkPreLift.liftObj

infixl:81 "↑ʷ" => WkPreLift.liftWk

end WkPreCat

class WkLift (α : Type u) (β : Type w) [WkPreCat α] extends WkPreLift α β where
  id_liftWk (n : α) (x : β) : (𝟙ʷ n) ↑ʷ x = 𝟙ʷ (n ↑,ʷ x)
  comp_liftWk {n m k : α} (ρ : n ->>ʷ m) (σ : m ->>ʷ k) (x : β) :
    (ρ ≫ʷ σ) ↑ʷ x = (ρ ↑ʷ x) ≫ʷ (σ ↑ʷ x)

class WkPrePave (α : Type u) (β : Type w) [WkPreCat α] where
  paveObj : β → α → α
  paveWk (x : β) {n m : α} (ρ : n ->>ʷ m) : paveObj x n ->>ʷ paveObj x m

namespace WkPreCat

infixl:70 "↓,ʷ" => WkPrePave.paveObj

infixr:81 "↓ʷ" => WkPrePave.paveWk

end WkPreCat

class WkPave (α : Type u) (β : Type w) [WkPreCat α] extends WkPrePave α β where
  paveWk_id (x : β) (n : α) : x ↓ʷ (𝟙ʷ n) = 𝟙ʷ (x ↓,ʷ n)
  paveWk_comp (x : β) {n m k : α} (ρ : n ->>ʷ m) (σ : m ->>ʷ k) :
    x ↓ʷ (ρ ≫ʷ σ) = x ↓ʷ ρ ≫ʷ x ↓ʷ σ

class WkGlue (α : Type u) (β : Type w) [WkPreCat α] [WkPreCat β] extends WkPreLift α β where
  wkGlue {n m : α} {x y : β} (ρ : n ->>ʷ m) (σ : x ->>ʷ y) : (n ↑,ʷ x) ->>ʷ (m ↑,ʷ y)
  wkGlue_id {n m : α} (ρ : n ->>ʷ m) (x : β) : wkGlue ρ (𝟙ʷ x) = ρ ↑ʷ x

class GlueWk (α : Type u) (β : Type w) [WkPreCat α] [WkPreCat β] extends WkPrePave α β where
  glueWk {x y : β}  (σ : x ->>ʷ y) {n m : α} (ρ : n ->>ʷ m) : (x ↓,ʷ n) ->>ʷ (y ↓,ʷ m)
  id_glueWk (x : β) {n m : α} (ρ : n ->>ʷ m) : glueWk (𝟙ʷ x) ρ = x ↓ʷ ρ

class WkEmpty (α : Type u) [WkPreCat α] [Zero α] where
  dropObj_uniq {n : α} (ρ σ : n ->>ʷ 0) : ρ = σ

class WkDrop (α : Type u) [WkPreCat α] [Zero α] where
  dropObj (n : α) : n ->>ʷ 0

class WkPreAdd (α : Type u) [WkPreCat α] [Add α] where
  addWk {n m n' m' : α} (ρ : n ->>ʷ m) (σ : n' ->>ʷ m') : n + n' ->>ʷ m + m'

namespace WkPreCat

infixl:70 "+ʷ" => WkPreAdd.addWk

end WkPreCat

class WkAdd (α : Type u) [WkPreCat α] [Add α] [WkPreAdd α] where
  addWk_id (n m : α) : 𝟙ʷ n +ʷ 𝟙ʷ m = 𝟙ʷ (n + m)
  addWk_comp {n m k n' m' k' : α}
    (ρ : n ->>ʷ m) (ρ' : n' ->>ʷ m')
    (σ : m ->>ʷ k) (σ' : m' ->>ʷ k')
    : (ρ ≫ʷ σ) +ʷ (ρ' ≫ʷ σ') = (ρ +ʷ ρ') ≫ʷ (σ +ʷ σ')

class WkAddAssoc (α : Type u) [WkPreCat α] [AddSemigroup α] [WkPreAdd α] where
  addWk_assoc {n n' m m' k k' : α} (ρ : n ->>ʷ n') (σ : m ->>ʷ m') (τ : k ->>ʷ k')
    : castWk (add_assoc _ _ _) (add_assoc _ _ _) ((ρ +ʷ σ) +ʷ τ) = ρ +ʷ (σ +ʷ τ)

class WkAddZero (α : Type u) [WkPreCat α] [AddZeroClass α] [WkPreAdd α] where
  zero_addWk {n m : α} (ρ : n ->>ʷ m) : castWk (zero_add _) (zero_add _) (𝟙ʷ 0 +ʷ ρ) = ρ
  addWk_zero {n m : α} (ρ : n ->>ʷ m) : castWk (add_zero _) (add_zero _) (ρ +ʷ 𝟙ʷ 0) = ρ

-- NOTE: this gives us the structure of a _strict_ monoidal category

class WkAddMonoid  (α : Type u) [WkPreCat α] [AddMonoid α] [WkPreAdd α]
  extends WkAddAssoc α, WkAddZero α

namespace WkPreCat

notation "𝟘ʷ" => WkDrop.dropObj

end WkPreCat

class WkPreDLift (α : Type u) (β : α → Type w) [WkPreCat α] where
  dliftObj : (n : α) → β n → α
  wkObj {n m : α} (ρ : n ->>ʷ m) : β m → β n
  wkObj_comp {n m k : α} (ρ : n ->>ʷ m) (σ : m ->>ʷ k) : wkObj (ρ ≫ʷ σ) = wkObj ρ ∘ wkObj σ
  dliftWk {n m : α} (ρ : n ->>ʷ m) : ∀x : β m, (dliftObj n (wkObj ρ x)) ->>ʷ (dliftObj m x)

structure WkPreHom (α : Type u) (γ : Type v) [WkPreCat α] [WkPreCat γ] where
  ctx : α → γ
  map {n m : α} (ρ : n ->>ʷ m) : ctx n ->>ʷ ctx m

structure WkHom (α : Type u) (γ : Type v) [WkPreCat α] [WkPreCat γ] extends WkPreHom α γ where
  map_id (n : α) : map (𝟙ʷ n) = 𝟙ʷ (ctx n)
  map_comp {n m k : α} (ρ : n ->>ʷ m) (σ : m ->>ʷ k) : map (ρ ≫ʷ σ) = map ρ ≫ʷ map σ
