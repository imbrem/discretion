import Discretion.Premonoidal.CopyDrop

open CategoryTheory

open CategoryTheory.MonoidalCategory

open CategoryTheory.Monoidal

variable {C : Type u} [Category C] [MonoidalCategoryStruct C] {D : Type v}

namespace CategoryTheory

namespace Monoidal

def tensorLL (f : D → C) : List D → C := List.foldr (λA B => f A ⊗ B) (𝟙_ C)

def tensorLR (f : D → C) : List D → C := List.foldl (λA B => A ⊗ f B) (𝟙_ C)

-- TODO: tensorLL is isomorphic to tensorLR in a braided premonoidal category

def tensorLL1 (f : D → C) : List D → C
  | [] => 𝟙_ C
  | [A] => f A
  | A::Γ => f A ⊗ tensorLL1 f Γ

-- TODO: tensorLL is isomorphic to tensorLL1 in a premonoidal category

def tensorLR1 (f : D → C) : List D → C
  | [] => 𝟙_ C
  | [A] => f A
  | A::Γ => tensorLR1 f Γ ⊗ f A

-- TODO: tensorLR is isomorphic to tensorLR1 in a premonoidal category

variable {Q} [Zero Q] [DecidableEq Q]

def tensorZL (f : D → C) : (Γ : List D) → Vector' Q Γ.length → C
  | [], .nil => 𝟙_ C
  | A::Γ, .cons q qs => (if q = 0 then 𝟙_ C else f A) ⊗ tensorZL f Γ qs

def tensorZR (f : D → C) : (Γ : List D) → Vector' Q Γ.length → C
  | [], .nil => 𝟙_ C
  | A::Γ, .cons q qs => tensorZR f Γ qs ⊗ (if q = 0 then 𝟙_ C else f A)

-- TODO: tensorZL is isomorphic to tensorZR in a braided premonoidal category

def tensorZL0 (f : D → C) : (Γ : List D) → Vector' Q Γ.length → C
  | [], .nil => 𝟙_ C
  | A::Γ, .cons q qs => if q = 0 then tensorZL0 f Γ qs else f A ⊗ tensorZL0 f Γ qs

-- TODO: tensorZL is isomorphic to tensorZL0 in a premonoidal category

def tensorZR0 (f : D → C) : (Γ : List D) → Vector' Q Γ.length → C
  | [], .nil => 𝟙_ C
  | A::Γ, .cons q qs => if q = 0 then tensorZR0 f Γ qs else tensorZR0 f Γ qs ⊗ f A

-- TODO: tensorZR is isomorphic to tensorZR0 in a premonoidal category

end Monoidal

end CategoryTheory
