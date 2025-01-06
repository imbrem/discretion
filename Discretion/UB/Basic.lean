import Discretion.Monad.Ordered
import Discretion.Order.Lattice
import Discretion.Nonempty.Set

def UB (α) := WithTop (NSet α)

namespace UB

instance instPartialOrder {α} : PartialOrder (UB α) := (inferInstance : PartialOrder (WithTop _))

instance instOrderTop {α} : OrderTop (UB α) := (inferInstance : OrderTop (WithTop _))

abbrev some (as : NSet α) : UB α := WithTop.some as

instance coeNSet {α} : Coe (NSet α) (UB α) := ⟨some⟩

@[elab_as_elim, cases_eliminator]
def casesOn {motive : UB α → Sort _}
  (top : motive ⊤) (coe : ∀as : NSet α, motive as) : (as : UB α) → motive as
  | ⊤ => top
  | (as : NSet α) => coe as

instance instMax {α} : Max (UB α) := (inferInstance : Max (WithTop (NSet α)))

instance instSemilatticeSup {α} : SemilatticeSup (UB α)
  := (inferInstance : SemilatticeSup (WithTop (NSet α)))

open Classical

-- TODO: this should be a typeclass...
noncomputable def nsSup (s : NSet (UB α)) : UB α
  := if h : ⊤ ∈ s then ⊤ else NSet.sUnion (α := α) ⟨UB.some ⁻¹' s, by
    have ⟨s, b, hb⟩ := s;
    cases b; contradiction
    case coe b => exact ⟨b, hb⟩
  ⟩

@[simp]
theorem nsSup_top_mem (s : NSet (UB α)) : ⊤ ∈ s → nsSup s = ⊤ := by intro h; simp [nsSup, h]

noncomputable instance instSupSet [Nonempty α] : SupSet (UB α) where
  sSup s := if h : s.Nonempty then nsSup ⟨s, h⟩ else ⊤
