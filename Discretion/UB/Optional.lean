import Discretion.Monad.Ordered
import Discretion.Order.Lattice

def UB? (α) := WithTop (Set α)

abbrev UB?.some (a : Set α) : UB? α := WithTop.some a

instance UB?.instCoeTC : CoeTC (Set α) (UB? α) := ⟨UB?.some⟩

instance UB?.instEmptyCollection : EmptyCollection (UB? α) := ⟨UB?.some ∅⟩

@[simp]
theorem UB?.some_empty : UB?.some (α := α) ∅ = ∅ := rfl

instance UB?.instPartialOrder : PartialOrder (UB? α)
  := (inferInstance : PartialOrder (WithTop _))

instance UB?.instBoundedOrder : BoundedOrder (UB? α)
  := (inferInstance : BoundedOrder (WithTop _))

@[elab_as_elim, cases_eliminator]
def UB?.casesOn {motive : UB? α → Sort _}
  (top : motive ⊤) (coe : ∀as : Set α, motive as) : (as : UB? α) → motive as
  | ⊤ => top
  | (as : Set α) => coe as

@[simp]
theorem UB?.coe_ne_top (as : Set α) : (as : UB? α) ≠ (⊤ : UB? α) := by intro h; cases h

@[simp]
theorem UB?.top_ne_coe (as : Set α) : (⊤ : UB? α) ≠ (as : UB? α) := by intro h; cases h

@[simp]
theorem UB?.coe_eq_coe {as bs : Set α} : (as : UB? α) = bs ↔ as = bs := WithTop.coe_eq_coe

def UB?.freeze : UB? α → Set α
  | ⊤ => Set.univ
  | (as : Set α) => as

@[simp]
theorem UB?.freeze_top : UB?.freeze (⊤ : UB? α) = Set.univ := rfl

@[simp]
theorem UB?.freeze_coe (as : Set α) : UB?.freeze as = as := rfl

instance UB?.instSingleton : Singleton α (UB? α) where
  singleton a := UB?.some {a}

@[simp]
theorem UB?.some_singleton (a : α) : UB?.some {a} = {a} := rfl

@[simp]
theorem UB?.freeze_singleton (a : α) : UB?.freeze {a} = {a} := rfl

@[simp]
theorem UB?.singleton_ne_top (a : α) : {a} ≠ (⊤ : UB? α) := by intro x; cases x

instance UB?.instInsert : Insert α (UB? α) where
  insert a | ⊤ => ⊤ | (as : Set α) => UB?.some <| insert a as

@[simp]
theorem UB?.insert_top (a : α) : insert a ⊤ = (⊤ : UB? α) := rfl

@[simp]
theorem UB?.insert_coe (a : α) (as : Set α)
  : insert (γ := UB? α) a as = insert (γ := Set α) a as := rfl

@[simp]
theorem UB?.freeze_insert (a : α) (as : UB? α) : UB?.freeze (insert a as) = insert a as.freeze := by
  cases as <;> simp

instance UB?.instLawfulSingleton : LawfulSingleton α (UB? α) where
  insert_emptyc_eq x := by simp [<-UB?.some_empty]

instance UB?.instLattice : Lattice (UB? α)
  := (inferInstance : Lattice (WithTop _))

instance UB?.instMembership : Membership α (UB? α) where
  mem as a := a ∈ as.freeze

@[simp]
theorem UB?.mem_def (a : α) (as : UB? α) : a ∈ as ↔ a ∈ as.freeze := by rfl

theorem UB?.mem_top (a : α) : a ∈ (⊤ : UB? α) := by simp

theorem UB?.mem_coe_iff (a : α) (as : Set α) : a ∈ (as : UB? α) ↔ a ∈ as := by simp

theorem UB?.mem_some_iff (a : α) (as : Set α) : a ∈ (UB?.some as : UB? α) ↔ a ∈ as := by simp

theorem UB?.mem_singleton_iff (a b : α) : a ∈ ({b} : UB? α) ↔ a = b := by simp

theorem UB?.coe_inf (as bs : Set α)
  : (min (α := Set α) as bs : UB? α) = (as : UB? α) ⊓ (bs : UB? α) := rfl

theorem UB?.coe_sup (as bs : Set α)
  : (max (α := Set α) as bs : UB? α) = (as : UB? α) ⊔ (bs : UB? α) := rfl

@[simp]
theorem UB?.freeze_inf (as bs : UB? α) : (as ⊓ bs).freeze = as.freeze ∩ bs.freeze := by
  cases as <;> cases bs <;> simp [<-UB?.coe_inf]

@[simp]
theorem UB?.freeze_sup (as bs : UB? α) : (as ⊔ bs).freeze = as.freeze ∪ bs.freeze := by
  cases as <;> cases bs <;> simp [<-UB?.coe_sup]

theorem UB?.mem_inf_iff (a : α) (as bs : UB? α) : a ∈ as ⊓ bs ↔ a ∈ as ∧ a ∈ bs
  := by simp

theorem UB?.mem_sup_iff (a : α) (as bs : UB? α) : a ∈ as ⊔ bs ↔ a ∈ as ∨ a ∈ bs
  := by simp

@[simp]
theorem UB?.not_mem_empty (a : α) : a ∉ (∅ : UB? α)
  := by simp [Membership.mem, EmptyCollection.emptyCollection, Set.Mem]

def UB?.bindSet (f : Set α → UB? β) : UB? α → UB? β
  | ⊤ => ⊤
  | (as : Set α) => f as

def UB?.liftSet (f : Set α → Set β) : UB? α → UB? β
  := UB?.bindSet (UB?.some ∘ f)

open Classical

noncomputable instance UB?.instCompleteLattice : CompleteLattice (UB? α)
  := (inferInstance : CompleteLattice (WithTop _))

@[simp]
theorem UB?.freeze_top' : UB?.freeze (Top.top (α := WithTop (Set α))) = Set.univ
  := rfl

@[simp]
theorem UB?.coe_ne_top' (as : Set α) : (as : UB? α) ≠ (Top.top (α := WithTop (Set α))) := by
  intro h; cases h

@[simp]
theorem UB?.top_ne_coe' (as : Set α) : (Top.top (α := WithTop (Set α))) ≠ (as : UB? α) := by
  intro h; cases h

@[simp]
theorem UB?.singleton_ne_top' (a : α) : ({a} : UB? α) ≠ (Top.top (α := WithTop (Set α))) := by
  intro h; cases h

@[simp]
theorem UB?.freeze_sSup (as : Set (UB? α)) : UB?.freeze (sSup as) = ⋃as' ∈ as, UB?.freeze as' := by
  simp only [sSup, Set.mem_preimage]; split
  case isTrue h =>
    ext k
    simp only [freeze_top', Set.mem_univ, Set.mem_iUnion, exists_prop, true_iff]
    exact ⟨⊤, h, by simp⟩
  case isFalse h =>
    ext k
    simp only [freeze_coe, Set.mem_setOf_eq, Set.mem_iUnion, exists_prop]
    constructor
    · intro ⟨a, ha, hk⟩; exact ⟨a, ha, hk⟩
    · intro ⟨a, ha, hk⟩; cases a; contradiction; exact ⟨_, ha, hk⟩

@[simp]
theorem UB?.freeze_sInf (as : Set (UB? α)) : UB?.freeze (sInf as) = ⋂as' ∈ as, UB?.freeze as' := by
  simp only [sInf, Set.mem_preimage]; split
  case isTrue h =>
    rw [Set.subset_singleton_iff_eq] at h
    cases h <;> simp [*]
  case isFalse h =>
    ext k
    simp only [freeze_coe, Set.mem_setOf_eq, Set.mem_iInter]
    constructor
    · intro h' as' has'; cases as'; simp; simp [h' _ has']
    · intro h' as' has'; exact h' _ has'

@[simp]
theorem UB?.freeze_iSup (as : ι → UB? α) : UB?.freeze (iSup as) = ⋃i : ι, UB?.freeze (as i)
  := by simp [iSup]

@[simp]
theorem UB?.freeze_iInf (as : ι → UB? α) : UB?.freeze (iInf as) = ⋂i : ι, UB?.freeze (as i)
  := by simp [iInf]

theorem UB?.mem_sSup_iff (a : α) (as : Set (UB? α)) : a ∈ sSup as ↔ ∃as' ∈ as, a ∈ as'
  := by simp

theorem UB?.mem_sInf_iff (a : α) (as : Set (UB? α)) : a ∈ sInf as ↔ ∀as' ∈ as, a ∈ as'
  := by simp

noncomputable instance UB?.instMonad : Monad UB? where
  pure a := {a}
  bind a f := bindSet (λa => ⨆ i ∈ a, f i) a

@[simp]
theorem UB?.bind_top (f : α → UB? β) : bind ⊤ f = ⊤ := rfl

@[simp]
theorem UB?.map_top (f : α → β) : f <$> (⊤ : UB? α) = (⊤ : UB? β) := rfl

@[simp]
theorem UB?.bind_coe (f : α → UB? β) (as : Set α)
  : bind (as : UB? α) f = ⨆ i ∈ as, f i := rfl

@[simp]
theorem UB?.bind_empty (f : α → UB? β) : bind ∅ f = ∅ := by simp [bind, bindSet]; rfl

@[simp]
theorem UB?.map_empty (f : α → β) : f <$> (∅ : UB? α) = ∅ := by simp [Functor.map, bindSet]; rfl

-- @[simp]
-- theorem UB?.map_coe (f : α → β) (as : Set α)
--   : Functor.map (f := UB?) f (as : UB? α) = f '' as
--   := by
--   simp [Functor.map, bindSet]
--   stop
--   split
--   case isTrue h => have ⟨y, hy, hy'⟩ := h; exact (UB?.singleton_ne_top _ hy').elim
--   case isFalse h =>
--   simp only [coe_eq_coe]
--   ext k
--   simp only [Set.mem_setOf_eq, Set.mem_image]
--   constructor
--   · sorry
--   · sorry

-- instance UB?.instLawfulMonad : LawfulMonad UB? := LawfulMonad.mk' UB?
--   (id_map := λx => by cases x <;> simp)
--   (pure_bind := λx f => by simp [pure, bind, bindSet])
--   (bind_assoc := λx f g => by
--     cases x with
--     | top => simp
--     | coe a => sorry)

-- -- NOTE: setTerm is _not_ monotonic! Which... makes _some_ sense... but points at a need for a
-- -- disjoint ∅
-- noncomputable def UB?.setTerm (as : Set α) : UB? α := if as = ∅ then ⊤ else as

-- noncomputable def UB?.assertTerm : UB? α → UB? α := bindSet setTerm

-- noncomputable def UB?.setDet (as : Set α) : UB? α := if as.Nontrivial then ⊤ else as

-- noncomputable def UB?.assertDet : UB? α → UB? α := bindSet setDet
