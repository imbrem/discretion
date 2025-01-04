import Discretion.Order.Discrete
import Discretion.Nonempty.Set
import Mathlib.Data.Set.Functor
import Mathlib.Control.Monad.Writer

instance Disc.instMonad : Monad Disc := Id.instMonad

instance Disc.instLawfulMonad : LawfulMonad Disc := Id.instLawfulMonad

instance WithTop.instMonad : Monad WithTop := (inferInstance : Monad Option)

instance WithTop.instLawfulMonad : LawfulMonad WithTop := (inferInstance : LawfulMonad Option)

instance WithBot.instMonad : Monad WithBot := (inferInstance : Monad Option)

instance WithBot.instLawfulMonad : LawfulMonad WithBot := (inferInstance : LawfulMonad Option)

instance DiscTop.instMonad : Monad DiscTop := (inferInstance : Monad Option)

instance DiscTop.instLawfulMonad : LawfulMonad DiscTop := (inferInstance : LawfulMonad Option)

instance DiscBot.instMonad : Monad DiscBot := (inferInstance : Monad Option)

instance DiscBot.instLawfulMonad : LawfulMonad DiscBot := (inferInstance : LawfulMonad Option)

-- TODO: DiscBounded is also a LawfulMonad

@[simp]
theorem DiscTop.bind_top {α β} (f : α → DiscTop β) : ⊤ >>= f = ⊤ := rfl

@[simp]
theorem DiscTop.bind_some {α β} (a : α) (f : α → DiscTop β) : some a >>= f = f a := rfl

@[simp]
theorem DiscTop.bind_coe {α β} (a : α) (f : α → DiscTop β) : a >>= f = f a := rfl

@[simp]
theorem DiscBot.bind_bot {α β} (f : α → DiscBot β) : ⊥ >>= f = ⊥ := rfl

@[simp]
theorem DiscBot.bind_some {α β} (a : α) (f : α → DiscBot β) : some a >>= f = f a := rfl

@[simp]
theorem DiscBot.bind_coe {α β} (a : α) (f : α → DiscBot β) : a >>= f = f a := rfl

class OrderedMonad (m : Type u → Type v) [Bind m] [∀α, LE (m α)] where
  bind_mono {α β} {a a' : m α} {f f' : α → m β} (ha : a ≤ a') (hf : f ≤ f') : a >>= f ≤ a' >>= f'

theorem OrderedMonad.map_mono {m : Type u → Type v}
  [Monad m] [LawfulMonad m] [∀α, Preorder (m α)] [OrderedMonad m]
  {α β} (f : α → β) {a a' : m α} (ha : a ≤ a') : f <$> a ≤ f <$> a' := by
  simp only [map_eq_pure_bind]
  apply OrderedMonad.bind_mono ha (le_refl _)

instance Disc.instOrderedMonad : OrderedMonad Disc where
  bind_mono ha hf := by cases ha; cases (DiscreteOrder.le_eq _ _ hf); rfl

instance DiscTop.instOrderedMonad : OrderedMonad DiscTop where
  bind_mono ha hf := by
    apply DiscTop.leCases (h := ha)
    · intro a; simp
    · intro a; simp [hf a]

instance DiscBot.instOrderedMonad : OrderedMonad DiscBot where
  bind_mono ha hf := by
    apply DiscBot.leCases (h := ha)
    · intro a; simp
    · intro a; simp [hf a]

-- TODO: DiscBounded is also an OrderedMonad

class TopMonad (m : Type u → Type v) [Bind m] [∀α, Top (m α)] where
  bind_top {α β} (f : α → m β) : ⊤ >>= f = ⊤

instance DiscTop.instTopMonad : TopMonad DiscTop where
  bind_top _ := rfl

class BotMonad (m : Type u → Type v) [Bind m] [∀α, Bot (m α)] where
  bind_bot {α β} (f : α → m β) : ⊥ >>= f = ⊥

instance DiscBot.instBotMonad : BotMonad DiscBot where
  bind_bot _ := rfl

-- TODO: DiscBounded is a TopMonad and a BotMonad

abbrev DiscT (m : Type u → Type v) (α : Type u) := Disc (m α)

instance DiscT.instMonad (m : Type u → Type v) [Hm : Monad m] : Monad (DiscT m) := Hm

instance DiscT.instLawfulMonad (m : Type u → Type v) [Monad m] [Hm : LawfulMonad m]
  : LawfulMonad (DiscT m) := Hm

instance DiscT.instOrderedMonad (m : Type u → Type v) [Monad m] : OrderedMonad (DiscT m) where
  bind_mono ha hf := by cases ha; cases discrete_order hf; rfl

instance ReaderT.instLE (m : Type u → Type v) [∀α, LE (m α)] (ρ : Type u) : LE (ReaderT ρ m α)
  := (inferInstance : LE (ρ → m α))

instance ReaderT.instPreorder (m : Type u → Type v) [∀α, Preorder (m α)] (ρ : Type u)
  : Preorder (ReaderT ρ m α) := (inferInstance : Preorder (ρ → m α))

instance ReaderT.instPartialOrder (m : Type u → Type v) [∀α, PartialOrder (m α)] (ρ : Type u)
  : PartialOrder (ReaderT ρ m α) := (inferInstance : PartialOrder (ρ → m α))

instance ReaderT.instOrderedMonad (m : Type u → Type v) [Monad m] [∀α, LE (m α)] [OrderedMonad m]
  (ρ) : OrderedMonad (ReaderT ρ m) where
  bind_mono ha hf := by
    intro r
    simp only [bind, ReaderT.bind]
    apply OrderedMonad.bind_mono
    apply ha
    intro a
    apply hf

instance WriterT.instLE (ω) (m : Type u → Type v) (α) [∀α, LE (m α)] : LE (WriterT ω m α)
  := (inferInstance : LE (m (α × ω)))

instance WriterT.instPreorder (ω) (m : Type u → Type v) [∀α, Preorder (m α)] (α)
  : Preorder (WriterT ω m α)
  := (inferInstance : Preorder (m (α × ω)))

instance WriterT.instPartialOrder (ω) (m : Type u → Type v) [∀α, PartialOrder (m α)] (α)
  : PartialOrder (WriterT ω m α)
  := (inferInstance : PartialOrder (m (α × ω)))

instance WriterT.instOrderedMonad (ω) (m : Type u → Type v)
  [Monad m] [LawfulMonad m] [∀α, Preorder (m α)] [OrderedMonad m] [Monoid ω]
  : OrderedMonad (WriterT ω m) where
  bind_mono ha hf := by
    apply OrderedMonad.bind_mono (m := m) ha
    intro x
    apply OrderedMonad.map_mono
    apply hf

instance StateT.instLE (σ) (m : Type u → Type v) (α) [∀α, LE (m α)] : LE (StateT σ m α)
  := (inferInstance : LE (σ → m (α × σ)))

instance StateT.instPreorder (σ) (m : Type u → Type v) [∀α, Preorder (m α)] (α)
  : Preorder (StateT σ m α)
  := (inferInstance : Preorder (σ → m (α × σ)))

instance StateT.instPartialOrder (σ) (m : Type u → Type v) [∀α, PartialOrder (m α)] (α)
  : PartialOrder (StateT σ m α)
  := (inferInstance : PartialOrder (σ → m (α × σ)))

instance StateT.instOrderedMonad (σ) (m : Type u → Type v)
  [Monad m] [LawfulMonad m] [∀α, Preorder (m α)] [OrderedMonad m] : OrderedMonad (StateT σ m) where
  bind_mono ha hf := by
    intro s
    simp only [bind, StateT.bind]
    apply OrderedMonad.bind_mono (m := m)
    apply ha
    intro x
    apply hf

instance ExceptT.instLE (ε) (m : Type u → Type v) (α) [∀α, LE (m α)] : LE (ExceptT ε m α)
  := (inferInstance : LE (m (Except ε α)))

instance ExceptT.instPreorder (ε) (m : Type u → Type v) [∀α, Preorder (m α)] (α)
  : Preorder (ExceptT ε m α)
  := (inferInstance : Preorder (m (Except ε α)))

instance ExceptT.instPartialOrder (ε) (m : Type u → Type v) [∀α, PartialOrder (m α)] (α)
  : PartialOrder (ExceptT ε m α)
  := (inferInstance : PartialOrder (m (Except ε α)))

instance ExceptT.instOrderedMonad (ε) (m : Type u → Type v)
  [Monad m] [LawfulMonad m] [∀α, Preorder (m α)] [OrderedMonad m] : OrderedMonad (ExceptT ε m) where
  bind_mono ha hf := by
    apply OrderedMonad.bind_mono (m := m) ha
    intro x
    cases x <;>
    simp only [ExceptT.bindCont, le_refl]
    apply hf

instance OptionT.instLE (m : Type u → Type v) [∀α, LE (m α)] : LE (OptionT m α)
  := (inferInstance : LE (m (Option α)))

instance OptionT.instPreorder (m : Type u → Type v) [∀α, Preorder (m α)] : Preorder (OptionT m α)
  := (inferInstance : Preorder (m (Option α)))

instance OptionT.instPartialOrder (m : Type u → Type v) [∀α, PartialOrder (m α)]
  : PartialOrder (OptionT m α) := (inferInstance : PartialOrder (m (Option α)))

instance OptionT.instOrderedMonad (m : Type u → Type v)
  [Monad m] [LawfulMonad m] [∀α, Preorder (m α)] [OrderedMonad m] : OrderedMonad (OptionT m) where
  bind_mono ha hf := by
    apply OrderedMonad.bind_mono (m := m) ha
    intro x
    cases x <;>
    simp only [le_refl]
    apply hf

-- TODO: more interesting:
-- - the trace monad with an ordered monoid
-- - the nondeterminism monad

attribute [local instance] Set.monad

instance Set.ordered_monad : OrderedMonad Set where
  bind_mono ha hf := by
    simp only [bind_def, le_eq_subset, iUnion_subset_iff]
    intro a ha' b hb'
    simp only [mem_iUnion, exists_prop]
    exact ⟨a, ha ha', hf a hb'⟩

instance Set.bot_monad : BotMonad Set where
  bind_bot _ := by simp

-- Note: set is _not_ a `TopMonad`, since not every α → Set β is a covering!

instance NSet.instOrderedMonad : OrderedMonad NSet where
  bind_mono ha hf := by
    simp only [LE.le, bind, coe_subset_iff, coe_iUnion, Set.iUnion_coe_set, Set.iUnion_subset_iff]
    intro a ha' b hb'
    simp only [Set.mem_iUnion, exists_prop]
    exact ⟨a, ha ha', hf a hb'⟩
