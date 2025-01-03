import Discretion.Order.Discrete
import Mathlib.Data.Set.Functor

instance Disc.instMonad : Monad Disc := Id.instMonad

instance Disc.instLawfulMonad : LawfulMonad Disc := Id.instLawfulMonad

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

class OrderedMonad (m : Type u → Type v) [Monad m] [∀α, LE (m α)] where
  bind_mono {α β} {a a' : m α} {f f' : α → m β} (ha : a ≤ a') (hf : f ≤ f') : a >>= f ≤ a' >>= f'

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

class TopMonad (m : Type u → Type v) [Monad m] [∀α, Top (m α)] where
  bind_top {α β} (f : α → m β) : ⊤ >>= f = ⊤

instance DiscTop.instTopMonad : TopMonad DiscTop where
  bind_top _ := rfl

class BotMonad (m : Type u → Type v) [Monad m] [∀α, Bot (m α)] where
  bind_bot {α β} (f : α → m β) : ⊥ >>= f = ⊥

instance DiscBot.instBotMonad : BotMonad DiscBot where
  bind_bot _ := rfl

-- TODO: DiscBounded is a TopMonad and a BotMonad

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
