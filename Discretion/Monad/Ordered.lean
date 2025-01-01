import Discretion.Order.Discrete

instance Disc.instMonad : Monad Disc := Id.instMonad

instance Disc.instLawfulMonad : LawfulMonad Disc := Id.instLawfulMonad

instance DiscTop.instMonad : Monad DiscTop := (inferInstance : Monad Option)

instance DiscTop.instLawfulMonad : LawfulMonad DiscTop := (inferInstance : LawfulMonad Option)

instance DiscBot.instMonad : Monad DiscBot := (inferInstance : Monad Option)

instance DiscBot.instLawfulMonad : LawfulMonad DiscBot := (inferInstance : LawfulMonad Option)

class OrderedMonad (m : Type u → Type v) [Monad m] [∀α, LE (m α)] where
  bind_mono {α β} {a a' : m α} {f f' : α → m β} (ha : a ≤ a') (hf : f ≤ f') : a >>= f ≤ a' >>= f'

instance Disc.instOrderedMonad : OrderedMonad Disc where
  bind_mono ha hf := by cases ha; cases (DiscreteOrder.le_eq _ _ hf); rfl

-- instance DiscTop.instOrderedMonad : OrderedMonad DiscTop where
--   bind_mono ha hf := sorry

-- instance DiscBot.instOrderedMonad : OrderedMonad DiscBot where
--   bind_mono ha hf := sorry
