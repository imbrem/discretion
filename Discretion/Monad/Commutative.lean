import Mathlib.Tactic.Convert
import Mathlib.Data.Set.Functor

class SeqComm (f : Type u → Type v) [Applicative f] : Prop where
  seq_comm {α β : Type u} (l : f α) (r : f β) :
    Prod.mk <$> l <*> r = (λr (l : α) => (l, r)) <$> r <*> l

theorem SeqComm.bind_pair_comm {m : Type u → Type v} [Monad m] [LawfulMonad m] [SeqComm m]
  {α β : Type u} (l : m α) (r : m β) :
  (do let l <- l; let r <- r; return (l, r)) = (do let r <- r; let l <- l; return (l, r)) := by
  convert SeqComm.seq_comm l r using 1 <;>
  simp [seq_eq_bind_map]

theorem SeqComm.bind_comm {m : Type u → Type v} [Monad m] [LawfulMonad m] [SeqComm m]
  {α β : Type u} (l : m α) (r : m β) (f : α → β → m γ) :
  (do let l <- l; let r <- r; f l r) = (do let r <- r; let l <- l; f l r) := calc
  _ = (do let l <- l; let r <- r; pure (l, r)) >>= (λ(l, r) => f l r) := by simp
  _ = _ := by rw [bind_pair_comm]; simp

instance Id.instSeqComm : SeqComm Id where seq_comm _ _ := rfl

instance Option.instSeqComm : SeqComm Option where
  seq_comm l r := by cases l <;> cases r <;> rfl

instance ReaderT.instSeqComm {ρ : Type u} {m : Type u → Type v} [Monad m] [SeqComm m]
  : SeqComm (ReaderT ρ m) where
  seq_comm l r := by ext ctx; simp [SeqComm.seq_comm]

--TODO: `WriterT` is commutative if the underlying monoid + monad is

--TODO: the free vector space monad is commutative, and therefore Linear Algebra (TM)

attribute [local instance] Set.monad

instance Set.instSeqComm : SeqComm Set where
  seq_comm l r := by
    ext ⟨a, b⟩;
    simp only [fmap_eq_image, seq_eq_set_seq, mem_seq_iff,
    mem_image, exists_exists_and_eq_and, Prod.mk.injEq, exists_eq_right_right]
    exact ⟨λ⟨ha, hb⟩ => ⟨_, hb, _, ha, rfl, rfl⟩, λ⟨_, ha, _, hb, rfl, rfl⟩ => ⟨hb, ha⟩⟩
