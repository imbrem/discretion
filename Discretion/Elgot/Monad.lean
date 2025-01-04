import Mathlib.Data.Sum.Basic
import Mathlib.Data.Set.Functor
import Mathlib.Control.Monad.Writer

import Discretion.Utils.Kleisli

open Sum

open Functor

open LawfulMonad

open Sum

section MonadParam

variable (m : Type u → Type v) [Monad m]

class MonadFix where
  mfix : {α : Type u} → (α → m α) → m α

open MonadFix

/- Inspired by : https://leventerkok.github.io/papers/erkok-thesis.pdf -/
class LawfulMonadFix [MonadFix m] where
  left_shrink {α β : Type u} (f : α → β → m α) (a : m β)
    : mfix (λx => a >>= f x) = a >>= λy => mfix (λx => f x y)
  sliding {α β : Type u} (f : α → m β) (h : β → α)
    : mfix (map h ∘ f) = map h (mfix (f ∘ h))
  nesting {α β : Type u} (f : α → α → m α)
    : mfix (λx => mfix (λy => f x y)) = mfix (λx => f x x)

class RecursiveMonadFix [MonadFix m] where
  bind_fix {α : Type u} (f : α → m α)
    : mfix f >>= f = mfix f

class MonadIterate where
  iterate : {α β : Type u} → (α → m (β ⊕ α)) → α → m β

open MonadIterate

class ElgotMonad extends LawfulMonad m, MonadIterate m where
  fixpoint {α β : Type u} (f : α → m (β ⊕ α))
    : f >=> Sum.elim pure (iterate f) = iterate f
  naturality {α β γ: Type u} (f: α -> m (β ⊕ α)) (g: β -> m γ)
    : (iterate f) >=> g = iterate (f >=> sumM g pure)
  codiagonal {α β: Type u} (f: α -> m ((β ⊕ α) ⊕ α))
    : iterate (iterate f) = iterate (f >=> Sum.elim pure (pure ∘ inr))
  uniformity {α β γ : Type u} (f : α → m (β ⊕ α)) (g : γ → m (β ⊕ γ)) (h : γ → α)
    : (f ∘ h) = g >=> sumM pure (pure ∘ h) → iterate f ∘ h = iterate g

theorem ElgotMonad.iterate_applied [ElgotMonad m]
  {α β : Type u} (f : α → m (β ⊕ α)) (a : α)
  : iterate f a = (f a) >>= Sum.elim pure (iterate f) := by
  conv => lhs; rw [<-fixpoint]
  simp [Bind.kleisliRight]

theorem ElgotMonad.iterate_applied' [ElgotMonad m]
  {α β : Type u} (f : α → m (β ⊕ α)) (a : α)
  : iterate f a = (do
    let x <- f a
    match x with
    | inl b => pure b
    | inr a => iterate f a)
  := by
  rw [iterate_applied]
  congr
  funext x; cases x <;> rfl

theorem ElgotMonad.uniformity_applied [ElgotMonad m]
  {α β γ : Type u} (f : α → m (β ⊕ α)) (g : γ → m (β ⊕ γ)) (h : γ → α)
  (H : (f ∘ h) = g >=> sumM pure (pure ∘ h)) (a : γ)
  : iterate f (h a) = iterate g a := congrFun (ElgotMonad.uniformity f g h H) a

-- Based on proof of lemma 31 of Goncharov and Schröder (2018, Guarded Traced Categories)
theorem ElgotMonad.squaring [ElgotMonad m]
  {α β : Type u} (f : α → m (β ⊕ α))
  : iterate (f >=> Sum.elim (pure ∘ inl) f) = iterate f := by
  generalize hw : (Sum.elim
            (f >=> sumM pure (pure ∘ inr) >=> pure ∘ inl)
            (f >=> sumM (pure ∘ inl) (pure ∘ inl)) : _ → m ((β ⊕ (α ⊕ α)) ⊕ (α ⊕ α))) = w;
  have hwl : iterate (f >=> Sum.elim (pure ∘ inl) f) = iterate (iterate w) ∘ inr := by
    rw [uniformity]
    conv =>
      lhs
      rw [
        <-fixpoint, <-hw, elim_kleisli, elim_comp_inr, hw, <-kleisli_assoc, elim_sumM, <-fixpoint,
        <-hw, elim_kleisli, hw, kleisli_pure, comp_pure_kleisli, elim_comp_inl, kleisli_comp_pure,
        kleisli_comp_map, comp_map_kleisli, elim_comp_inl, kleisli_pure
      ]
    rw [
      <-kleisli_assoc, elim_kleisli, comp_pure_kleisli, sumM_comp_inl, map_comp_pure
    ]
  have hwi : Sum.elim (f >=> sumM pure (pure ∘ inr)) (f >=> sumM pure (pure ∘ inl))
              >=> sumM pure (pure ∘ Sum.elim id id)
            = f ∘ Sum.elim id id := by
    simp [elim_kleisli, <-kleisli_assoc, sumM_sumM, comp_pure_kleisli, sumM_pure_pure, comp_elim]
  have hwr : iterate (w >=> Sum.elim pure (pure ∘ inr)) ∘ inr = iterate f := by
    have hwi' := uniformity _ _ _ hwi.symm
    have hwf' : iterate f = (iterate f ∘ Sum.elim id id) ∘ inr := by simp [Function.comp_assoc]
    rw [
      <-hw, elim_kleisli, kleisli_comp_pure, kleisli_comp_map, comp_map_kleisli, elim_comp_inl,
      kleisli_pure, <-kleisli_assoc, elim_sumM, kleisli_pure, hwf', hwi', kleisli_comp_pure,
      <-map_comp_pure (f := inl)
    ]
    rfl
  cases hw
  apply Eq.trans hwl (Eq.trans _ hwr)
  rw [codiagonal]

-- Based on proof of lemma 31 of Goncharov and Schröder (2018, Guarded Traced Categories)
theorem ElgotMonad.dinaturality [ElgotMonad m]
  {α β γ : Type u} (f : α → m (β ⊕ γ)) (g : γ → m (β ⊕ α))
  : iterate (f >=> Sum.elim (pure ∘ inl) g)
    = f >=> Sum.elim pure (iterate (g >=> Sum.elim (pure ∘ inl) f)) := by
  generalize hh : Sum.elim (g >=> sumM pure (pure ∘ inr)) (f >=> sumM pure (pure ∘ inl)) = h
  have hhl : pure ∘ inl >=> iterate h = iterate (g >=> Sum.elim (pure ∘ inl) f) := by
    rw [comp_pure_kleisli, <-hh, <-squaring, uniformity]
    funext k
    simp only [Function.comp_apply, Bind.kleisliRight, elim_inl, bind_assoc]
    congr
    funext x
    cases x <;> simp [sumM, Bind.kleisliRight]
  have hhr : pure ∘ inr >=> iterate h = iterate (f >=> Sum.elim (pure ∘ inl) g) := by
    rw [comp_pure_kleisli, <-hh, <-squaring, uniformity]
    funext k
    simp only [Function.comp_apply, Bind.kleisliRight, elim_inr, bind_assoc]
    congr
    funext x
    cases x <;> simp [sumM, Bind.kleisliRight]
  rw [
    <-hhl, <-fixpoint (f := h), <-hh, kleisli_assoc, pure_inl_elim, <-kleisli_assoc,
    elim_sumM, kleisli_pure, hh, hhr
  ]
  conv =>
    lhs
    rw [<-fixpoint]
  rw [<-kleisli_assoc, elim_kleisli, pure_inl_elim]

end MonadParam

variable {m : Type u → Type v}

open MonadIterate

section MonadIterate

variable [MonadIterate m]

instance ReaderT.monad_iterate {ρ : Type u}
  : MonadIterate (ReaderT ρ m) where
  iterate f a := λr => iterate (λx => (f x).run r) a

theorem ReaderT.iterate_run {ρ α β : Type u}
  (f : α → ReaderT ρ m (β ⊕ α)) (a : α) (r : ρ)
  : (iterate f a).run r = iterate (λx => (f x).run r) a := rfl

theorem ReaderT.iterate_def {ρ α β : Type u}
  (f : α → ReaderT ρ m (β ⊕ α))
  : iterate f = λa r => iterate (λx => (f x).run r) a := rfl

theorem ReaderT.iterate_abs {m : Type u → Type v} [MonadIterate m] {ρ α β : Type u}
  (f : α → ReaderT ρ m (β ⊕ α)) (r : ρ)
  : (λa => (iterate f a).run r) = iterate (λx => (f x).run r) := rfl

end MonadIterate

section Monad

variable [Monad m]

instance ReaderT.elgot [E : ElgotMonad m] {α : Type u}
  : ElgotMonad (ReaderT α m) where
  fixpoint f := by
    ext a r
    rw [
      kleisli_bind_applied, iterate_run, <-E.fixpoint, Bind.kleisliRight,
      <-iterate_abs
    ]
    congr
    funext b
    cases b <;> rfl
  naturality f g := by
    ext a r
    simp only [iterate_run, kleisli_kleisli_applied]
    rw [E.naturality]
    congr
    funext a
    simp only [Bind.kleisliRight]
    congr
    funext b
    cases b <;> rfl
  codiagonal f := by
    ext a r
    simp only [iterate_run]
    rw [E.codiagonal]
    congr
    funext a
    simp only [Bind.kleisliRight]
    congr
    funext b
    casesm* (_ ⊕ _) <;> rfl
  uniformity f g h H := by
    ext a r
    simp only [Function.comp_apply, iterate_run]
    apply E.uniformity_applied
    funext a
    convert congrFun (congrFun H a) r
    simp only [Bind.kleisliRight, run_bind, bind_applied]
    congr
    funext b; cases b <;> rfl

def WriterT.runSum {ω α β : Type u} [Monoid ω] (a : WriterT ω m (α ⊕ β)) : m (α × ω ⊕ β × ω)
  := Equiv.sumProdDistrib _ _ _ <$> a.run

def WriterT.prependSum {ω α β : Type u} [Monoid ω] (w : ω) (a : WriterT ω m (α ⊕ β))
  := (λ| (inl a, w') => (inl (a, w * w')) | (inr b, w') => (inr (b, w * w'))) <$> a.run

theorem WriterT.prependSum_def'
  [LawfulMonad m] {ω α β : Type u} [Monoid ω] (w : ω) (a : WriterT ω m (α ⊕ β))
  : WriterT.prependSum w a = (a.prepend w).runSum
  := by
  simp [prependSum, prepend, runSum, run_mk]
  congr
  funext ⟨x, w⟩
  cases x <;> rfl

instance WriterT.monad_iterate [MonadIterate m] {ω : Type u} [Monoid ω]
  : MonadIterate (WriterT ω m) where
  iterate f a := WriterT.mk (iterate (m := m) (λ(a, w) => ((f a).prependSum w)) (a, 1))

theorem WriterT.iterate_applied [MonadIterate m] {ω α β : Type u} [Monoid ω]
  (f : α → WriterT ω m (β ⊕ α)) (a)
  : iterate f a = WriterT.mk (iterate (m := m) (λ(a, w) => ((f a).prependSum w)) (a, 1)) := rfl

theorem WriterT.iterate_def [MonadIterate m] {ω α β : Type u} [Monoid ω]
  (f : α → WriterT ω m (β ⊕ α))
  : iterate f = (λa : α
    => WriterT.mk (iterate (m := m) (λ(a, w) => (f a).prependSum w) (a, 1))) := rfl

theorem WriterT.iterate_run [MonadIterate m] {ω α β : Type u} [Monoid ω]
  (f : α → WriterT ω m (β ⊕ α)) (a)
  : (iterate f a).run = iterate (m := m) (λ(a, w) => (f a).prependSum w) (a, 1) := rfl

-- -- TODO: use uniformity
-- theorem WriterT.prepend_iterate_run [E : ElgotMonad m] {ω α β : Type u} [Monoid ω]
--   (f : α → WriterT ω m (β ⊕ α)) (a) (w)
--   : ((iterate f a).prepend w).run
--   = iterate (m := m) (λ(a, w) => (f a).prependSum w) (a, w) := by
--   sorry

-- theorem WriterT.prepend_iterate [ElgotMonad m] {ω α β : Type u} [Monoid ω]
--   (f : α → WriterT ω m (β ⊕ α)) (a) (w)
--   : (iterate f a).prepend w
--   = WriterT.mk (iterate (m := m) (λ(a, w) => (f a).prependSum w) (a, w))
--   := prepend_iterate_run f a w

-- instance WriterT.elgot [E : ElgotMonad m] {ω : Type u} [Monoid ω]
--   : ElgotMonad (WriterT ω m) where
--   fixpoint f := by
--     ext a
--     rw [iterate_run, <-E.fixpoint]
--     simp [Bind.kleisliRight, prependSum]
--     congr
--     funext ⟨x, w⟩
--     cases x with
--     | inl => simp
--     | inr => simp; exact prepend_iterate_run _ _ _
--   naturality f g := by
--     ext a
--     sorry
--   codiagonal f := by
--     ext a
--     sorry
--   uniformity f g h H := by
--     ext a
--     sorry

instance StateT.monad_iterate [MonadIterate m] {σ : Type u}
  : MonadIterate (StateT σ m) where
  iterate f a s := (iterate (λ(a, s) => (f a s)
    >>= λ| (inl b, s) => pure (inl (b, s))
         | (inr a, s) => pure (inr (a, s)))) (a, s)

-- attribute [local instance] Set.monad

-- instance Set.instMonadIterate : MonadIterate Set where
--   iterate f a := sorry

-- instance Set.instElgotMonad : ElgotMonad Set where
--   fixpoint f := sorry
--   naturality f g := sorry
--   codiagonal f := sorry
--   uniformity f g h := sorry

-- instance SetM.instMonadIterate : MonadIterate SetM := Set.instMonadIterate

-- instance SetM.instElgotMonad : ElgotMonad SetM := Set.instElgotMonad
