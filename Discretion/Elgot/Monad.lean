import Mathlib.Data.Sum.Basic
import Mathlib.Data.Set.Functor

import Discretion.Utils.Kleisli

open Sum

open Functor

open LawfulMonad

section Fixpoints

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
    have hwf' : iterate f = (iterate f ∘ Sum.elim id id) ∘ inr := by simp [Function.comp.assoc]
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

end Fixpoints

attribute [local instance] Set.monad

instance Set.instMonadIterate : MonadIterate Set where
  iterate f a := sorry

instance Set.instElgotMonad : ElgotMonad Set where
  fixpoint f := sorry
  naturality f g := sorry
  codiagonal f := sorry
  uniformity f g h := sorry

instance SetM.instMonadIterate : MonadIterate SetM := Set.instMonadIterate

instance SetM.instElgotMonad : ElgotMonad SetM := Set.instElgotMonad
