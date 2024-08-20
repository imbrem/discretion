import Mathlib.Data.Sum.Basic

open Sum

open Functor

open LawfulMonad

section Combinator

variable {m : Type u → Type v} [Monad m]

def casesM {α β : Type u} (x : m (α ⊕ β)) (f : α → m γ) (g : β → m γ) : m γ :=
  x >>= Sum.elim f g

def sumM {α β α' β' : Type u} (f : α → m α') (g : β → m β') : α ⊕ β → m (α' ⊕ β')
  := Sum.elim (map inl ∘ f) (map inr ∘ g)

end Combinator

section Kleisli

variable {m : Type u → Type v} [Monad m]

theorem elim_kleisli {α β γ γ' : Type u}
  (f : α → m γ) (g : β → m γ) (h : γ → m γ')
  : Sum.elim f g >=> h = Sum.elim (f >=> h) (g >=> h) := by
  funext a; cases a <;> simp [Bind.kleisliRight]

theorem sumM_comp_inl {α β α' β' : Type u} (f : α → m α') (g : β → m β')
  : sumM f g ∘ inl = map inl ∘ f := by funext a; simp [sumM]

theorem sumM_comp_inr {α β α' β' : Type u} (f : α → m α') (g : β → m β')
  : sumM f g ∘ inr = map inr ∘ g := by funext a; simp [sumM]

variable [LawfulMonad m]

theorem kleisli_assoc {α β γ : Type u} (f : α → m β) (g : β → m γ) (h : γ → m δ)
  : f >=> g >=> h = (f >=> g) >=> h := by
  funext a
  simp only [Bind.kleisliRight]
  rw [bind_assoc]
  rfl

theorem kleisli_comp_pure {α β γ : Type u} {f : α → m β} {g : β → γ}
  : f >=> pure ∘ g = map g ∘ f := by
  funext a
  simp only [Bind.kleisliRight, Function.comp_apply, map_eq_pure_bind]
  rfl

@[simp]
theorem kleisli_pure {α β : Type u} {f : α → m β}
  : f >=> pure = f := by funext a; simp [Bind.kleisliRight]

@[simp]
theorem pure_kleisli {α β : Type u} {f : α → m β}
  : pure >=> f = f := by funext a; simp [Bind.kleisliRight]

theorem comp_pure_kleisli {α β γ : Type u} (f : α → β) (g : β → m γ)
  : pure ∘ f >=> g = g ∘ f := by funext a; simp [Bind.kleisliRight]

theorem inl_kleisli {α β γ : Type u} (f : α ⊕ β → m γ)
  : pure ∘ inl >=> f = f ∘ inl := by rw [comp_pure_kleisli]

theorem inr_kleisli {α β γ : Type u} (f : α ⊕ β → m γ)
  : pure ∘ inr >=> f = f ∘ inr := by rw [comp_pure_kleisli]

theorem pure_inl_elim {α β γ : Type u} (f : α → m γ) (g : β → m γ)
  : pure ∘ inl >=> Sum.elim f g = f := by funext a; simp [Bind.kleisliRight]

theorem pure_inr_elim {α β γ : Type u} (f : α → m γ) (g : β → m γ)
  : pure ∘ inr >=> Sum.elim f g = g := by funext a; simp [Bind.kleisliRight]

theorem inl_sumM {α β α' β' : Type u} (f : α → m α') (g : β → m β')
  : pure ∘ inl >=> sumM f g = f >=> pure ∘ inl := by rw [sumM, pure_inl_elim, kleisli_comp_pure]

theorem inr_sumM {α β α' β' : Type u} (f : α → m α') (g : β → m β')
  : pure ∘ inr >=> sumM f g = g >=> pure ∘ inr := by rw [sumM, pure_inr_elim, kleisli_comp_pure]

theorem kleisli_comp_map {α β γ γ' : Type u} (f : α → m β) (g : β → m γ) (h : γ → γ')
  : f >=> (map h ∘ g) = map h ∘ (f >=> g) := by simp [<-kleisli_comp_pure, kleisli_assoc]

theorem comp_map_kleisli {α β β' γ : Type u} (f : α → m β) (g : β → β') (h : β' → m γ)
  : (map g ∘ f) >=> h = f >=> (h ∘ g) := by
  rw [<-kleisli_comp_pure, <-kleisli_assoc, comp_pure_kleisli]

theorem map_inl_kleisli_elim {ι α β γ : Type u} (h : ι → m α) (f : α → m γ) (g : β → m γ)
  : map inl ∘ h >=> Sum.elim f g = h >=> f := by
  funext a; simp [Bind.kleisliRight, map_eq_pure_bind]

theorem map_inr_kleisli_elim {ι α β γ : Type u} (h : ι → m β) (f : α → m γ) (g : β → m γ)
  : map inr ∘ h >=> Sum.elim f g = h >=> g := by
  funext a; simp [Bind.kleisliRight, map_eq_pure_bind]

theorem map_inl_sumM {ι α β α' β' : Type u} (h : ι → m α) (f : α → m α') (g : β → m β')
  : map inl ∘ h >=> sumM f g = map inl ∘ (h >=> f)
  := by simp [sumM, map_inl_kleisli_elim, kleisli_comp_map]

theorem elim_sumM {α β α' β' γ : Type u}
  (f : α → m α') (g : β → m β') (l : α' → m γ) (r : β' → m γ)
  : sumM f g >=> Sum.elim l r = Sum.elim (f >=> l) (g >=> r) := by
  rw [sumM, elim_kleisli, map_inl_kleisli_elim, map_inr_kleisli_elim]

theorem sumM_sumM {α₀ β₀ α₁ β₁ α₂ β₂ : Type u}
  (f₁ : α₀ → m α₁) (g₁ : β₀ → m β₁) (f₂ : α₁ → m α₂) (g₂ : β₁ → m β₂)
  : sumM f₁ g₁ >=> sumM f₂ g₂ = sumM (f₁ >=> f₂) (g₁ >=> g₂) := by
  simp [sumM, elim_kleisli, comp_map_kleisli, kleisli_comp_map]

theorem map_comp_pure {α β : Type u} (f : α → β)
  : map f ∘ pure = pure (f := m) ∘ f := by funext a; simp

theorem sumM_pure_pure {α β : Type u} : sumM (m := m) (α := α) (β := β) pure pure = pure := by
  simp [sumM, map_comp_pure]

end Kleisli

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
