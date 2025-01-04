import Mathlib.Data.Sum.Basic
import Mathlib.Data.Set.Functor
import Mathlib.Control.Monad.Writer

open Sum

open Functor

open LawfulMonad

variable {m : Type u → Type v}

theorem ReaderT.run_def {α : Type u} (x : ReaderT ρ m α) (r : ρ)
  : x.run r = x r := rfl

theorem WriterT.run_mk {α ω : Type u} [Monoid ω] (a : m (α × ω))
  : (WriterT.mk a).run = a := rfl

variable [Monad m]

def casesM {α β : Type u} (x : m (α ⊕ β)) (f : α → m γ) (g : β → m γ) : m γ :=
  x >>= Sum.elim f g

def sumM {α β α' β' : Type u} (f : α → m α') (g : β → m β') : α ⊕ β → m (α' ⊕ β')
  := Sum.elim (map inl ∘ f) (map inr ∘ g)

theorem sumM_comp_inl {α β α' β' : Type u} (f : α → m α') (g : β → m β')
  : sumM f g ∘ inl = map inl ∘ f := by funext a; simp [sumM]

theorem sumM_comp_inr {α β α' β' : Type u} (f : α → m α') (g : β → m β')
  : sumM f g ∘ inr = map inr ∘ g := by funext a; simp [sumM]

theorem elim_kleisli {α β γ γ' : Type u}
  (f : α → m γ) (g : β → m γ) (h : γ → m γ')
  : Sum.elim f g >=> h = Sum.elim (f >=> h) (g >=> h) := by
  funext a; cases a <;> simp [Bind.kleisliRight]

theorem ReaderT.bind_applied
  {α β : Type u} (x : ReaderT ρ m α) (f : α → ReaderT ρ m β) (r : ρ)
  : (x >>= f) r = (x.run r) >>= (λa => f a r) := rfl

theorem ReaderT.kleisli_bind {α β γ : Type u} (f : α → ReaderT ρ m β) (g : β → ReaderT ρ m γ)
  : f >=> g = λa r => (f a).run r >>= (λb => (g b).run r) := rfl

theorem ReaderT.kleisli_bind_applied {α β γ : Type u}
  (f : α → ReaderT ρ m β) (g : β → ReaderT ρ m γ) (a : α) (r : ρ)
  : ((f >=> g) a).run r = (f a).run r >>= (λb => (g b).run r) := rfl

theorem ReaderT.kleisli_kleisli {α β γ : Type u}
  (f : α → ReaderT ρ m β) (g : β → ReaderT ρ m γ)
  : f >=> g = λa r => ((λa => (f a).run r) >=> (λb => (g b).run r)) a := rfl

theorem ReaderT.kleisli_kleisli_applied {α β γ : Type u}
  (f : α → ReaderT ρ m β) (g : β → ReaderT ρ m γ) (a : α) (r : ρ)
  : ((f >=> g) a).run r = ((λa => (f a).run r) >=> (λb => (g b).run r)) a := rfl

def WriterT.append {ω α} [Monoid ω] (a : WriterT ω m α) (w : ω) : WriterT ω m α
  := WriterT.mk ((λ(a, w') => (a, w' * w)) <$> a.run)

@[simp]
theorem WriterT.run_append {ω α} [Monoid ω] (a : WriterT ω m α) (w : ω)
  : (a.append w).run = (λ(a, w') => (a, w' * w)) <$> a.run := rfl

def WriterT.prepend {ω α} [Monoid ω] (w : ω) (a : WriterT ω m α) : WriterT ω m α
  := WriterT.mk ((λ(a, w') => (a, w * w')) <$> a.run)

@[simp]
theorem WriterT.run_prepend {ω α} [Monoid ω] (w : ω) (a : WriterT ω m α)
  : (a.prepend w).run = (λ(a, w') => (a, w * w')) <$> a.run := rfl

@[simp]
theorem WriterT.run_bind {α β ω : Type u} [Monoid ω] (a : WriterT ω m α) (f : α → WriterT ω m β)
  : (a >>= f).run = a.run >>= (λ(b, w) => ((f b).prepend w).run) := rfl

theorem WriterT.run_kleisli_bind {α β γ ω : Type u} [Monoid ω]
  (f : α → WriterT ω m β) (g : β → WriterT ω m γ) (a : α)
  : ((f >=> g) a).run = (f a).run >>= (λ(b, w) => ((g b).prepend w).run) := rfl

theorem StateT.kleisli_bind {α β γ σ : Type u} (f : α → StateT σ m β) (g : β → StateT σ m γ)
  : f >=> g = λa s => (f a).run s >>= (λ(b, s) => (g b).run s) := rfl

@[simp]
theorem WriterT.run_map {α β ω : Type u} [Monoid ω] (f : α → β) (a : WriterT ω m α)
  : (f <$> a).run = (λ(a, w) => (f a, w)) <$> a.run := rfl

@[simp]
theorem WriterT.run_pure {α ω : Type u} [Monoid ω] (a : α)
  : (pure a : WriterT ω m α).run = pure (a, 1) := rfl

variable [LawfulMonad m]

@[simp]
theorem WriterT.append_one {ω α} [Monoid ω] (a : WriterT ω m α)
  : a.append 1 = a := by ext; simp [WriterT.append, WriterT.mk, WriterT.run]

@[simp]
theorem WriterT.append_pure {ω α} [Monoid ω] (a : α) (w : ω)
  : (pure a : WriterT ω m α).append w = WriterT.mk (pure (a, w))
  := by simp [append, pure, WriterT.run]

@[simp]
theorem WriterT.append_mk_pure {ω α} [Monoid ω] (a : α) (w w' : ω)
  : (WriterT.mk (pure (a, w))).append w' = WriterT.mk (M := m) (pure (a, w * w'))
  := by simp [append, pure, WriterT.run, WriterT.mk]

@[simp]
theorem WriterT.prepend_one {ω α} [Monoid ω] (a : WriterT ω m α)
  : a.prepend 1 = a := by ext; simp [WriterT.prepend, WriterT.mk, WriterT.run]

@[simp]
theorem WriterT.prepend_pure {ω α} [Monoid ω] (w : ω) (a : α)
  : (pure a : WriterT ω m α).prepend w = WriterT.mk (pure (a, w))
  := by simp [prepend, pure, WriterT.run]

@[simp]
theorem WriterT.prepend_mk_pure {ω α} [Monoid ω] (w w' : ω) (a : α)
  : (WriterT.mk (pure (a, w))).prepend w' = WriterT.mk (M := m) (pure (a, w' * w))
  := by simp [prepend, pure, WriterT.run, WriterT.mk]

theorem WriterT.prepend_bind {ω α β} [Monoid ω] (a : WriterT ω m α) (f : α → WriterT ω m β) (w : ω)
  : (a >>= f).prepend w = a.prepend w >>= f := by ext; simp [mul_assoc]

theorem bind_kleisli {α β γ : Type u} (x : m α) (f : α → m β) (g : β → m γ)
  : x >>= (f >=> g) = x >>= f >>= g := by rw [bind_assoc]; rfl

theorem WriterT.prepend_kleisli {α β γ ω : Type u} [Monoid ω]
  (f : α → WriterT ω m β) (g : β → WriterT ω m γ) (a : α) (w : ω)
  : ((f >=> g) a).prepend w = (WriterT.mk (pure (a, w))) >>= (f >=> g) := by
  ext; simp [Bind.kleisliRight, prepend_bind, run_mk]

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
  funext a; simp only [Bind.kleisliRight, map_eq_pure_bind]; simp

theorem map_inr_kleisli_elim {ι α β γ : Type u} (h : ι → m β) (f : α → m γ) (g : β → m γ)
  : map inr ∘ h >=> Sum.elim f g = h >=> g := by
  funext a; simp only [Bind.kleisliRight, map_eq_pure_bind]; simp

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
