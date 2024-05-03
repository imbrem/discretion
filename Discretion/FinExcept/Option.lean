import Discretion.FinExcept.Defs
import Discretion.WithDefault

open Finset

namespace FinExcept

theorem WithTop.untop_eq_iff {α : Type _} {a b : WithTop α} (ha : a ≠ ⊤) (hb : b ≠ ⊤)
    : a.untop ha = b.untop hb ↔ a = b
  := match a, b, ha, hb with
  | (a : α), (b : α), _, _ => by simp

theorem WithBot.unbot_eq_iff {α : Type _} {a b : WithBot α} (ha : a ≠ ⊥) (hb : b ≠ ⊥)
    : a.unbot ha = b.unbot hb ↔ a = b
  := match a, b, ha, hb with
  | (a : α), (b : α), _, _ => by simp

theorem WithDefault.undefault_eq_iff {α : Type _} {a b : WithDefault α}
  (ha : a ≠ default) (hb : b ≠ default) : a.undefault ha = b.undefault hb ↔ a = b
  := match a, b, ha, hb with
  | (a : α), (b : α), _, _ => by simp

section GetSet

variable [DecidableEq α] [DecidableEq M]
  {f g : α →ᶠ[{none}] (Option M)} {x y : α} {a : M}

theorem not_mem_support_iff_none : x ∉ f.support ↔ f x = none := not_mem_support_iff

theorem mem_support_iff_isSome : x ∈ f.support ↔ (f x).isSome := by
  simp only [mem_support_iff, Set.mem_singleton_iff, Option.isSome]
  split <;> simp [*]

theorem mem_support_of_eq_coe (h : f x = ↑a) : x ∈ f.support := by simp [h]

theorem mem_support_of_coe_eq (h : ↑a = f x) : x ∈ f.support := mem_support_of_eq_coe h.symm

/-- Get an element in the support of `f` -/
def get (f : α →ᶠ[{none}] (Option M)) (x : α) (hx : x ∈ f.support) : M
  := (f x).get (mem_support_iff_isSome.mp hx)

@[simp]
theorem get_eq (hx : x ∈ f.support) : ↑(f.get x hx) = f x := by simp [get]

theorem get_eq_of_eq_coe (h : f x = ↑a) : f.get x (mem_support_of_eq_coe h) = a := by
  simp [get, h]

theorem get_eq_of_coe_eq (h : ↑a = f x) : f.get x (mem_support_of_coe_eq h) = a := by
  simp [get, <-h]

theorem get_eq_iff_eq_at (hx : x ∈ f.support) (hy : y ∈ f.support)
  : f.get x hx = f.get y hy ↔ f x = f y := by
  simp only [get, Option.get]; split; split; simp [*]

/-- This is the same as `f.update x ↑a`, but with nicer defeqs for the support -/
def cons (x : α) (a : M) (f : α →ᶠ[{none}] (Option M)) : α →ᶠ[{none}] (Option M) where
  support := insert x f.support
  toFun := Function.update f x a
  mem_support_toFun y := by simp only [Function.update]; aesop

theorem cons_apply : (f.cons x a) y = if y = x then ↑a else f y
  := by simp [cons, Function.update]

theorem cons_head : (f.cons x a) x = ↑a
  := by simp [cons, Function.update]

theorem cons_tail (h : y ≠ x) : (f.cons x a) y = f y
  := by simp [cons, Function.update, h]

@[simp, norm_cast]
theorem coe_cons : (f.cons x a : α → Option M) = Function.update f x a := rfl

@[simp]
theorem default_cons : cons x a default = single none x ↑a := by
  ext
  rw [single_eq_update]
  rfl

theorem support_cons :
    support (f.cons x a) = insert x f.support := rfl

theorem cons_eq_update (x : α) (a : M) (f : α →ᶠ[{none}] (Option M))
  : cons x a f = f.update x a :=
  rfl

@[simp]
theorem cons_eq_self (h : x ∈ f.support)
  : f.cons x (f.get x h) = f := by simp [cons_eq_update]

theorem cons_comm (f : α →ᶠ[{none}] (Option M)) (h : x ≠ y) (a b : M) :
  cons x a (cons y b f) = cons y b (cons x a f) := by simp only [cons_eq_update, f.update_comm h]

@[simp]
theorem cons_idem (x : α) (a : M) (f : α →ᶠ[{none}] (Option M))
  : cons x a (cons x a f) = cons x a f :=
  by simp only [cons_eq_update, f.update_idem]

theorem eq_at_of_cons_eq_self (h : cons x a f = f) : a = f x := by
  have h : cons x a f x = f x := by rw [h];
  simp only [cons_apply, ↓reduceIte] at h
  rw [h]

theorem cons_eq_self_of_eq_at (h : a = f x) : cons x a f = f := by
  ext
  simp only [cons_apply]
  split <;> simp [*]

@[simp]
theorem cons_eq_self_iff : cons x a f = f ↔ a = f x
  := ⟨eq_at_of_cons_eq_self, cons_eq_self_of_eq_at⟩

@[simp]
theorem eq_self_cons_iff : f = cons x a f ↔ f x = a
  := ⟨Eq.symm ∘ eq_at_of_cons_eq_self ∘ Eq.symm, Eq.symm ∘ cons_eq_self_of_eq_at ∘ Eq.symm⟩

theorem ne_cons_self_iff : f ≠ cons x a f ↔ f x ≠ a
  := by rw [Ne.def, eq_self_cons_iff]

theorem cons_ne_self_iff : cons x a f ≠ f ↔ ↑a ≠ f x
  := by rw [Ne.def, cons_eq_self_iff]

theorem mem_support_cons : x ∈ (cons x a f).support := by simp

theorem mem_support_cons_of_mem_support : y ∈ f.support → y ∈ (cons x a f).support
  := by rw [support_cons]; aesop

theorem mem_support_of_cons_eq (h : cons x a f = g) : x ∈ g.support := h ▸ mem_support_cons

theorem mem_support_of_eq_cons : g = cons x a f → x ∈ g.support
  := mem_support_of_cons_eq ∘ Eq.symm

theorem cons_eq_iff : cons x a f = g ↔ g x = a ∧ ∀y, y ≠ x -> f y = g y
  := ⟨λh => ⟨h ▸ cons_head, λy hy => h ▸ (cons_tail hy).symm⟩,
      λ⟨_, _⟩ => by ext y; simp only [cons_apply]; split <;> simp [*]⟩

theorem eq_cons_iff : g = cons x a f ↔ a = g x ∧ ∀y, y ≠ x -> g y = f y
  := ⟨λh => ⟨h ▸ cons_head.symm, λy hy => h ▸ cons_tail hy⟩,
      λ⟨_, _⟩ => by ext y; simp only [cons_apply]; split <;> simp [*]⟩

@[simp]
theorem get_cons_head : (cons x a f).get x (mem_support_cons) = a := by simp [get]

theorem get_cons_tail (h : y ≠ x) (hy : y ∈ f.support)
  : (cons x a f).get y (mem_support_cons_of_mem_support hy) = f.get y hy := by simp [get, h]

end GetSet

section WithTop

theorem not_mem_support_iff_top [Top M] {f : α →ᶠ[{⊤}] M}
  : x ∉ f.support ↔ f x = ⊤ := not_mem_support_iff

theorem mem_support_iff_ne_top [Top M] {f : α →ᶠ[{⊤}] M}
  : x ∈ f.support ↔ f x ≠ ⊤ := by simp [not_mem_support_iff_top]

variable [DecidableEq α] [DecidableEq M]
  {f g : α →ᶠ[{⊤}] (WithTop M)} {x y : α} {a : M}

theorem mem_support_of_eq_coe_top : f x = ↑a → x ∈ f.support := mem_support_of_eq_coe

theorem mem_support_of_coe_eq_top : ↑a = f x → x ∈ f.support := mem_support_of_coe_eq

/-- Get an element in the support of `f` -/
def untop (f : α →ᶠ[{⊤}] (WithTop M)) (x : α) (hx : x ∈ f.support) : M
  := (f x).untop (mem_support_iff_ne_top.mp hx)

theorem untop_eq_get {hx : x ∈ f.support} : f.untop x hx = f.get x hx := by
  simp only [untop, get, WithTop.untop, Option.get]
  split
  rename_i h _
  split
  rename_i h' _
  cases h.symm.trans h'
  rfl

@[simp]
theorem untop_eq (hx : x ∈ f.support) : ↑(f.untop x hx) = f x := by simp [untop]

theorem untop_eq_of_eq_coe (h : f x = ↑a) : f.untop x (mem_support_of_eq_coe h) = a := by
  simp [untop, h]

theorem untop_eq_of_coe_eq (h : ↑a = f x) : f.untop x (mem_support_of_coe_eq h) = a := by
  simp [untop, <-h]

theorem untop_eq_iff_eq_at (hx : x ∈ f.support) (hy : y ∈ f.support)
  : f.untop x hx = f.untop y hy ↔ f x = f y
  := untop_eq_get.symm ▸ untop_eq_get.symm ▸ get_eq_iff_eq_at hx hy

/-- This is the same as `f.update x ↑a`, but with nicer defeqs for the support -/
def cons_top (x : α) (a : M) (f : α →ᶠ[{⊤}] (WithTop M)) : α →ᶠ[{⊤}] (WithTop M) where
  support := insert x f.support
  toFun := Function.update f x a
  mem_support_toFun y := by simp only [Function.update]; aesop

theorem cons_top_eq_cons : @cons_top = @cons := rfl

theorem cons_top_apply : (f.cons_top x a) y = if y = x then ↑a else f y := cons_apply

theorem cons_top_head : (f.cons_top x a) x = ↑a := cons_head

theorem cons_top_tail : y ≠ x → (f.cons_top x a) y = f y := cons_tail

@[simp, norm_cast]
theorem coe_cons_top : (f.cons_top x a : α → WithTop M) = Function.update f x a := rfl

@[simp]
theorem top_cons_top : cons_top x a ⊤ = single ⊤ x ↑a := by
  ext
  rw [single_eq_update]
  rfl

@[simp]
theorem default_cons_top : cons_top x a default = single ⊤ x ↑a := top_cons_top

theorem support_cons_top :
    support (f.cons_top x a) = insert x f.support := rfl

theorem cons_top_eq_update (x : α) (a : M) (f : α →ᶠ[{⊤}] (WithTop M))
  : cons_top x a f = f.update x a :=
  rfl

@[simp]
theorem cons_top_eq_self (h : x ∈ f.support)
  : f.cons_top x (f.untop x h) = f := by simp [cons_top_eq_update]

theorem cons_top_comm (f : α →ᶠ[{none}] (Option M)) (h : x ≠ y) (a b : M) :
  cons_top x a (cons_top y b f) = cons_top y b (cons_top x a f)
  := by simp only [cons_top_eq_update, f.update_comm h]

@[simp]
theorem cons_top_idem (x : α) (a : M) (f : α →ᶠ[{none}] (Option M))
  : cons_top x a (cons_top x a f) = cons_top x a f :=
  by simp only [cons_top_eq_update, f.update_idem]

theorem eq_at_of_cons_top_eq_self (h : cons_top x a f = f) : a = f x := by
  have h : cons_top x a f x = f x := by rw [h];
  simp only [cons_top_apply, ↓reduceIte] at h
  rw [h]

theorem cons_top_eq_self_of_eq_at (h : a = f x) : cons_top x a f = f := by
  ext
  simp only [cons_top_apply]
  split <;> simp [*]

@[simp]
theorem cons_top_eq_self_iff : cons_top x a f = f ↔ a = f x := cons_eq_self_iff

@[simp]
theorem eq_self_cons_top_iff : f = cons_top x a f ↔ f x = a := eq_self_cons_iff

theorem ne_cons_top_self_iff : f ≠ cons_top x a f ↔ f x ≠ a := ne_cons_self_iff

theorem cons_top_ne_self_iff : cons_top x a f ≠ f ↔ ↑a ≠ f x := cons_ne_self_iff

theorem mem_support_cons_top : x ∈ (cons_top x a f).support := mem_support_cons

theorem mem_support_cons_top_of_mem_support : y ∈ f.support → y ∈ (cons_top x a f).support
  := mem_support_cons_of_mem_support

theorem mem_support_of_cons_top_eq (h : cons_top x a f = g) : x ∈ g.support := h ▸ mem_support_cons

theorem mem_support_of_eq_cons_top : g = cons_top x a f → x ∈ g.support
  := mem_support_of_eq_cons

theorem cons_top_eq_iff : cons_top x a f = g ↔ g x = a ∧ ∀y, y ≠ x -> f y = g y := cons_eq_iff

theorem eq_cons_top_iff : g = cons_top x a f ↔ a = g x ∧ ∀y, y ≠ x -> g y = f y := eq_cons_iff

@[simp]
theorem untop_cons_head : (cons_top x a f).untop x (mem_support_cons) = a := by simp [untop]

theorem untop_cons_tail (h : y ≠ x) (hy : y ∈ f.support)
  : (cons_top x a f).untop y (mem_support_cons_of_mem_support hy) = f.untop y hy
  := by simp [untop, h]

end WithTop

section WithBot

theorem not_mem_support_iff_bot [Bot M] {f : α →ᶠ[{⊥}] M}
  : x ∉ f.support ↔ f x = ⊥ := not_mem_support_iff

theorem mem_support_iff_ne_bot [Bot M] {f : α →ᶠ[{⊥}] M}
  : x ∈ f.support ↔ f x ≠ ⊥ := by simp [not_mem_support_iff_bot]

variable [DecidableEq α] [DecidableEq M]
  {f g : α →ᶠ[{⊥}] (WithBot M)} {x y : α} {a : M}

theorem mem_support_of_eq_coe_bot : f x = ↑a → x ∈ f.support := mem_support_of_eq_coe

theorem mem_support_of_coe_eq_bot : ↑a = f x → x ∈ f.support := mem_support_of_coe_eq

/-- Get an element in the support of `f` -/
def unbot (f : α →ᶠ[{⊥}] (WithBot M)) (x : α) (hx : x ∈ f.support) : M
  := (f x).unbot (mem_support_iff_ne_bot.mp hx)

theorem unbot_eq_get {hx : x ∈ f.support} : f.unbot x hx = f.get x hx := untop_eq_get

@[simp]
theorem unbot_eq (hx : x ∈ f.support) : ↑(f.unbot x hx) = f x := untop_eq hx

theorem unbot_eq_of_eq_coe (h : f x = ↑a) : f.unbot x (mem_support_of_eq_coe h) = a
  := untop_eq_of_eq_coe h

theorem unbot_eq_of_coe_eq (h : ↑a = f x) : f.unbot x (mem_support_of_coe_eq h) = a
  := untop_eq_of_coe_eq h

theorem unbot_eq_iff_eq_at (hx : x ∈ f.support) (hy : y ∈ f.support)
  : f.unbot x hx = f.unbot y hy ↔ f x = f y
  := untop_eq_iff_eq_at hx hy

/-- This is the same as `f.update x ↑a`, but with nicer defeqs for the support -/
def cons_bot (x : α) (a : M) (f : α →ᶠ[{⊥}] (WithBot M)) : α →ᶠ[{⊥}] (WithBot M) where
  support := insert x f.support
  toFun := Function.update f x a
  mem_support_toFun y := by simp only [Function.update]; aesop

theorem cons_bot_apply : (f.cons_bot x a) y = if y = x then ↑a else f y := cons_apply

theorem cons_bot_head : (f.cons_bot x a) x = ↑a := cons_head

theorem cons_bot_tail : y ≠ x → (f.cons_bot x a) y = f y := cons_tail

@[simp, norm_cast]
theorem coe_cons_bot : (f.cons_bot x a : α → WithBot M) = Function.update f x a := rfl

@[simp]
theorem bot_cons_bot : cons_bot x a ⊥ = single ⊥ x ↑a := top_cons_top

@[simp]
theorem default_cons_bot : cons_bot x a default = single ⊥ x ↑a := bot_cons_bot

theorem support_cons_bot :
    support (f.cons_bot x a) = insert x f.support := rfl

theorem cons_bot_eq_update (x : α) (a : M) (f : α →ᶠ[{⊥}] (WithBot M))
  : cons_bot x a f = f.update x a :=
  rfl

@[simp]
theorem cons_bot_eq_self (h : x ∈ f.support) : f.cons_bot x (f.unbot x h) = f := cons_top_eq_self h

theorem cons_bot_comm (f : α →ᶠ[{none}] (Option M)) (h : x ≠ y) (a b : M) :
  cons_bot x a (cons_bot y b f) = cons_bot y b (cons_bot x a f) := cons_top_comm f h a b

@[simp]
theorem cons_bot_idem (x : α) (a : M) (f : α →ᶠ[{none}] (Option M))
  : cons_bot x a (cons_bot x a f) = cons_bot x a f := cons_top_idem x a f

theorem eq_at_of_cons_bot_eq_self (h : cons_bot x a f = f) : a = f x := eq_at_of_cons_top_eq_self h

theorem cons_bot_eq_self_of_eq_at (h : a = f x) : cons_bot x a f = f := cons_top_eq_self_of_eq_at h

@[simp]
theorem cons_bot_eq_self_iff : cons_bot x a f = f ↔ a = f x := cons_eq_self_iff

@[simp]
theorem eq_self_cons_bot_iff : f = cons_bot x a f ↔ f x = a := eq_self_cons_iff

theorem ne_cons_bot_self_iff : f ≠ cons_bot x a f ↔ f x ≠ a := ne_cons_self_iff

theorem cons_bot_ne_self_iff : cons_bot x a f ≠ f ↔ ↑a ≠ f x := cons_ne_self_iff

theorem mem_support_cons_bot : x ∈ (cons_bot x a f).support := mem_support_cons

theorem mem_support_cons_bot_of_mem_support : y ∈ f.support → y ∈ (cons_bot x a f).support
  := mem_support_cons_of_mem_support

theorem mem_support_of_cons_bot_eq (h : cons_bot x a f = g) : x ∈ g.support := h ▸ mem_support_cons

theorem mem_support_of_eq_cons_bot : g = cons_bot x a f → x ∈ g.support
  := mem_support_of_eq_cons

theorem cons_bot_eq_iff : cons_bot x a f = g ↔ g x = a ∧ ∀y, y ≠ x -> f y = g y := cons_eq_iff

theorem eq_cons_bot_iff : g = cons_bot x a f ↔ a = g x ∧ ∀y, y ≠ x -> g y = f y := eq_cons_iff

@[simp]
theorem unbot_cons_head : (cons_bot x a f).unbot x (mem_support_cons) = a := by simp [unbot]

theorem unbot_cons_tail (h : y ≠ x) (hy : y ∈ f.support)
  : (cons_bot x a f).unbot y (mem_support_cons_of_mem_support hy) = f.unbot y hy
  := by simp [unbot, h]

end WithBot

section WithDefault

theorem not_mem_support_iff_default [Inhabited M] {f : α →ᶠ[{default}] M}
  : x ∉ f.support ↔ f x = default := not_mem_support_iff

theorem mem_support_iff_ne_default [Inhabited M] {f : α →ᶠ[{default}] M}
  : x ∈ f.support ↔ f x ≠ default := mem_support_iff_ne

variable [DecidableEq α] [DecidableEq M]
  {f g : α →ᶠ[{default}] (WithDefault M)} {x y : α} {a : M}

theorem mem_support_of_eq_coe_default : f x = ↑a → x ∈ f.support := mem_support_of_eq_coe

theorem mem_support_of_coe_eq_default : ↑a = f x → x ∈ f.support := mem_support_of_coe_eq

/-- Get an element in the support of `f` -/
def undefault (f : α →ᶠ[{default}] (WithDefault M)) (x : α) (hx : x ∈ f.support) : M
  := (f x).undefault (mem_support_iff_ne_default.mp hx)

theorem undefault_eq_get {hx : x ∈ f.support} : f.undefault x hx = f.get x hx := untop_eq_get

@[simp]
theorem undefault_eq (hx : x ∈ f.support) : ↑(f.undefault x hx) = f x := untop_eq hx

theorem undefault_eq_of_eq_coe (h : f x = ↑a) : f.undefault x (mem_support_of_eq_coe h) = a
  := untop_eq_of_eq_coe h

theorem undefault_eq_of_coe_eq (h : ↑a = f x) : f.undefault x (mem_support_of_coe_eq h) = a
  := untop_eq_of_coe_eq h

theorem undefault_eq_iff_eq_at (hx : x ∈ f.support) (hy : y ∈ f.support)
  : f.undefault x hx = f.undefault y hy ↔ f x = f y
  := untop_eq_iff_eq_at hx hy

/-- This is the same as `f.update x ↑a`, but with nicer defeqs for the support -/
def cons_default (x : α) (a : M) (f : α →ᶠ[{default}] (WithDefault M))
  : α →ᶠ[{default}] (WithDefault M) where
  support := insert x f.support
  toFun := Function.update f x a
  mem_support_toFun y := by simp only [Function.update]; aesop

theorem cons_default_apply : (f.cons_default x a) y = if y = x then ↑a else f y := cons_apply

theorem cons_default_head : (f.cons_default x a) x = ↑a := cons_head

theorem cons_default_tail : y ≠ x → (f.cons_default x a) y = f y := cons_tail

@[simp, norm_cast]
theorem coe_cons_default : (f.cons_default x a : α → WithDefault M) = Function.update f x a := rfl

@[simp]
theorem default_cons_default : cons_default x a default = single default x ↑a := bot_cons_bot

theorem support_cons_default :
    support (f.cons_default x a) = insert x f.support := rfl

theorem cons_default_eq_update (x : α) (a : M) (f : α →ᶠ[{default}] (WithDefault M))
  : cons_default x a f = f.update x a :=
  rfl

@[simp]
theorem cons_default_eq_self (h : x ∈ f.support) : f.cons_default x (f.undefault x h) = f
  := cons_top_eq_self h

theorem cons_default_comm (f : α →ᶠ[{default}] (WithDefault M)) (h : x ≠ y) (a b : M) :
  cons_default x a (cons_default y b f) = cons_default y b (cons_default x a f)
  := cons_top_comm f h a b

@[simp]
theorem cons_default_idem (x : α) (a : M) (f : α →ᶠ[{default}] (WithDefault M))
  : cons_default x a (cons_default x a f) = cons_bot x a f := cons_top_idem x a f

theorem eq_at_of_cons_default_eq_self (h : cons_default x a f = f) : a = f x
  := eq_at_of_cons_top_eq_self h

theorem cons_default_eq_self_of_eq_at (h : a = f x) : cons_default x a f = f
  := cons_top_eq_self_of_eq_at h

@[simp]
theorem cons_default_eq_self_iff : cons_default x a f = f ↔ a = f x := cons_eq_self_iff

@[simp]
theorem eq_self_cons_default_iff : f = cons_default x a f ↔ f x = a := eq_self_cons_iff

theorem ne_cons_default_self_iff : f ≠ cons_default x a f ↔ f x ≠ a := ne_cons_self_iff

theorem cons_default_ne_self_iff : cons_default x a f ≠ f ↔ ↑a ≠ f x := cons_ne_self_iff

theorem mem_support_cons_default : x ∈ (cons_default x a f).support := mem_support_cons

theorem mem_support_cons_default_of_mem_support : y ∈ f.support → y ∈ (cons_default x a f).support
  := mem_support_cons_of_mem_support

theorem mem_support_of_cons_default_eq (h : cons_default x a f = g) : x ∈ g.support
  := h ▸ mem_support_cons

theorem mem_support_of_eq_cons_default : g = cons_default x a f → x ∈ g.support
  := mem_support_of_eq_cons

theorem cons_default_eq_iff : cons_default x a f = g ↔ g x = a ∧ ∀y, y ≠ x -> f y = g y
  := cons_eq_iff

theorem eq_cons_default_iff : g = cons_default x a f ↔ a = g x ∧ ∀y, y ≠ x -> g y = f y
  := eq_cons_iff

@[simp]
theorem undefault_cons_head : (cons_default x a f).undefault x (mem_support_cons) = a
  := by simp [undefault]

theorem undefault_cons_tail (h : y ≠ x) (hy : y ∈ f.support)
  : (cons_default x a f).undefault y (mem_support_cons_of_mem_support hy) = f.undefault y hy
  := by simp [undefault, h]

end WithDefault

-- TODO: injectivity and monotonicity theorems

-- TODO: le_cons_iff and friends, Discrete Edition (TM)
