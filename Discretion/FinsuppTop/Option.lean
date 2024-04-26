import Discretion.FinsuppTop.Defs

open Finset

namespace FinsuppTop

theorem WithTop.untop_eq_iff {α : Type _} {a b : WithTop α} (ha : a ≠ ⊤) (hb : b ≠ ⊤)
    : a.untop ha = b.untop hb ↔ a = b
  := match a, b, ha, hb with
  | (a : α), (b : α), _, _ => by simp

section GetSet

variable [DecidableEq α] [DecidableEq M] {f g : α →ᵀ (WithTop M)} {x y : α} {a : M}

theorem not_mem_support_iff_none : x ∉ f.support ↔ f x = none := not_mem_support_iff

theorem mem_support_of_eq_coe (h : f x = ↑a) : x ∈ f.support := by simp [h]

theorem mem_support_of_coe_eq (h : ↑a = f x) : x ∈ f.support := mem_support_of_eq_coe h.symm

/-- Get an element in the support of `f` -/
def get (f : α →ᵀ (WithTop M)) (x : α) (hx : x ∈ f.support) : M
  := (f x).untop (mem_support_iff.mp hx)

@[simp]
theorem get_eq (hx : x ∈ f.support) : ↑(f.get x hx) = f x := by simp [get]

theorem get_eq_of_eq_coe (h : f x = ↑a) : f.get x (mem_support_of_eq_coe h) = a := by
  simp [get, h]

theorem get_eq_of_coe_eq (h : ↑a = f x) : f.get x (mem_support_of_coe_eq h) = a := by
  simp [get, <-h]

theorem get_eq_iff_eq_at (hx : x ∈ f.support) (hy : y ∈ f.support)
  : f.get x hx = f.get y hy ↔ f x = f y := by
  simp only [get, WithTop.untop_eq_iff]

/-- This is the same as `f.update x ↑a`, but with nicer defeqs for the support -/
def cons (x : α) (a : M) (f : α →ᵀ (WithTop M)) : α →ᵀ (WithTop M) where
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
theorem coe_cons : (f.cons x a : α → WithTop M) = Function.update f x a := rfl

@[simp]
theorem top_cons : cons x a ⊤ = single x ↑a := by
  ext
  rw [single_eq_update]
  rfl

theorem support_cons :
    support (f.cons x a) = insert x f.support := rfl

theorem cons_eq_update (x : α) (a : M) (f : α →ᵀ (WithTop M)) : cons x a f = f.update x a :=
  DFunLike.ext' rfl

@[simp]
theorem cons_eq_self (h : x ∈ f.support) : f.cons x (f.get x h) = f := by simp [cons_eq_update]

theorem cons_comm (f : α →ᵀ (WithTop M)) (h : x ≠ y) (a b : M) :
  cons x a (cons y b f) = cons y b (cons x a f) := by simp only [cons_eq_update, f.update_comm h]

@[simp]
theorem cons_idem (x : α) (a : M) (f : α →ᵀ (WithTop M)) : cons x a (cons x a f) = cons x a f :=
  by simp only [cons_eq_update, f.update_idem]

theorem eq_at_of_cons_eq_self (h : cons x a f = f) : a = f x := by
  have h : cons x a f x = f x := by rw [h];
  simp only [cons_apply, ↓reduceIte] at h
  rw [h]

theorem cons_eq_self_of_eq_at (h : a = f x) : cons x a f = f := by
  ext
  simp only [cons_apply, ite_eq_right_iff]
  intro h'; cases h'; rw [h]

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

-- TODO: injectivity and monotonicity theorems

-- TODO: le_cons_iff and friends, Discrete Edition (TM)

end GetSet
