-- Based on https://github.com/opencompl/lean-mlir/blob/8524c5836b840e2a4d7bffca9edb33d566a05f3d/SSA/Core/HVector.lean#L9

import Mathlib.Logic.Function.Defs
import Mathlib.Data.List.Basic

import Discretion.Vector.Basic

variable {α : Type u} {f : α → Type v}

inductive HVector {α : Type u} (f : α → Type v) : List α → Type _
  | nil : HVector f []
  | cons {a Γ} : f a → HVector f Γ → HVector f (a :: Γ)

infixl:67 "::ₕ" => HVector.cons

namespace HVector

def head : ∀{Γ}, HVector f (a :: Γ) → f a
  | _, .cons a _ => a

@[simp]
theorem head_cons {a Γ} (h : f a) (t : HVector f Γ) : head (h ::ₕ t) = h := rfl

def tail : ∀{Γ}, HVector f Γ → HVector f Γ.tail
  | _, .nil => .nil
  | _, .cons _ Γ => Γ

@[simp]
theorem tail_cons {a Γ} (h : f a) (t : HVector f Γ) : tail (h ::ₕ t) = t := rfl

@[simp]
theorem cons_head_tail {a Γ} (v : HVector f (a::Γ)) : v.head ::ₕ v.tail = v := by cases v; rfl

def get {Γ} (v : HVector f Γ) (i : Fin Γ.length) : f (Γ.get i) := match Γ, v with
  | _, .nil => i.elim0
  | _, .cons a v => i.cases a v.get

def ofFn {Γ} (F : ∀i, f (Γ.get i)) : HVector f Γ := match Γ with
  | [] => .nil
  | _ :: Γ => by dsimp at F; exact (F 0) ::ₕ ofFn (λi => F i.succ)

-- TODO: get_ofFn form an isomorphism

-- TODO: order lore

end HVector

inductive HVector' {α : Type u} (f : α → Type v) : ∀{n}, Vector' α n → Type _
  | nil : HVector' f Vector'.nil
  | cons {a v} : f a → HVector' f v → HVector' f (v.cons a)

namespace HVector'

def head : ∀{n} {v : Vector' α n}, HVector' f (v.cons a) → f a
  | _, _, .cons a _ => a

@[simp]
theorem head_cons {a} {v : Vector' α (n + 1)} (h : f a) (t : HVector' f v)
  : (head (t.cons h) : f a) = h := rfl

def tail {n} {v : Vector' α n} : HVector' f (v.cons a) → HVector' f v
  | .cons _ v => v

@[simp]
theorem tail_cons {a} {v : Vector' α (n + 1)} (h : f a) (t : HVector' f v)
  : tail (t.cons h) = t := rfl

@[simp]
theorem cons_head_tail {n} {v : Vector' α n} (t : HVector' f (v.cons a))
  : t.tail.cons t.head = t := by cases t; rfl

def get {n} {v : Vector' α n} (t : HVector' f v) (i : Fin n) : f (v.get i) := match n, v, t with
  | _, _, .nil => i.elim0
  | _, _, .cons a v => i.cases a v.get

def ofFn {n} {v : Vector' α n} (F : ∀i, f (v.get i)) : HVector' f v := match v with
  | .nil => .nil
  | .cons _ v => .cons (F 0) (ofFn (λi => F i.succ))

-- TODO: get_ofFn form an isomorphism

-- TODO: order lore

end HVector'
