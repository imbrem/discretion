import Discretion.SEC.Signature

namespace SEC

open FreeSignature

inductive Term (τ : Type _) [FreeSignature τ] : Type _
  | var : ℕ → Term τ
  | op : Untyped.Inst τ → Term τ → Term τ
  | let₁ : Term τ → Term τ → Term τ
  | unit : Term τ
  | pair : Term τ → Term τ → Term τ
  | let₂ : Term τ → Term τ → Term τ

variable {τ} [FreeSignature τ]

namespace Term

@[simp]
def wk (ρ : ℕ → ℕ) : Term τ → Term τ
  | .var v => .var (ρ v)
  | .op f t => .op f (t.wk ρ)
  | .let₁ t u => .let₁ (t.wk ρ) (u.wk (Nat.liftWk ρ))
  | .unit => .unit
  | .pair t u => .pair (t.wk ρ) (u.wk ρ)
  | .let₂ t u => .let₂ (t.wk ρ) (u.wk (Nat.liftWk (Nat.liftWk ρ)))

theorem wk_id (t : Term τ) : t.wk id = t := by induction t <;> simp [*]

theorem wk_comp (ρ σ : ℕ → ℕ) (t : Term τ)
  : t.wk (ρ ∘ σ) = (t.wk σ).wk ρ
  := by induction t generalizing ρ σ <;> simp [Nat.liftWk_comp, *]

notation "wk0" => wk Nat.succ

notation "wk1" => wk (Nat.liftWk Nat.succ)

notation "wk2" => wk (Nat.liftWk (Nat.liftWk Nat.succ))

notation "wk3" => wk (Nat.liftWk (Nat.liftWk (Nat.liftWk Nat.succ)))

notation "wk4" => wk (Nat.liftWk (Nat.liftWk (Nat.liftWk (Nat.liftWk Nat.succ))))

def fvi : Term τ → ℕ
  | .var v => v + 1
  | .op _ t => t.fvi
  | .let₁ t u => t.fvi ⊔ (u.fvi - 1)
  | .unit => 0
  | .pair t u => t.fvi ⊔ u.fvi
  | .let₂ t u => t.fvi ⊔ (u.fvi - 2)

def fvu (i : ℕ) : Term τ → Bool
  | .var v => v = i
  | .op _ t => t.fvu i
  | .let₁ t u => t.fvu i ⊔ if i >= 1 then u.fvu (i - 1) else false
  | .unit => false
  | .pair t u => t.fvu i ⊔ u.fvu i
  | .let₂ t u => t.fvu i ⊔ if i >= 2 then u.fvu (i - 2) else false

open Term

abbrev Subst (τ : Type _) [FreeSignature τ] := ℕ → Term τ

namespace Subst

def lift (σ : Subst τ) : Subst τ
  | 0 => .var 0
  | i + 1 => wk0 (σ i)

@[simp]
theorem lift_zero {σ : Subst τ} : σ.lift 0 = .var 0 := rfl

@[simp]
theorem lift_succ {σ : Subst τ} (i : ℕ) : σ.lift (i + 1) = wk0 (σ i) := rfl

abbrev id : Subst τ := .var

@[simp]
theorem lift_id : id.lift = id (τ := τ) := funext (λn => by cases n <;> simp [lift, Term.wk])

def fromWk (ρ : ℕ → ℕ) : Subst τ := .var ∘ ρ

end Subst

@[simp]
def subst (σ : Subst τ) : Term τ → Term τ
  | .var v => σ v
  | .op f t => .op f (t.subst σ)
  | .let₁ t u => .let₁ (t.subst σ) (u.subst (σ.lift))
  | .unit => .unit
  | .pair t u => .pair (t.subst σ) (u.subst σ)
  | .let₂ t u => .let₂ (t.subst σ) (u.subst (σ.lift).lift)

@[simp]
theorem subst_id (t : Term τ) : t.subst Subst.id = t := by induction t <;> simp [*]

-- theorem subst_liftn_wkn (σ : Subst τ) (t : Term τ) (n : ℕ)
--   : (t.wk (Nat.liftWk^[n] .succ)).subst (Subst.lift^[n] σ) = (t.subst σ).wk (Nat.liftWk^[n] .succ)
--   := by
--   induction t generalizing n <;> simp only [subst, wk, let₁.injEq, let₂.injEq, true_and, *]
--   case var => induction n with
--     | zero => simp
--     | succ n => sorry
--   case let₁ => sorry
--   case let₂ => sorry

-- theorem subst_lift_wk0 (σ : Subst τ) (t : Term τ)
--   : (wk0 t).subst σ.lift = wk0 (t.subst σ) := by sorry

namespace Subst

def comp (σ σ' : Subst τ) : Subst τ := λi => (σ i).subst σ'

@[simp]
theorem comp_id (σ : Subst τ) : comp σ Subst.id = σ := funext (λi => by simp [comp])

@[simp]
theorem id_comp (σ : Subst τ) : comp Subst.id σ = σ := funext (λi => by simp [comp])

-- theorem lift_comp (σ σ' : Subst τ)
--   : (σ.comp σ').lift = σ.lift.comp σ'.lift := funext (λi => by cases i <;> simp [comp] <;> sorry
-- )

end Subst

-- @[simp]
-- theorem subst_comp (σ σ' : Subst τ) (t : Term τ) : t.subst (σ.comp σ') = (t.subst σ).subst σ' := by
--   induction t <;> simp [Subst.comp, *]

abbrev LSubst (τ : Type _) [FreeSignature τ] := List (Term τ)

def LSubst.lift (σ : LSubst τ) : LSubst τ := (σ.map wk0).cons (var 0)

@[simp]
theorem LSubst.lift_zero (σ : LSubst τ) : σ.lift[0]'(by simp [lift]) = .var 0 := rfl

@[simp]
theorem LSubst.lift_succ (σ : LSubst τ) {i : ℕ} (h : i < σ.length)
  : σ.lift[i + 1]'(by simp [lift, h]) = wk0 (σ[i]) := by simp [lift]

@[simp]
theorem LSubst.length_lift (σ : LSubst τ) : (σ.lift).length = σ.length + 1 := by simp [LSubst.lift]

def LSubst.id (n : ℕ) : LSubst τ := List.ofFn (λi : Fin n => var i)

theorem LSubst.id_zero : id (τ := τ) 0 = [] := rfl

@[simp]
theorem LSubst.getElem_id {n i} (h) : (id n)[i]'h = var (τ := τ) i := by simp [id]

@[simp]
theorem LSubst.length_id (n : ℕ) : (id (τ := τ) n).length = n := by simp [LSubst.id]

@[simp]
theorem LSubst.lift_id (n : ℕ) : lift (id (τ := τ) n) = id (n + 1) := by
  apply List.ext_getElem
  simp
  intro i hi hi'
  cases i with
  | zero => simp
  | succ i =>
    simp at hi
    rw [lift_succ, getElem_id, getElem_id]; simp
    simp [hi]

def LSubst.var (σ : LSubst τ) : Subst τ := λi => if _ : i < σ.length then σ[i] else .var i

theorem LSubst.var_id (n : ℕ) : (id n).var = Subst.id (τ := τ)
  := funext (λi => by simp [LSubst.var])

theorem LSubst.var_lift (σ : LSubst τ) : σ.lift.var = σ.var.lift
  := funext (λi => by
    cases i with
    | zero => simp [LSubst.var]
    | succ =>
      simp only [var, lift, List.length_cons, List.length_map, Nat.add_lt_add_iff_right,
        List.getElem_cons_succ, List.getElem_map, Subst.lift_succ]
      split <;> rfl
    )

-- TODO: var is an injection

def lsubst (σ : LSubst τ) : Term τ → Term τ
  | .var v => σ.var v
  | .op f t => .op f (t.lsubst σ)
  | .let₁ t u => .let₁ (t.lsubst σ) (u.lsubst σ.lift)
  | .unit => .unit
  | .pair t u => .pair (t.lsubst σ) (u.lsubst σ)
  | .let₂ t u => .let₂ (t.lsubst σ) (u.lsubst σ.lift.lift)

theorem subst_var (σ : LSubst τ) (t : Term τ) : t.subst σ.var = t.lsubst σ
  := by induction t generalizing σ <;> simp [<-LSubst.var_lift, lsubst, *]

-- TODO: lsubst composition

-- TODO: var preserves composition, i.e. is a faithful functor

end Term

end SEC
