import Discretion.Ctx.Ren.Nat
import Discretion.Ctx.Wk.Basic

namespace Nat

inductive Wk : Nat → Nat → Type
  | nil : Wk 0 0
  | step {n m} : Wk n m -> Wk (n + 1) m
  | lift {n m} : Wk n m -> Wk (n + 1) (m + 1)

namespace Wk

def one : (n : ℕ) → Wk n n | 0 => .nil | n + 1 => .lift (one n)

def zero : (n : ℕ) → Wk n 0 | 0 => .nil | n + 1 => .step (zero n)

def pave {n m} : Wk n m → Wk (n + 1) (m + 1)
  | .nil => .lift .nil
  | .step ρ => .step ρ.pave
  | .lift ρ => .lift ρ.pave

theorem pave_nil : pave .nil = .lift .nil := rfl

theorem pave_step {n m} (ρ : Wk n m) : pave (.step ρ) = .step ρ.pave := rfl

theorem pave_lift {n m} (ρ : Wk n m) : pave (.lift ρ) = .lift ρ.pave := rfl

def comp {n m k : ℕ} : Wk n m → Wk m k → Wk n k
  | .nil, .nil => .nil
  | .step ρ, σ => .step (ρ.comp σ)
  | .lift ρ, .step σ => .step (ρ.comp σ)
  | .lift ρ, .lift σ => .lift (ρ.comp σ)

theorem one_comp {n m : ℕ} (ρ : Wk n m) : (one n).comp ρ = ρ
  := by induction ρ <;> simp [one, comp, *]

theorem comp_one {n m : ℕ} (ρ : Wk n m) : ρ.comp (one m) = ρ
  := by induction ρ <;> simp [one, comp, *]

theorem comp_assoc {n m k l : ℕ} (ρ : Wk n m) (σ : Wk m k) (τ : Wk k l)
  : (ρ.comp σ).comp τ = ρ.comp (σ.comp τ)
  := by induction ρ generalizing k l <;> cases σ <;> cases τ <;> simp [comp, *]

theorem lift_comp {n m k : ℕ} (ρ : Wk n m) (σ : Wk m k)
  : (ρ.comp σ).lift = ρ.lift.comp σ.lift
  := by cases ρ <;> cases σ <;> rfl

theorem pave_comp {n m k : ℕ} (ρ : Wk n m) (σ : Wk m k)
  : (ρ.comp σ).pave = ρ.pave.comp σ.pave
  := by induction ρ generalizing k <;> cases σ <;> simp [comp, pave, *]

def ren {n m : ℕ} : Wk n m → Ren
  | .nil => 1
  | .lift ρ => ρ.ren.lift
  | .step ρ => ρ.ren.step

theorem ren_injective {n m : ℕ} : Function.Injective (ren (n := n) (m := m)) := λρ σ h => by
  induction ρ <;> cases σ <;> simp [ren] at * <;> apply_assumption <;> assumption

theorem ren_inj {n m : ℕ} {ρ σ : Wk n m} : ρ.ren = σ.ren ↔ ρ = σ
  := ren_injective.eq_iff

theorem swk {n m : ℕ} : ∀(ρ : Wk n m), ρ.ren.SWk n m
  | .nil => .one 0
  | .step ρ => .step ρ.swk
  | .lift ρ => .lift ρ.swk

def ofWk {n m : ℕ} {ρ : Ren} (h : ρ.Wk n m) : Wk n m := match m, n with
  | 0, n => .zero n
  | m + 1, 0 => by cases h.eq_zero
  | m + 1, n + 1 =>
    if h0 : ρ.ix 0 = 0 then
      (ofWk h.unlift).lift
    else
      (ofWk (h.unstep_of_ne h0)).step

--TODO: EqOn ofWk

--TODO: therefore, if SWk, eq ofWk, establishing bijection

end Wk

instance instWk : WkCat ℕ where
  Wk := Wk
  one := Wk.one
  comp := Wk.comp
  one_comp := Wk.one_comp
  comp_one := Wk.comp_one
  comp_assoc := Wk.comp_assoc

--TODO: WkLift 1

--TODO: WkDrop, WkEmpty, WkAddMonoid
