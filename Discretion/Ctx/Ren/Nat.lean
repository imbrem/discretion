import Mathlib.Data.Nat.Basic
import Mathlib.Algebra.Group.Basic
import Mathlib.Tactic.Convert
import Mathlib.Order.Lattice

namespace Nat

def Ren : Type := ℕ → ℕ

namespace Ren

def ofFn (ρ : ℕ → ℕ) : Ren := ρ

def ix (ρ : Ren) (x : ℕ) := ρ x

@[simp] theorem ix_ofFn_apply (ρ : ℕ → ℕ) (x : ℕ) : ix (ofFn ρ) x = ρ x := rfl

@[simp] theorem ofFn_ix (ρ : Ren) : ofFn ρ.ix = ρ := rfl

theorem ix_comp_ofFn : ix ∘ ofFn = id := rfl

theorem ofFn_comp_ix : ofFn ∘ ix = id := rfl

instance instCoeFun : CoeFun Ren (fun _ => ℕ → ℕ) where coe ρ := ρ.ix

@[ext] theorem ext (ρ σ : Ren) (h : ∀x, ρ.ix x = σ.ix x) : ρ = σ := funext h

instance mul : Mul Ren where mul ρ σ := ofFn (ρ.ix ∘ σ.ix)

@[simp] theorem ix_mul (ρ σ : Ren) (x : ℕ) : (ρ * σ).ix x = ρ.ix (σ.ix x) := rfl

@[simp] theorem mul_apply (ρ σ : Ren) (x : ℕ) : (ρ * σ) x = ρ (σ x) := rfl

instance instOne : One Ren where one := ofFn id

@[simp] theorem ix_one (x : ℕ) : (1 : Ren).ix x = x := rfl

@[simp] theorem one_apply (x : ℕ) : (1 : Ren) x = x := rfl

instance instZero : Zero Ren where zero := ofFn (λ_ => 0)

@[simp] theorem ix_zero (x : ℕ) : (0 : Ren).ix x = 0 := rfl

@[simp] theorem zero_apply (x : ℕ) : (0 : Ren) x = 0 := rfl

instance instMonoid : Monoid Ren where
  mul_assoc _ _ _ := rfl
  one_mul _ := rfl
  mul_one _ := rfl

instance instVAdd : VAdd ℕ Ren where
  vadd x ρ := ofFn (λy => ρ.ix y + x)

theorem vadd_def (x : ℕ) (ρ : Ren) : x +ᵥ ρ = ofFn (λy => ρ.ix y + x) := rfl

@[simp] theorem ix_vadd (x : ℕ) (ρ : Ren) (y : ℕ) : (x +ᵥ ρ).ix y = ρ.ix y + x := rfl

@[simp] theorem vadd_apply (x : ℕ) (ρ : Ren) (y : ℕ) : (x +ᵥ ρ) y = ρ y + x := rfl

instance instSMul : SMul ℕ Ren where
  smul x ρ := ofFn (λy => x * ρ.ix y)

theorem vadd_injective (x : ℕ) : Function.Injective (VAdd.vadd x : Ren → Ren)
  := λρ σ h => by ext x; convert congrFun h x using 0; apply Nat.add_right_cancel_iff.symm

def step (ρ : Ren) := 1 +ᵥ ρ

@[simp] theorem ix_step (ρ : Ren) (x : ℕ) : ρ.step.ix x = ρ.ix x + 1 := rfl

@[simp] theorem step_apply (ρ : Ren) (x : ℕ) : ρ.step x = ρ x + 1 := rfl

def slant (ρ : Ren) := ofFn (λ| 0 => 0 | x + 1 => ρ.ix x)

@[simp] theorem ix_slant_zero (ρ : Ren) : ρ.slant.ix 0 = 0 := rfl

@[simp] theorem ix_slant_succ (ρ : Ren) (x : ℕ) : ρ.slant.ix (x + 1) = ρ.ix x := rfl

def lift (ρ : Ren) := ρ.step.slant

@[simp] theorem ix_lift_zero (ρ : Ren) : ρ.lift.ix 0 = 0 := rfl

@[simp] theorem ix_lift_succ (ρ : Ren) (x : ℕ) : ρ.lift.ix (x + 1) = ρ.ix x + 1 := rfl

@[simp] theorem lift_zero_apply (ρ : Ren) : ρ.lift 0 = 0 := rfl

@[simp] theorem lift_succ_apply (ρ : Ren) (x : ℕ) : ρ.lift (x + 1) = ρ x + 1 := rfl

theorem step_injective : Function.Injective step := vadd_injective 1

@[simp]
theorem step_inj (ρ σ : Ren) : step ρ = step σ ↔ ρ = σ
  := step_injective.eq_iff

theorem slant_injective : Function.Injective slant
  := λρ σ h => ext ρ σ λx => congrFun h (x + 1)

@[simp] theorem slant_inj (ρ σ : Ren) : slant ρ = slant σ ↔ ρ = σ
  := slant_injective.eq_iff

theorem lift_injective : Function.Injective lift
  := slant_injective.comp step_injective

@[simp] theorem lift_inj (ρ σ : Ren) : lift ρ = lift σ ↔ ρ = σ
  := lift_injective.eq_iff

@[simp] theorem slant_ne_step (ρ σ : Ren) : ρ.slant ≠ σ.step := λh => by cases congrFun h 0

@[simp] theorem step_ne_slant (ρ σ : Ren) : ρ.step ≠ σ.slant := (slant_ne_step σ ρ).symm

@[simp] theorem lift_ne_step (ρ σ : Ren) : ρ.lift ≠ σ.step := slant_ne_step ρ.step σ

@[simp] theorem step_ne_lift (ρ σ : Ren) : ρ.step ≠ σ.lift := step_ne_slant ρ σ.step

theorem step_mul (ρ σ : Ren) : (ρ * σ).step = ρ.step * σ := by ext x; rfl

@[simp] theorem lift_mul (ρ σ : Ren) : (ρ * σ).lift = ρ.lift * σ.lift := by ext x; cases x <;> rfl

@[simp] theorem lift_one : (1 : Ren).lift = 1 := by ext x; cases x <;> rfl

def stepn (n : ℕ) (ρ : Ren) : Ren := n +ᵥ ρ

theorem vadd_zero (ρ : Ren) : 0 +ᵥ ρ = ρ := rfl

theorem stepn_zero_apply (ρ : Ren) : stepn 0 ρ = ρ := vadd_zero ρ

theorem stepn_zero : stepn 0 = id := funext stepn_zero_apply

theorem vadd_succ (n : ℕ) (ρ : Ren) : (n + 1) +ᵥ ρ = (n +ᵥ ρ).step := rfl

theorem stepn_succ_apply' (n : ℕ) (ρ : Ren) : stepn (n + 1) ρ = (stepn n ρ).step := rfl

theorem stepn_succ' (n : ℕ) : stepn (n + 1) = step ∘ stepn n := funext (stepn_succ_apply' n)

theorem stepn_def' (n : ℕ) : stepn n = step^[n] := by
  induction n
  <;> simp only [Function.iterate_succ', stepn_succ', Function.iterate_zero, stepn_zero, *]

theorem stepn_succ_apply (n : ℕ) (ρ : Ren) : stepn (n + 1) ρ = ρ.step.stepn n
  := by rw [stepn_def', Function.iterate_succ_apply, <-stepn_def']

theorem stepn_succ (n : ℕ) : stepn (n + 1) =  stepn n ∘ step  := funext (stepn_succ_apply n)

theorem stepn_one (ρ : Ren) : stepn 1 ρ = ρ.step := by rw [stepn_succ, stepn_zero]; rfl

def slantn (n : ℕ) (ρ : Ren) : Ren := ofFn (λx => if x < n then x else ρ.ix (x - n))

def liftn (n : ℕ) (ρ : Ren) : Ren := (ρ.stepn n).slantn n

theorem liftn_zero_apply (ρ : Ren) : liftn 0 ρ = ρ := rfl

theorem liftn_zero : liftn 0 = id := funext liftn_zero_apply

theorem liftn_succ_apply' (n : ℕ) (ρ : Ren) : liftn (n + 1) ρ = (liftn n ρ).lift
  := by
  ext x
  cases x <;> simp [liftn, slantn, stepn, lift, slant, step, ix, ofFn, vadd_def]
  split <;> omega

theorem liftn_succ' (n : ℕ) : liftn (n + 1) = lift ∘ liftn n := funext (liftn_succ_apply' n)

theorem liftn_def' (n : ℕ) : liftn n = lift^[n] := by
  induction n
  <;> simp only [Function.iterate_succ', liftn_succ', Function.iterate_zero, liftn_zero, *]

theorem liftn_succ_apply (n : ℕ) (ρ : Ren) : liftn (n + 1) ρ = ρ.lift.liftn n
  := by rw [liftn_def', Function.iterate_succ_apply, <-liftn_def']

theorem liftn_succ (n : ℕ) : liftn (n + 1) =  liftn n ∘ lift  := funext (liftn_succ_apply n)

theorem liftn_one (ρ : Ren) : liftn 1 ρ = ρ.lift := by rw [liftn_succ, liftn_zero]; rfl

@[simp]
theorem liftn_of_one (n : ℕ) : liftn n (1 : Ren) = 1 := by
  induction n <;> simp [liftn_zero, liftn_succ, *]

@[simp]
theorem liftn_of_mul (n : ℕ) (ρ σ : Ren) : (ρ * σ).liftn n = ρ.liftn n * σ.liftn n := by
  induction n generalizing ρ σ <;> simp [liftn_zero, liftn_succ, *]

structure Bounded (n m : ℕ) (ρ : Ren) : Prop where
  bounded : ∀x < m, ρ.ix x < n

theorem bounded_iff {ρ : Ren} {n m : ℕ} : Bounded n m ρ ↔ ∀x < m, ρ.ix x < n
  := ⟨Bounded.bounded, Bounded.mk⟩

theorem Bounded.mono {n n' m m' : ℕ}
  (hn : n ≤ n') (hm : m' ≤ m) {ρ : Ren} (hρ : Bounded n m ρ) : Bounded n' m' ρ
  where bounded _ hx := lt_of_lt_of_le (hρ.bounded _ (lt_of_lt_of_le hx hm)) hn

theorem Bounded.one (n : ℕ) : Bounded n n (1 : Ren) where bounded _ hx := hx

theorem Bounded.mul {ρ σ : Ren} {n m k : ℕ}
  (hρ : Bounded n m ρ) (hσ : Bounded m k σ) : Bounded n k (ρ * σ) where
  bounded x hx := hρ.bounded (σ.ix x) (hσ.bounded x hx)

theorem Bounded.step {ρ : Ren} {n m : ℕ} (hρ : Bounded n m ρ) : Bounded (n + 1) m ρ.step
  where bounded x hx := by rw [ix_step, Nat.add_lt_add_iff_right]; apply hρ.bounded _ hx

theorem Bounded.slant {ρ : Ren} {n m : ℕ} (hρ : Bounded n m ρ) : Bounded (n ⊔ 1) (m + 1) ρ.slant
  where bounded x hx := by cases x <;> simp; apply Or.inl <| hρ.bounded _ (lt_of_succ_lt_succ hx)

theorem Bounded.lift {ρ : Ren} {n m : ℕ} (hρ : Bounded n m ρ) : Bounded (n + 1) (m + 1) ρ.lift
  where bounded x hx := by cases x <;> simp; apply hρ.bounded _ (lt_of_succ_lt_succ hx)

theorem Bounded.eq_zero {ρ : Ren} {m : ℕ} (hρ : Bounded 0 m ρ) : m = 0 := by
  cases m; rfl; have h := hρ.bounded 0 (by simp); cases h

def Bounded.toFin (ρ : Ren) {n m : ℕ} (hρ : Bounded n m ρ) : Fin m → Fin n
  := λx => ⟨ρ x, hρ.bounded x x.isLt⟩

@[simp] theorem toFin_one (n : ℕ) : Bounded.toFin (1 : Ren) (Bounded.one n) = id := rfl

@[simp]
theorem toFin_mul {ρ σ : Ren} {n m k : ℕ} (hρ : Bounded n m ρ) (hσ : Bounded m k σ)
  : Bounded.toFin (ρ * σ) (Bounded.mul hρ hσ) = Bounded.toFin ρ hρ ∘ Bounded.toFin σ hσ := rfl

structure MonoOn (n : ℕ) (ρ : Ren) : Prop where
  mono_on : ∀x < n, ∀y < n, x ≤ y → ρ.ix x ≤ ρ.ix y

theorem MonoOn.one (n : ℕ) : MonoOn n (1 : Ren) where
  mono_on _ _ _ _ hxy := hxy

theorem MonoOn.step {ρ : Ren} {n : ℕ} (hρ : MonoOn n ρ) : MonoOn n ρ.step
  where mono_on x hx y hy hxy := succ_le_succ (hρ.mono_on x hx y hy hxy)

theorem MonoOn.lift {ρ : Ren} {n : ℕ} (hρ : MonoOn n ρ) : MonoOn (n + 1) ρ.lift
  where
  mono_on x hx y hy hxy := by
    cases x with
    | zero => simp
    | succ x => cases y; cases hxy; simp; apply hρ.mono_on <;> omega

structure InjOn (n : ℕ) (ρ : Ren) : Prop where
  inj_on : ∀x < n, ∀y < n, ρ.ix x = ρ.ix y → x = y

theorem InjOn.one (n : ℕ) : InjOn n (1 : Ren) where
  inj_on _ _ _ _ hxy := hxy

theorem InjOn.step {ρ : Ren} {n : ℕ} (hρ : InjOn n ρ) : InjOn n ρ.step
  where inj_on x hx y hy hxy := by simp at hxy; apply hρ.inj_on <;> assumption

theorem InjOn.lift {ρ : Ren} {n : ℕ} (hρ : InjOn n ρ) : InjOn (n + 1) ρ.lift
  where
  inj_on x hx y hy hxy := by
    cases x with
    | zero => cases y; rfl; cases hxy
    | succ x => cases y; cases hxy; simp at hxy; simp; apply hρ.inj_on <;> omega

structure StrictMonoOn (n : ℕ) (ρ : Ren) : Prop extends MonoOn n ρ, InjOn n ρ where
  strict_mono_on : ∀x < n, ∀y < n, x < y → ρ.ix x < ρ.ix y
  mono_on x hx y hy hxy := (le_iff_lt_or_eq.mp hxy).elim
    (λhxy => le_of_lt (strict_mono_on x hx y hy hxy)) (λhxy => le_of_eq (congrArg ρ.ix hxy))
  inj_on x hx y hy hxy := Classical.byContradiction (λh => (Nat.lt_or_lt_of_ne h).elim
    (λhxy' => not_le_of_lt (strict_mono_on x hx y hy hxy') (le_of_eq hxy.symm))
    (λhxy' => not_le_of_lt (strict_mono_on y hy x hx hxy') (le_of_eq hxy)))

theorem StrictMonoOn.one (n : ℕ) : StrictMonoOn n (1 : Ren)  where
  strict_mono_on _ _ _ _ hxy := hxy

theorem StrictMonoOn.step {ρ : Ren} {n : ℕ} (hρ : StrictMonoOn n ρ) : StrictMonoOn n ρ.step
  where strict_mono_on x hx y hy hxy := succ_lt_succ (hρ.strict_mono_on x hx y hy hxy)

theorem StrictMonoOn.lift {ρ : Ren} {n : ℕ} (hρ : StrictMonoOn n ρ) : StrictMonoOn (n + 1) ρ.lift
  where
  strict_mono_on x hx y hy hxy := by
    cases x with
    | zero => cases y; cases hxy; simp
    | succ x => cases y; cases hxy; simp; apply hρ.strict_mono_on <;> omega

structure Clipped (n m : ℕ) (ρ : Ren) : Prop where
  clipped : ∀x ≥ m, ρ.ix x = (x - m) + n

theorem clipped_iff (n m : ℕ) (ρ : Ren) : Clipped n m ρ ↔ ∀x ≥ m, ρ.ix x = (x - m) + n
  := ⟨Clipped.clipped, Clipped.mk⟩

theorem clipped_iff_out_le_in (n m : ℕ) (hnm : m ≤ n) (ρ : Ren)
  : Clipped n m ρ ↔ ∀x ≥ m, ρ.ix x = x + (n - m)
  := Iff.trans (ρ.clipped_iff n m) (by rw [forall₂_congr]; intro x hx; omega)

theorem Clipped.out_le_in
  {ρ : Ren} {n m : ℕ} (hρ : Clipped n m ρ) (hnm : m ≤ n) : ∀x ≥ m, ρ.ix x = x + (n - m)
  := (clipped_iff_out_le_in n m hnm ρ).mp hρ

theorem Clipped.add_right {ρ : Ren} {n m k : ℕ} (hρ : Clipped n m ρ) : Clipped (n + k) (m + k) ρ
  where clipped x hx := by rw [hρ.clipped _ _] <;> omega

theorem Clipped.add_left {ρ : Ren} {n m k : ℕ} (hρ : Clipped n m ρ) : Clipped (k + n) (k + m) ρ
  where clipped x hx := by rw [hρ.clipped _ _] <;> omega

theorem Clipped.one (n : ℕ) : Clipped n n (1 : Ren) where clipped _ _ := by rw [ix_one]; omega

theorem Clipped.mul {ρ σ : Ren} {n m k : ℕ}
  (hρ : Clipped n m ρ) (hσ : Clipped m k σ) : Clipped n k (ρ * σ) where
  clipped x hx := by
    rw [ix_mul, hρ.clipped (σ.ix x), hσ.clipped x hx]; omega
    rw [hσ.clipped x hx]; omega

theorem Clipped.step {ρ : Ren} {n m : ℕ} (hρ : Clipped n m ρ) : Clipped (n + 1) m ρ.step
  where clipped x hx := by rw [ix_step, hρ.clipped _ _] <;> omega

theorem Clipped.lift {ρ : Ren} {n m : ℕ} (hρ : Clipped n m ρ) : Clipped (n + 1) (m + 1) ρ.lift
  where clipped x hx := by cases x; cases hx; rw [ix_lift_succ, hρ.clipped _ _] <;> omega

structure PermWk (n m : ℕ) (ρ : Ren) : Prop extends Bounded n m ρ, InjOn m ρ

theorem PermWk.one (n : ℕ) : PermWk n n (1 : Ren) where
  toBounded := Bounded.one n
  toInjOn := InjOn.one n

theorem PermWk.mul {ρ σ : Ren} {n m k : ℕ}
  (hρ : PermWk n m ρ) (hσ : PermWk m k σ) : PermWk n k (ρ * σ) where
  toBounded := Bounded.mul hρ.toBounded hσ.toBounded
  inj_on x hx y hy hxy := hσ.inj_on x hx y hy <|
    hρ.inj_on (σ.ix x) (hσ.bounded x hx) (σ.ix y) (hσ.bounded y hy) hxy

theorem PermWk.step {ρ : Ren} {n m : ℕ} (hρ : PermWk n m ρ) : PermWk (n + 1) m ρ.step where
  toBounded := Bounded.step hρ.toBounded
  toInjOn := InjOn.step hρ.toInjOn

theorem PermWk.lift {ρ : Ren} {n m : ℕ} (hρ : PermWk n m ρ) : PermWk (n + 1) (m + 1) ρ.lift where
  toBounded := Bounded.lift hρ.toBounded
  toInjOn := InjOn.lift hρ.toInjOn

structure Wk (n m : ℕ) (ρ : Ren) : Prop extends PermWk n m ρ, StrictMonoOn m ρ

theorem Wk.one (n : ℕ) : Wk n n (1 : Ren) where
  toPermWk := PermWk.one n
  strict_mono_on := (StrictMonoOn.one n).strict_mono_on

theorem Wk.mul {ρ σ : Ren} {n m k : ℕ}
  (hρ : Wk n m ρ) (hσ : Wk m k σ) : Wk n k (ρ * σ) where
  toPermWk := PermWk.mul hρ.toPermWk hσ.toPermWk
  strict_mono_on x hx y hy hxy :=
    hρ.strict_mono_on (σ.ix x) (hσ.bounded x hx) (σ.ix y) (hσ.bounded y hy)
      <| hσ.strict_mono_on x hx y hy hxy

theorem Wk.step {ρ : Ren} {n m : ℕ} (hρ : Wk n m ρ) : Wk (n + 1) m ρ.step where
  toPermWk := PermWk.step hρ.toPermWk
  strict_mono_on := (StrictMonoOn.step hρ.toStrictMonoOn).strict_mono_on

theorem Wk.lift {ρ : Ren} {n m : ℕ} (hρ : Wk n m ρ) : Wk (n + 1) (m + 1) ρ.lift where
  toPermWk := PermWk.lift hρ.toPermWk
  strict_mono_on := (StrictMonoOn.lift hρ.toStrictMonoOn).strict_mono_on

structure SPermWk (n m : ℕ) (ρ : Ren)  : Prop extends PermWk n m ρ, Clipped n m ρ

theorem Bounded.add_right {n m k : ℕ} {ρ : Ren} (hρ : Bounded n m ρ) (hρ' : Clipped n m ρ)
  : Bounded (n + k) (m + k) ρ where
  bounded x hx :=
    if hx' : x < m then
      lt_of_lt_of_le (hρ.bounded x hx') (by simp)
    else
      by rw [hρ'.clipped x (ge_of_not_lt hx')]; omega

theorem SPermWk.add_right {n m k : ℕ} {ρ : Ren} (hρ : SPermWk n m ρ) : SPermWk (n + k) (m + k) ρ
  where
  toClipped := hρ.toClipped.add_right
  toBounded := hρ.toBounded.add_right hρ.toClipped
  inj_on x hx y hy hxy := by
    if hx' : x < m then
      if hy' : y < m then
        exact hρ.inj_on x hx' y hy' hxy
      else
        have _ := hρ.bounded x hx'
        rw [hρ.clipped y (ge_of_not_lt hy')] at hxy
        omega
    else
      if hy' : y < m then
        have _ := hρ.bounded y hy'
        rw [hρ.clipped x (ge_of_not_lt hx')] at hxy
        omega
      else
        rw [hρ.clipped x (ge_of_not_lt hx'), hρ.clipped y (ge_of_not_lt hy')] at hxy
        omega

theorem SPermWk.one (n : ℕ) : SPermWk n n (1 : Ren) where
  toPermWk := PermWk.one n
  toClipped := Clipped.one n

theorem SPermWk.mul {ρ σ : Ren} {n m k : ℕ}
  (hρ : SPermWk n m ρ) (hσ : SPermWk m k σ) : SPermWk n k (ρ * σ) where
  toPermWk := PermWk.mul hρ.toPermWk hσ.toPermWk
  toClipped := Clipped.mul hρ.toClipped hσ.toClipped

theorem SPermWk.step {ρ : Ren} {n m : ℕ} (hρ : SPermWk n m ρ) : SPermWk (n + 1) m ρ.step where
  toPermWk := PermWk.step hρ.toPermWk
  toClipped := Clipped.step hρ.toClipped

theorem SPermWk.lift {ρ : Ren} {n m : ℕ} (hρ : SPermWk n m ρ) : SPermWk (n + 1) (m + 1) ρ.lift where
  toPermWk := PermWk.lift hρ.toPermWk
  toClipped := Clipped.lift hρ.toClipped

structure SWk (n m : ℕ) (ρ : Ren) : Prop extends Wk n m ρ, Clipped n m ρ, SPermWk n m ρ

theorem SWk.one (n : ℕ) : SWk n n  (1 : Ren) where
  toWk := Wk.one n
  toClipped := Clipped.one n

theorem SWk.add_right {n m k : ℕ} {ρ : Ren} (hρ : SWk n m ρ) : SWk (n + k) (m + k) ρ
  where
  toBounded := hρ.toBounded.add_right hρ.toClipped
  toClipped := hρ.toClipped.add_right
  strict_mono_on x hx y hy hxy := by
    if hx' : x < m then
    if hy' : y < m then
      exact hρ.strict_mono_on x hx' y hy' hxy
    else
      have _ := hρ.bounded x hx'
      rw [hρ.clipped y (ge_of_not_lt hy')]
      omega
  else
    if hy' : y < m then
      have _ := hρ.bounded y hy'
      rw [hρ.clipped x (ge_of_not_lt hx')]
      omega
    else
      rw [hρ.clipped x (ge_of_not_lt hx'), hρ.clipped y (ge_of_not_lt hy')]
      omega

theorem SWk.mul {ρ σ : Ren} {n m k : ℕ}
  (hρ : SWk n m ρ) (hσ : SWk m k σ) : SWk n k (ρ * σ) where
  toWk := Wk.mul hρ.toWk hσ.toWk
  toClipped := Clipped.mul hρ.toClipped hσ.toClipped

theorem SWk.step {ρ : Ren} {n m : ℕ} (hρ : SWk n m ρ) : SWk (n + 1) m ρ.step where
  toWk := Wk.step hρ.toWk
  toClipped := Clipped.step hρ.toClipped

theorem SWk.lift {ρ : Ren} {n m : ℕ} (hρ : SWk n m ρ) : SWk (n + 1) (m + 1) ρ.lift where
  toWk := Wk.lift hρ.toWk
  toClipped := Clipped.lift hρ.toClipped

structure EqOn (n : ℕ) (ρ σ : Ren) : Prop where
  eq_on : ∀x < n, ρ.ix x = σ.ix x

theorem eqOn_refl (n : ℕ) (ρ : Ren) : EqOn n ρ ρ where eq_on _ _ := rfl

theorem eqOn_of_eq (n : ℕ) {ρ σ : Ren} (hρσ : ρ = σ) : EqOn n ρ σ := hρσ ▸ ρ.eqOn_refl n

theorem EqOn.symm {ρ σ : Ren} {n : ℕ} (hρσ : EqOn n ρ σ) : EqOn n σ ρ where
  eq_on x hx := (hρσ.eq_on x hx).symm

theorem EqOn.trans {ρ σ τ : Ren} {n : ℕ} (hρσ : EqOn n ρ σ) (hστ : EqOn n σ τ) : EqOn n ρ τ where
  eq_on x hx := ((hρσ.eq_on x hx).trans (hστ.eq_on x hx))

theorem EqOn.step {ρ σ : Ren} {n : ℕ} (hρσ : EqOn n ρ σ) : EqOn n ρ.step σ.step where
  eq_on x hx := by simp [hρσ.eq_on x hx]

theorem EqOn.slant {ρ σ : Ren} {n : ℕ} (hρσ : EqOn n ρ σ) : EqOn (n + 1) ρ.slant σ.slant where
  eq_on x hx := by cases x; rfl; simp [hρσ.eq_on _ (lt_of_succ_lt_succ hx)]

theorem EqOn.lift {ρ σ : Ren} {n : ℕ} (hρσ : EqOn n ρ σ) : EqOn (n + 1) ρ.lift σ.lift
  := hρσ.step.slant

theorem Clipped.eq_of_eqOn {ρ σ : Ren} {n m : ℕ}
  (hρ : Clipped n m ρ) (hσ : Clipped n m σ) (hρσ : EqOn m ρ σ) : ρ = σ  := by
  ext x; if hx : x ≥ m then rw [hρ.clipped x hx, hσ.clipped x hx] else apply hρσ.eq_on x; omega

theorem Clipped.eqOn_iff {ρ σ : Ren} {n m : ℕ}
  (hρ : Clipped n m ρ) (hσ : Clipped n m σ) : EqOn m ρ σ ↔ ρ = σ
  := ⟨hρ.eq_of_eqOn hσ, eqOn_of_eq m⟩

theorem Bounded.eqOn {ρ σ : Ren} {n m : ℕ} (h : EqOn m ρ σ) (hρ : Bounded n m ρ) : Bounded n m σ
  where
  bounded x hx := by convert hρ.bounded x hx using 1; exact (h.eq_on x hx).symm

theorem StrictMonoOn.eqOn  {ρ σ : Ren} {m : ℕ} (h : EqOn m ρ σ) (hρ : StrictMonoOn m ρ)
  : StrictMonoOn m σ
  where
  strict_mono_on x hx y hy hxy := by
    convert hρ.strict_mono_on x hx y hy hxy using 1
    <;> apply h.symm.eq_on <;> assumption

theorem Wk.eqOn {ρ σ : Ren} {n m : ℕ} (h : EqOn m ρ σ) (hρ : Wk n m ρ) : Wk n m σ
  where
  toBounded := hρ.toBounded.eqOn h
  strict_mono_on := (hρ.toStrictMonoOn.eqOn h).strict_mono_on

def shift (ρ : Ren) := ρ * (1 : Ren).step

theorem Bounded.shift {ρ : Ren} (h : Bounded n (m + 1) ρ) : Bounded n m (ρ.shift)
  := .mul h (.step (.one m))

theorem Clipped.shift {ρ : Ren} (h : Clipped n (m + 1) ρ) : Clipped n m (ρ.shift)
  := .mul h (.step (.one m))

theorem Wk.shift {ρ : Ren} (h : Wk n (m + 1) ρ) : Wk n m (ρ.shift)
  := .mul h (.step (.one m))

theorem SWk.shift {ρ : Ren} (h : SWk n (m + 1) ρ) : SWk n m (ρ.shift)
  := .mul h (.step (.one m))

def unstep (ρ : Ren) := ofFn (λx => ρ.ix x - 1)

theorem Bounded.unstep  {ρ : Ren} (h : Bounded (n + 2) m ρ)
  : Bounded (n + 1) m (ρ.unstep) where
  bounded x hx := by have hx' := h.bounded x hx; simp [Ren.unstep]; omega

theorem Bounded.unstep_step {ρ : Ren} (h : Bounded (n + 1) m ρ.step)
  : Bounded n m ρ where
  bounded x hx := by convert h.bounded x hx using 0; simp [Ren.step]

theorem Clipped.unstep {ρ : Ren} (h : Clipped (n + 1) m ρ) : Clipped n m (ρ.unstep) where
  clipped x hx := have hx' := h.clipped x hx; by simp [Ren.unstep, hx']

def unlift (ρ : Ren) := ρ.shift.unstep

theorem Wk.eqOn_lift {ρ : Ren} (h : Wk n m ρ) (hρ : ρ.ix 0 = 0)
  : EqOn m (ρ.unlift.lift) ρ := EqOn.mk (λx hx => by
  cases x; exact hρ.symm
  simp [Ren.unlift, Ren.shift, Ren.unstep]
  have hρ := h.strict_mono_on 0 (by cases hx <;> simp) _ hx (by simp)
  omega
)

theorem Wk.eqOn_step {ρ : Ren} (h : Wk n m ρ) (hρ : ρ.ix 0 ≠ 0)
  : EqOn m (ρ.unstep.step) ρ := EqOn.mk (λx hx => by
  cases x; simp [Ren.shift, Ren.unstep]; omega
  simp [Ren.unlift, Ren.shift, Ren.unstep]
  have hρ := h.strict_mono_on 0 (by cases hx <;> simp) _ hx (by simp)
  omega
)

theorem Bounded.unlift_lift {ρ : Ren}
  (h : Bounded (n + 1) (m + 1) ρ.lift) : Bounded n m ρ where
  bounded x hx := by convert h.bounded (x + 1) (by simp [hx]) using 0; simp

theorem Wk.unlift_lift {ρ : Ren} (h : Wk (n + 1) (m + 1) ρ.lift) : Wk n m ρ where
  toBounded := h.toBounded.unlift_lift
  strict_mono_on x hx y hy hxy := by
    convert h.strict_mono_on (x + 1) (by simp [hx]) (y + 1) (by simp [hy]) (by simp [hxy]) using 0
    simp

theorem Wk.unstep_step {ρ : Ren} (h : Wk (n + 1) m ρ.step) : Wk n m ρ where
  toBounded := h.toBounded.unstep_step
  strict_mono_on x hx y hy hxy := by convert h.strict_mono_on x hx y hy hxy using 0; simp

theorem Wk.unstep_of_ne {ρ : Ren} (h : Wk (n + 1) m ρ) (h0 : ρ.ix 0 ≠ 0) : Wk n m ρ.unstep
  := (h.eqOn (h.eqOn_step h0).symm).unstep_step

theorem Wk.unlift {ρ : Ren} (h : Wk (n + 1) (m + 1) ρ) : Wk n m (ρ.unlift) :=
  if hρ : ρ.ix 0 = 0 then
    (h.eqOn (h.eqOn_lift hρ).symm).unlift_lift
  else by
    have h := (h.eqOn (h.eqOn_step hρ).symm).unstep_step.shift
    apply h.eqOn
    constructor
    intro x hx
    simp [Ren.shift, Ren.unstep, Ren.unlift]

theorem Clipped.unlift {ρ : Ren} (h : Clipped (n + 1) (m + 1) ρ) : Clipped n m (ρ.unlift)
  := h.unstep.shift

theorem SWk.unlift {ρ : Ren} (h : SWk (n + 1) (m + 1) ρ) : SWk n m (ρ.unlift) where
  toWk := h.toWk.unlift
  toClipped := h.toClipped.unlift

theorem SWk.eq_lift {ρ : Ren} (h : SWk n m ρ) (hρ : ρ.ix 0 = 0)
  : ρ.unlift.lift = ρ :=  by
  apply (h.eq_of_eqOn _ (h.eqOn_lift hρ).symm).symm
  constructor; intro x hx
  have hx' := h.clipped x hx
  cases x with
  | zero => simp at *; cases hx; cases hx'; simp [*]
  | succ x => cases m with
  | zero =>
    simp [Ren.unlift, Ren.unstep, Ren.shift, hx']
    omega
  | succ m =>
    have hn := h.bounded 0 (by simp)
    simp [Ren.unlift, Ren.unstep, Ren.shift, hx']
    omega

theorem SWk.eq_step {ρ : Ren} (h : SWk n m ρ) (hρ : ρ.ix 0 ≠ 0)
  : ρ.unstep.step = ρ := by
  apply (h.eq_of_eqOn _ (h.eqOn_step hρ).symm).symm
  constructor; intro x hx
  have hx' := h.clipped x hx
  cases x with
  | zero => simp [Ren.unstep, hx']; omega
  | succ x => cases m with
  | zero =>
    simp [Ren.unlift, Ren.unstep, Ren.shift, hx']
    omega
  | succ m =>
    have hn := h.bounded 0 (by simp)
    simp [Ren.unlift, Ren.unstep, Ren.shift, hx']
    omega
