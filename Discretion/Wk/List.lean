import Discretion.Wk.Nat
import Discretion.Wk.Fin
import Discretion.Wk.NatInductive
import Mathlib.Data.Fintype.Card

-- TODO: general relation edition...
inductive List.Wk {α} : List α → List α → Type
  | nil : Wk [] []
  | step (A) {Γ Δ} : Wk Γ Δ → Wk (A :: Γ) Δ
  | lift (A) {Γ Δ} : Wk Γ Δ → Wk (A :: Γ) (A :: Δ)

def List.Wk.id {α} : ∀(Γ : List α), Wk Γ Γ
  | [] => .nil
  | A :: Γ => (Wk.id Γ).lift A

def List.Wk.drop {α} : ∀(Γ : List α), Wk Γ []
  | [] => .nil
  | A :: Γ => (Wk.drop Γ).step A

def List.Wk.comp {α} {Γ Δ Ξ : List α} : Wk Γ Δ → Wk Δ Ξ → Wk Γ Ξ
  | .nil, .nil => .nil
  | .step A ρ, σ | .lift A ρ, .step _ σ => .step A (ρ.comp σ)
  | .lift A ρ, .lift _ σ => .lift A (ρ.comp σ)

def List.Wk.nw {α} : ∀{Γ Δ : List α}, Wk Γ Δ → Nat.Wk Γ.length Δ.length
  | _, _, .nil => .nil
  | _, _, .step _ ρ => ρ.nw.step
  | _, _, .lift _ ρ => ρ.nw.lift

@[simp]
theorem List.Wk.nw_nil {α} : List.Wk.nw (α := α) .nil = .nil := rfl

@[simp]
theorem List.Wk.nw_step {α} {Γ Δ : List α} (A) (ρ : Wk Γ Δ)
  : List.Wk.nw (ρ.step A) = ρ.nw.step := rfl

@[simp]
theorem List.Wk.nw_lift {α} {Γ Δ : List α} (A) (ρ : Wk Γ Δ)
  : List.Wk.nw (ρ.lift A) = ρ.nw.lift := rfl

@[simp]
theorem List.Wk.nw_id {α} {Γ : List α} : List.Wk.nw (List.Wk.id Γ) = Nat.Wk.id Γ.length
  := by induction Γ <;> simp only [nw, id, Nat.Wk.id, *]

@[simp]
theorem List.Wk.nw_comp {α} {Γ Δ Ξ : List α} (ρ : Wk Γ Δ) (σ : Wk Δ Ξ)
  : List.Wk.nw (ρ.comp σ) = (List.Wk.nw ρ).comp (List.Wk.nw σ) := by
  induction ρ generalizing Ξ <;> cases σ <;> simp only [nw, comp, Nat.Wk.comp, *]

theorem List.Wk.nw_injective {α} {Γ Δ : List α} : Function.Injective (@List.Wk.nw α Γ Δ)
  := λ ρ σ h => by
  induction ρ <;> cases σ
  <;> simp only [length_cons, nw, Nat.Wk.lift.injEq, Nat.Wk.step.injEq, reduceCtorEq] at h
  <;> congr
  <;> apply_assumption
  <;> rw [h]

@[simp]
theorem List.Wk.comp_id {α} {Γ Δ : List α} (ρ : Wk Γ Δ) : ρ.comp (Wk.id Δ) = ρ
  := List.Wk.nw_injective (by simp)

@[simp]
theorem List.Wk.id_comp {α} {Γ Δ : List α} (ρ : Wk Γ Δ) : (Wk.id Γ).comp ρ = ρ
  := List.Wk.nw_injective (by simp)

theorem List.Wk.comp_assoc {α} {Γ Δ Ξ Ω : List α} (ρ : Wk Γ Δ) (σ : Wk Δ Ξ) (τ : Wk Ξ Ω)
  : (ρ.comp σ).comp τ = ρ.comp (σ.comp τ)
  := List.Wk.nw_injective (by simp [Nat.Wk.comp_assoc])

theorem List.Wk.nw_inj {α} {Γ Δ : List α} {ρ σ : Wk Γ Δ} : List.Wk.nw ρ = List.Wk.nw σ ↔ ρ = σ
  := nw_injective.eq_iff

def List.Wk.ix {α} : ∀{Γ Δ : List α}, Wk Γ Δ → ℕ → ℕ
  | _, _, .nil => _root_.id
  | _, _, .step A ρ => Nat.stepWk ρ.ix
  | _, _, .lift A ρ => Nat.liftWk ρ.ix

def List.Wk.ixf {α} : ∀{Γ Δ : List α}, Wk Γ Δ → Fin Δ.length → Fin Γ.length
  | _, _, .nil => Fin.elim0
  | _, _, .step A ρ => Fin.stepWk ρ.ixf
  | _, _, .lift A ρ => Fin.liftWk ρ.ixf

def List.Wk.pv {α} : ∀{Γ Δ : List α}, Wk Γ Δ → Vector' β Γ.length → Vector' β Δ.length
  | _, _, .nil, _ => Vector'.nil
  | _, _, .step A ρ, .cons _ v => ρ.pv v
  | _, _, .lift A ρ, .cons a v => (ρ.pv v).cons a

@[simp]
theorem List.Wk.pv_nil {α} {v : Vector' β 0} : (.nil : Wk (α := α) [] []).pv v = .nil := rfl

@[simp]
theorem List.Wk.pv_step_cons {α} {A} {Γ Δ : List α} (ρ : Wk Γ Δ) (a) (v : Vector' β _)
  : (ρ.step A).pv (v.cons a) = ρ.pv v := rfl

@[simp]
theorem List.Wk.pv_lift_cons {α} {A} {Γ Δ : List α} (ρ : Wk Γ Δ) (a) (v : Vector' β _)
  : (ρ.lift A).pv (v.cons a) = (ρ.pv v).cons a := rfl

theorem List.Wk.pv_nw {α} {Γ Δ : List α} (ρ : Wk Γ Δ)
  : ρ.nw.pv = ρ.pv (β := β) := by funext v; induction ρ <;> cases v <;> simp [*]

inductive List.Wk.Wf {α} : ∀{Γ Δ : List α}, Wk Γ Δ → Vector' EQuant Γ.length → Prop
  | nil : Wf .nil Vector'.nil
  | step (A) {Γ Δ} (ρ : Wk Γ Δ) (q qs)
    : 0 ≤ q → Wf ρ qs → Wf (ρ.step A) (qs.cons q)
  | lift (A) {Γ Δ} (ρ : Wk Γ Δ) (q qs)
    : 1 ≤ q → Wf ρ qs → Wf (ρ.lift A) (qs.cons q)

inductive List.Wk.EWf {α} : ∀{Γ Δ : List α}, Wk Γ Δ → Vector' EQuant Γ.length → Prop

def List.Wk.minQ {α} : ∀{Γ Δ : List α}, Wk Γ Δ → Vector' EQuant Γ.length
  | _, _, .nil => .nil
  | _, _, .step _ ρ => (ρ.minQ).cons 0
  | _, _, .lift _ ρ => (ρ.minQ).cons 1

-- TODO: Wk wf iff minQ leq qs...

-- TODO: Split wf iff sum minQ leq qs...

def List.QWk (Γ Δ : List α) (qs : Vector' EQuant Γ.length) := {ρ : Wk Γ Δ | ρ.Wf qs}

-- TODO: List.Wk is a subsingleton if Γ has no duplicates of elements of Δ
-- (and therefore, in particular, if it has no duplicates at all!)

def List.Split {α} (Γ Δ Ξ : List α) := List.Wk Γ Δ × List.Wk Γ Ξ

abbrev List.Split.lwk {α} {Γ Δ Ξ : List α} (ρ : List.Split Γ Δ Ξ) : List.Wk Γ Δ := ρ.1

abbrev List.Split.rwk {α} {Γ Δ Ξ : List α} (ρ : List.Split Γ Δ Ξ) : List.Wk Γ Ξ := ρ.2

def List.Split.nw {α} {Γ Δ Ξ : List α} (ρ : List.Split Γ Δ Ξ) : Nat.Split Γ.length Δ.length Ξ.length
  := (ρ.lwk.nw, ρ.rwk.nw)

theorem List.Split.nw_injective {α} {Γ Δ Ξ : List α} : Function.Injective (@List.Split.nw α Γ Δ Ξ)
  := λ ρ σ h => by
  rw [Prod.eq_iff_fst_eq_snd_eq] at *
  cases h; constructor <;> apply List.Wk.nw_injective <;> assumption

theorem List.Split.nw_inj {α} {Γ Δ Ξ : List α} {ρ σ : List.Split Γ Δ Ξ}
  : List.Split.nw ρ = List.Split.nw σ ↔ ρ = σ
  := nw_injective.eq_iff

@[match_pattern]
def List.Split.nil {α} : List.Split (α := α) [] [] [] := (List.Wk.id _, List.Wk.id _)

@[match_pattern]
def List.Split.both {α} (A : α) {Γ Δ Ξ : List α} (ρ : List.Split Γ Δ Ξ)
  : List.Split (A :: Γ) (A :: Δ) (A :: Ξ) := (ρ.1.lift A, ρ.2.lift A)

@[match_pattern]
def List.Split.left {α} (A : α) {Γ Δ Ξ : List α} (ρ : List.Split Γ Δ Ξ)
  : List.Split (A :: Γ) (A :: Δ) Ξ := (ρ.1.lift A, ρ.2.step A)

@[match_pattern]
def List.Split.right {α} (A : α) {Γ Δ Ξ : List α} (ρ : List.Split Γ Δ Ξ)
  : List.Split (A :: Γ) Δ (A :: Ξ) := (ρ.1.step A, ρ.2.lift A)

@[match_pattern]
def List.Split.skip {α} (A : α) {Γ Δ Ξ : List α} (ρ : List.Split Γ Δ Ξ)
  : List.Split (A :: Γ) Δ Ξ := (ρ.1.step A, ρ.2.step A)

@[elab_as_elim, induction_eliminator]
def List.Split.induction {α} {motive : ∀{Γ Δ Ξ}, List.Split Γ Δ Ξ → Sort _}
  (nil : motive (List.Split.nil (α := α)))
  (both : ∀(A) {Γ Δ Ξ} (ρ : List.Split Γ Δ Ξ), motive ρ → motive (ρ.both A))
  (left : ∀(A) {Γ Δ Ξ} (ρ : List.Split Γ Δ Ξ), motive ρ → motive (ρ.left A))
  (right : ∀(A) {Γ Δ Ξ} (ρ : List.Split Γ Δ Ξ), motive ρ → motive (ρ.right A))
  (skip : ∀(A) {Γ Δ Ξ} (ρ : List.Split Γ Δ Ξ), motive ρ → motive (ρ.skip A))
  {Γ Δ Ξ : List α} (ρ : List.Split Γ Δ Ξ) : motive ρ := match Γ, Δ, Ξ, ρ with
  | _, _, _, ⟨.nil, .nil⟩ => nil
  | _, _, _, ⟨.lift A ρ, .lift _ σ⟩ => both A (ρ, σ) (induction nil both left right skip (ρ, σ))
  | _, _, _, ⟨.lift A ρ, .step _ σ⟩ => left A (ρ, σ) (induction nil both left right skip (ρ, σ))
  | _, _, _, ⟨.step A ρ, .lift _ σ⟩ => right A (ρ, σ) (induction nil both left right skip (ρ, σ))
  | _, _, _, ⟨.step A ρ, .step _ σ⟩ => skip A (ρ, σ) (induction nil both left right skip (ρ, σ))

def List.Split.cases' {α} {motive : ∀{Γ Δ Ξ}, List.Split Γ Δ Ξ → Sort _}
  (nil : motive (List.Split.nil (α := α)))
  (both : ∀(A) {Γ Δ Ξ} (ρ : List.Split Γ Δ Ξ), motive (ρ.both A))
  (left : ∀(A) {Γ Δ Ξ} (ρ : List.Split Γ Δ Ξ), motive (ρ.left A))
  (right : ∀(A) {Γ Δ Ξ} (ρ : List.Split Γ Δ Ξ), motive (ρ.right A))
  (skip : ∀(A) {Γ Δ Ξ} (ρ : List.Split Γ Δ Ξ), motive (ρ.skip A))
  {Γ Δ Ξ : List α} (ρ : List.Split Γ Δ Ξ) : motive ρ := match Γ, Δ, Ξ, ρ with
  | _, _, _, ⟨.nil, .nil⟩ => nil
  | _, _, _, ⟨.lift A ρ, .lift _ σ⟩ => both A (ρ, σ)
  | _, _, _, ⟨.lift A ρ, .step _ σ⟩ => left A (ρ, σ)
  | _, _, _, ⟨.step A ρ, .lift _ σ⟩ => right A (ρ, σ)
  | _, _, _, ⟨.step A ρ, .step _ σ⟩ => skip A (ρ, σ)

@[simp]
theorem List.Split.nw_nil {α} : List.Split.nw (α := α) .nil = .nil := rfl

@[simp]
theorem List.Split.nw_both {α} {Γ Δ Ξ : List α} (ρ : List.Split Γ Δ Ξ) (A : α)
  : (ρ.both A).nw = ρ.nw.both := rfl

@[simp]
theorem List.Split.nw_left {α} {Γ Δ Ξ : List α} (ρ : List.Split Γ Δ Ξ) (A : α)
  : (ρ.left A).nw = ρ.nw.left := rfl

@[simp]
theorem List.Split.nw_right {α} {Γ Δ Ξ : List α} (ρ : List.Split Γ Δ Ξ) (A : α)
  : (ρ.right A).nw = ρ.nw.right := rfl

@[simp]
theorem List.Split.nw_skip {α} {Γ Δ Ξ : List α} (ρ : List.Split Γ Δ Ξ) (A : α)
  : (ρ.skip A).nw = ρ.nw.skip := rfl

inductive List.Split.Wf {α} : ∀{Γ Δ Ξ : List α}, List.Split Γ Δ Ξ → Vector' EQuant Γ.length → Prop
  | nil : List.Split.Wf .nil .nil
  | both (A) {Γ Δ Ξ} (ρ : List.Split Γ Δ Ξ) (q qs)
    : .copy ≤ q → List.Split.Wf ρ qs → List.Split.Wf (ρ.both A) (qs.cons q)
  | left (A) {Γ Δ Ξ} (ρ : List.Split Γ Δ Ξ) (q qs)
    : 1 ≤ q → List.Split.Wf ρ qs → List.Split.Wf (ρ.left A) (qs.cons q)
  | right (A) {Γ Δ Ξ} (ρ : List.Split Γ Δ Ξ) (q qs)
    : 1 ≤ q → List.Split.Wf ρ qs → List.Split.Wf (ρ.right A) (qs.cons q)
  | skip (A) {Γ Δ Ξ} (ρ : List.Split Γ Δ Ξ) (q qs)
    : 0 ≤ q → List.Split.Wf ρ qs → List.Split.Wf (ρ.skip A) (qs.cons q)

def List.QSplit (Γ Δ Ξ : List α)
  (qΓ : Vector' EQuant Γ.length) (qΔ : Vector' EQuant Δ.length) (qΞ : Vector' EQuant Ξ.length)
  := {ρ : List.Split Γ Δ Ξ | ρ.Wf qΓ ∧ ρ.lwk.pv qΓ = qΔ ∧ ρ.rwk.pv qΓ = qΞ}

def List.Split.minQ {α} {Γ Δ Ξ : List α} (ρ : Split Γ Δ Ξ) : Vector' EQuant Γ.length
  := ρ.lwk.minQ + ρ.rwk.minQ

@[simp]
theorem List.Split.minQ_nil {α} : List.Split.minQ (α := α) .nil = .nil := rfl

@[simp]
theorem List.Split.minQ_both {α} {Γ Δ Ξ : List α} (A) (ρ : List.Split Γ Δ Ξ)
  : (ρ.both A).minQ = ρ.minQ.cons .copy := rfl

@[simp]
theorem List.Split.minQ_lift_lift {α} {Γ Δ Ξ : List α} (A) (ρ : List.Wk Γ Δ) (σ : List.Wk Γ Ξ)
  : minQ ⟨ρ.lift A, σ.lift A⟩ = (minQ ⟨ρ, σ⟩).cons .copy := rfl

@[simp]
theorem List.Split.minQ_left {α} {Γ Δ Ξ : List α} (A) (ρ : List.Split Γ Δ Ξ)
  : (ρ.left A).minQ = ρ.minQ.cons 1 := rfl

@[simp]
theorem List.Split.minQ_lift_step {α} {Γ Δ Ξ : List α} (A) (ρ : List.Wk Γ Δ) (σ : List.Wk Γ Ξ)
  : minQ ⟨ρ.lift A, σ.step A⟩ = (minQ ⟨ρ, σ⟩).cons 1 := rfl

@[simp]
theorem List.Split.minQ_right {α} {Γ Δ Ξ : List α} (A) (ρ : List.Split Γ Δ Ξ)
  : (ρ.right A).minQ = ρ.minQ.cons 1 := rfl

@[simp]
theorem List.Split.minQ_step_lift {α} {Γ Δ Ξ : List α} (A) (ρ : List.Wk Γ Δ) (σ : List.Wk Γ Ξ)
  : minQ ⟨ρ.step A, σ.lift A⟩ = (minQ ⟨ρ, σ⟩).cons 1 := rfl

@[simp]
theorem List.Split.minQ_skip {α} {Γ Δ Ξ : List α} (A) (ρ : List.Split Γ Δ Ξ)
  : (ρ.skip A).minQ = ρ.minQ.cons 0 := rfl

@[simp]
theorem List.Split.minQ_step_step {α} {Γ Δ Ξ : List α} (A) (ρ : List.Wk Γ Δ) (σ : List.Wk Γ Ξ)
  : minQ ⟨ρ.step A, σ.step A⟩ = (minQ ⟨ρ, σ⟩).cons 0 := rfl

theorem List.Split.Wf.minQ_le {α}
  {Γ Δ Ξ : List α} {ρ : List.Split Γ Δ Ξ} {qs : Vector' EQuant Γ.length}
  (h : List.Split.Wf ρ qs) : ρ.minQ ≤ qs := by induction h <;> simp [*]

theorem List.Split.Wf.of_minQ_le {α}
  {Γ Δ Ξ : List α} {ρ : List.Split Γ Δ Ξ} {qs : Vector' EQuant Γ.length}
  (h : ρ.minQ ≤ qs) : List.Split.Wf ρ qs := by
  induction ρ with
  | nil => cases qs; constructor
  | both A ρ I => cases qs; apply both _ _ _ _ h.head (I h.tail)
  | left A ρ I => cases qs; apply left _ _ _ _ h.head (I h.tail)
  | right A ρ I => cases qs; apply right _ _ _ _ h.head (I h.tail)
  | skip A ρ I => cases qs; apply skip _ _ _ _ h.head (I h.tail)

theorem List.Split.Wf.minQ' {α}
  {Γ Δ Ξ : List α} (ρ : List.Split Γ Δ Ξ) : List.Split.Wf ρ ρ.minQ := of_minQ_le (le_refl _)

theorem List.Split.Wf.le_minQ_iff {α}
  {Γ Δ Ξ : List α} {ρ : List.Split Γ Δ Ξ} {qs : Vector' EQuant Γ.length}
  : List.Split.Wf ρ qs ↔ ρ.minQ ≤ qs := ⟨List.Split.Wf.minQ_le, List.Split.Wf.of_minQ_le⟩

-- TODO: HVector split...

-- TODO: quant compatibility

/-- The function `ρ` sends `Γ` to `Δ` -/
def List.IsFWk (Γ Δ : List α) (ρ : Fin Δ.length → Fin Γ.length) : Prop
  := Fin.FEWkn Γ.get Δ.get ρ

theorem List.IsFWk.get {Γ Δ : List α} {ρ : Fin Δ.length → Fin Γ.length} (h : List.IsFWk Γ Δ ρ)
  : ∀i, Γ.get (ρ i) = Δ.get i := h.apply

theorem List.IsFWk.getElem {Γ Δ : List α} {ρ : Fin Δ.length → Fin Γ.length} (h : List.IsFWk Γ Δ ρ)
  : ∀i, Γ[ρ i] = Δ[i] := h.apply

theorem List.IsFWk.comp {ρ : Fin Δ.length → Fin Γ.length} {σ : Fin Ξ.length → Fin Δ.length}
  (hρ : List.IsFWk Γ Δ ρ) (hσ : List.IsFWk Δ Ξ σ) : List.IsFWk Γ Ξ (ρ ∘ σ)
  := Fin.FEWkn.comp hρ hσ

theorem List.IsFWk.lift {ρ : Fin Δ.length → Fin Γ.length} (hρ : List.IsFWk Γ Δ ρ)
    : List.IsFWk (A :: Γ) (A :: Δ) (Fin.liftWk ρ)
  := by funext i; cases i using Fin.cases with
  | zero => rfl
  | succ i =>
    simp only [length_cons, Function.comp_apply, Fin.liftWk, Fin.cases_succ, Fin.val_succ,
      get_eq_getElem, getElem_cons_succ]
    apply hρ.getElem

/-- The function `ρ` sends `Γ` to `Δ` -/
def List.IsWk (Γ Δ : List α) (ρ : ℕ → ℕ) : Prop
  := ∀n, (hΔ : n < Δ.length) → ∃hΓ : ρ n < Γ.length, Γ[ρ n] = Δ[n]

theorem List.IsWk.bounded {ρ : ℕ → ℕ} (h : List.IsWk Γ Δ ρ) (n : ℕ) (hΔ : n < Δ.length)
  : ρ n < Γ.length := match h n hΔ with | ⟨hΓ, _⟩ => hΓ

def List.IsWk.toFinWk {ρ : ℕ → ℕ} (h : List.IsWk Γ Δ ρ) : Fin (Δ.length) → Fin (Γ.length)
  := Fin.wkOfBounded ρ h.bounded

theorem List.IsWk.toIsFWk (Γ Δ : List α) (ρ : ℕ → ℕ)
  (h : List.IsWk Γ Δ ρ) : List.IsFWk Γ Δ (List.IsWk.toFinWk h)
  := funext λ⟨i, hi⟩ => have ⟨_, h⟩ := h i hi; h

-- ... TODO: IsWks

@[simp]
theorem List.IsWk.id (Γ : List α) : List.IsWk Γ Γ id
  := λ_ hΓ => ⟨hΓ, rfl⟩

-- ... TODO: len_le

@[simp]
theorem List.IsWk.drop_all (Γ : List α) (ρ) : List.IsWk Γ [] ρ
  := λi h => by cases h

theorem List.IsWk.comp {ρ : ℕ → ℕ} {σ : ℕ → ℕ} (hρ : List.IsWk Γ Δ ρ) (hσ : List.IsWk Δ Ξ σ)
  : List.IsWk Γ Ξ (ρ ∘ σ) := λn hΞ =>
    have ⟨hΔ, hσ⟩ := hσ n hΞ;
    have ⟨hΓ, hρ⟩ := hρ _ hΔ;
    ⟨hΓ, hρ ▸ hσ⟩

theorem List.IsWk.lift {ρ : ℕ → ℕ} (hρ : List.IsWk Γ Δ ρ)
  : List.IsWk (A :: Γ) (A :: Δ) (Nat.liftWk ρ) := λn hΔ => match n with
  | 0 => ⟨Nat.zero_lt_succ _, rfl⟩
  | n+1 => have ⟨hΔ, hρ⟩ := hρ n (Nat.lt_of_succ_lt_succ hΔ); ⟨Nat.succ_lt_succ hΔ, hρ⟩

theorem List.IsWk.lift_tail {ρ : ℕ → ℕ} (h : List.IsWk (A :: Γ) (B :: Δ) (Nat.liftWk ρ))
    : List.IsWk Γ Δ ρ
  := λi hΔ => have ⟨hΔ, hρ⟩ := h i.succ (Nat.succ_lt_succ hΔ); ⟨Nat.lt_of_succ_lt_succ hΔ, hρ⟩

theorem List.IsWk.lift_head {ρ : ℕ → ℕ} (h : List.IsWk (A :: Γ) (B :: Δ) (Nat.liftWk ρ)) : A = B
  := (h 0 (Nat.zero_lt_succ _)).2

theorem List.IsWk.lift_iff (A B) (Γ Δ : List α) (ρ : ℕ → ℕ)
  : List.IsWk (A :: Γ) (B :: Δ) (Nat.liftWk ρ) ↔ A = B ∧ List.IsWk Γ Δ ρ
  := ⟨
    λh => ⟨h.lift_head, List.IsWk.lift_tail h⟩,
    λ⟨rfl, hρ⟩ => List.IsWk.lift hρ
  ⟩

theorem List.IsWk.lift_id (hρ : List.IsWk Γ Δ _root_.id)
  : List.IsWk (A :: Γ) (A :: Δ) _root_.id := Nat.liftWk_id ▸ hρ.lift

theorem List.IsWk.lift_id_tail (h : List.IsWk (left :: Γ) (right :: Δ) _root_.id)
    : List.IsWk Γ Δ _root_.id
  := (Nat.liftWk_id ▸ h).lift_tail

theorem List.IsWk.lift_id_head (h : List.IsWk (left :: Γ) (right :: Δ) _root_.id)
  : left = right
  := (Nat.liftWk_id ▸ h).lift_head

theorem List.IsWk.lift_id_iff (h : List.IsWk (left :: Γ) (right :: Δ) _root_.id)
  : left = right ∧ List.IsWk Γ Δ _root_.id
  := ⟨h.lift_id_head, h.lift_id_tail⟩

theorem List.IsWk.lift₂ {ρ : ℕ → ℕ} (hρ : List.IsWk Γ Δ ρ)
    : List.IsWk (A₁ :: A₂ :: Γ) (A₁ :: A₂ :: Δ) (Nat.liftWk (Nat.liftWk ρ))
  := hρ.lift.lift

theorem List.IsWk.liftn₂ {ρ : ℕ → ℕ} (hρ : List.IsWk Γ Δ ρ)
    : List.IsWk (A₁ :: A₂ :: Γ) (A₁ :: A₂ :: Δ) (Nat.liftnWk 2 ρ)
  := by rw [Nat.liftnWk_two]; exact hρ.lift₂

theorem List.IsWk.liftn_append {ρ : ℕ → ℕ} (Ξ : List α) (hρ : List.IsWk Γ Δ ρ)
    : List.IsWk (Ξ ++ Γ) (Ξ ++ Δ) (Nat.liftnWk Ξ.length ρ) := by
  induction Ξ with
  | nil => exact hρ
  | cons A Ξ I =>
    rw [List.length, Nat.liftnWk_succ']
    exact I.lift

theorem List.IsWk.liftn_append' {ρ : ℕ → ℕ} (Ξ : List α) (hΞ : Ξ.length = n)
  (hρ : List.IsWk Γ Δ ρ) : List.IsWk (Ξ ++ Γ) (Ξ ++ Δ) (Nat.liftnWk n ρ) := hΞ ▸ hρ.liftn_append Ξ

theorem List.IsWk.step {ρ : ℕ → ℕ} (A : α) (hρ : List.IsWk Γ Δ ρ)
    : List.IsWk (A :: Γ) Δ (Nat.succ ∘ ρ)
  := λn hΔ => have ⟨hΔ, hρ⟩ := hρ n hΔ; ⟨Nat.succ_lt_succ hΔ, hρ⟩

@[simp]
theorem List.IsWk.succ (A : α) : List.IsWk (A :: Γ) Γ .succ := step (ρ := _root_.id) A (id _)

theorem List.IsWk.step_tail {ρ : ℕ → ℕ} (h : List.IsWk (A :: Γ) Δ (Nat.succ ∘ ρ)) : List.IsWk Γ Δ ρ
  := λi hΔ => have ⟨hΔ, hρ⟩ := h i hΔ; ⟨Nat.lt_of_succ_lt_succ hΔ, hρ⟩

theorem List.IsWk.step_iff (A) (Γ Δ : List α) (ρ : ℕ → ℕ)
  : List.IsWk (A :: Γ) Δ (Nat.succ ∘ ρ) ↔ List.IsWk Γ Δ ρ
  := ⟨
    List.IsWk.step_tail,
    List.IsWk.step A
  ⟩

theorem List.IsWk.stepn_append {ρ : ℕ → ℕ} (Ξ : List α) (hρ : List.IsWk Γ Δ ρ)
    : List.IsWk (Ξ ++ Γ) Δ (Nat.stepnWk Ξ.length ρ)
  := by induction Ξ with
    | nil => exact hρ
    | cons A Ξ I =>
      rw [List.length, Nat.stepnWk_succ']
      exact I.step _

theorem List.IsWk.stepn_append' {ρ : ℕ → ℕ} (Ξ : List α) (hΞ : Ξ.length = n)
  (hρ : List.IsWk Γ Δ ρ) : List.IsWk (Ξ ++ Γ) Δ (Nat.stepnWk n ρ) := hΞ ▸ hρ.stepn_append Ξ

variable [PartialOrder α] {Γ Δ Ξ : List α}

/-- The function `ρ` weakens `Γ` to `Δ` -/
def List.FWkn (Γ Δ : List α) (ρ : Fin Δ.length → Fin Γ.length) : Prop
  := Fin.FWkn Γ.get Δ.get ρ

theorem List.FWkn.get {Γ Δ : List α} {ρ : Fin Δ.length → Fin Γ.length} (h : List.FWkn Γ Δ ρ)
  : ∀i, Γ.get (ρ i) ≤ Δ.get i := h

theorem List.FWkn.getElem {Γ Δ : List α} {ρ : Fin Δ.length → Fin Γ.length} (h : List.FWkn Γ Δ ρ)
  : ∀i, Γ[ρ i] ≤ Δ[i] := h

theorem List.FWkn.id (Γ : List α) : List.FWkn Γ Γ id := le_refl _

theorem List.FWkn.comp {ρ : Fin Δ.length → Fin Γ.length} {σ : Fin Ξ.length → Fin Δ.length}
  (hρ : List.FWkn Γ Δ ρ) (hσ : List.FWkn Δ Ξ σ) : List.FWkn Γ Ξ (ρ ∘ σ)
  := Fin.FWkn.comp hρ hσ

theorem List.FWkn.lift {ρ : Fin Δ.length → Fin Γ.length} (hAB : A ≤ B) (hρ : List.FWkn Γ Δ ρ)
    : List.FWkn (A :: Γ) (B :: Δ) (Fin.liftWk ρ)
  := λi => by cases i using Fin.cases with
  | zero => exact hAB
  | succ i => exact hρ i

theorem List.FWkn.step {ρ : Fin Δ.length → Fin Γ.length} (A : α) (hρ : List.FWkn Γ Δ ρ)
  : List.FWkn (A :: Γ) Δ (Fin.stepWk ρ) := λi => hρ i

/-- The list `Γ` weakens to `Δ` -/
def List.FWkns (Γ Δ : List α) : Prop := ∃ρ, List.FWkn Γ Δ ρ ∧ StrictMono ρ

theorem List.FWkns.refl (Γ : List α) : List.FWkns Γ Γ
  := ⟨id, List.FWkn.id Γ, strictMono_id⟩

theorem List.FWkns.trans (hAB : List.FWkns Γ Δ) (hBC : List.FWkns Δ Ξ) : List.FWkns Γ Ξ
  := match hAB, hBC with
  | ⟨ρ, hAB, hρ⟩, ⟨σ, hBC, hσ⟩ => ⟨ρ ∘ σ, List.FWkn.comp hAB hBC, hρ.comp hσ⟩

theorem List.FWkns.len_le (hAB : List.FWkns Γ Δ) : Δ.length ≤ Γ.length
  := match hAB with | ⟨ρ, _, hρ⟩ => by {
    have h := Fintype.card_fin _ ▸ Fintype.card_fin _ ▸ Fintype.card_le_of_injective _ hρ.injective;
    simp only [Fintype.card_fin] at h
    exact h
  }

theorem List.FWkns.antisymm (hAB : List.FWkns Γ Δ) (hBA : List.FWkns Δ Γ) : Γ = Δ :=
  -- TODO: why does le_antisymm not work here?
  have len_eq : Γ.length = Δ.length := le_antisymm_iff.mpr ⟨hBA.len_le, hAB.len_le⟩
  match hAB, hBA with
  | ⟨ρ, hAB, hρ⟩, ⟨σ, hBA, hσ⟩
    => by
      cases Fin.strictMono_eq_cast hρ len_eq.symm
      cases Fin.strictMono_eq_cast hσ len_eq
      exact List.ext_get len_eq λi h h' => le_antisymm_iff.mpr ⟨hAB ⟨i, h'⟩, hBA ⟨i, h⟩⟩

/-- The function `ρ` weakens `Γ` to `Δ` -/
def List.NWkn (Γ Δ : List α) (ρ : ℕ → ℕ) : Prop
  := ∀n, (hΔ : n < Δ.length) → ∃hΓ : ρ n < Γ.length, Γ.get ⟨ρ n , hΓ⟩ ≤ Δ.get ⟨n, hΔ⟩

theorem List.NWkn.bounded {ρ : ℕ → ℕ} (h : List.NWkn Γ Δ ρ) (n : ℕ) (hΔ : n < Δ.length)
  : ρ n < Γ.length := match h n hΔ with | ⟨hΓ, _⟩ => hΓ

-- TODO: abbrev, or remove?
/-- Restrict `ρ` from a function on `ℕ` to indices into `Δ` -/
def List.NWkn.toFinWk {ρ : ℕ → ℕ} (h : List.NWkn Γ Δ ρ) : Fin (Δ.length) → Fin (Γ.length)
  := Fin.wkOfBounded ρ h.bounded

theorem List.NWkn.toFWkn (Γ Δ : List α) (ρ : ℕ → ℕ)
  (h : List.NWkn Γ Δ ρ) : List.FWkn Γ Δ (List.NWkn.toFinWk h)
  := λ⟨i, hi⟩ => have ⟨_, h⟩ := h i hi; h

theorem List.NWkn_iff (Γ Δ : List α) (ρ : ℕ → ℕ)
  : List.NWkn Γ Δ ρ ↔ ∃ρ', List.FWkn Γ Δ ρ' ∧ ∀i : Fin Δ.length, ρ i = ρ' i
  := ⟨
    λh => ⟨_, h.toFWkn, λ_ => rfl⟩,
    λ⟨ρ', h, hρ'⟩ n hΔ =>
      have hρ' : ρ n = ρ' ⟨n, hΔ⟩ := hρ' ⟨n, hΔ⟩;
      have hΓ' : ρ' ⟨n, hΔ⟩ < Γ.length := by simp;
      have hΓ : ρ n < Γ.length := hρ' ▸ hΓ';
      have h' : Γ.get ⟨ρ' ⟨n, hΔ⟩, hΓ'⟩ ≤ Δ.get ⟨n, hΔ⟩ := h ⟨n, hΔ⟩;
      have hΓn : Γ.get ⟨ρ' ⟨n, hΔ⟩, hΓ'⟩ = Γ.get ⟨ρ n, hΓ⟩ := by
        congr
        exact hρ'.symm
      ⟨hρ' ▸ hΓ, hΓn ▸ h'⟩
  ⟩

theorem List.NWkn.id (Γ : List α) : List.NWkn Γ Γ id
  := λ_ hΓ => ⟨hΓ, le_refl _⟩

theorem List.NWkn.len_le {Γ Δ : List α} (h : List.NWkn Γ Δ ρ) (hρ : StrictMono ρ)
  : Δ.length ≤ Γ.length
  := FWkns.len_le ⟨_, h.toFWkn, Fin.wkOfBounded_strictMono hρ⟩

theorem List.NWkn.id_len_le {Γ Δ : List α} (h : List.NWkn Γ Δ _root_.id)
  : Δ.length ≤ Γ.length := h.len_le strictMono_id

theorem List.NWkn.drop_all (Γ : List α) (ρ) : List.NWkn Γ [] ρ
  := λi h => by cases h

theorem List.NWkn.comp {ρ : ℕ → ℕ} {σ : ℕ → ℕ} (hρ : List.NWkn Γ Δ ρ) (hσ : List.NWkn Δ Ξ σ)
  : List.NWkn Γ Ξ (ρ ∘ σ) := λn hΞ =>
    have ⟨hΔ, hσ⟩ := hσ n hΞ;
    have ⟨hΓ, hρ⟩ := hρ _ hΔ;
    ⟨hΓ, le_trans hρ hσ⟩

theorem List.NWkn.lift {ρ : ℕ → ℕ} (hAB : A ≤ B) (hρ : List.NWkn Γ Δ ρ)
  : List.NWkn (A :: Γ) (B :: Δ) (Nat.liftWk ρ) := λn hΔ => match n with
  | 0 => ⟨Nat.zero_lt_succ _, hAB⟩
  | n+1 => have ⟨hΔ, hρ⟩ := hρ n (Nat.lt_of_succ_lt_succ hΔ); ⟨Nat.succ_lt_succ hΔ, hρ⟩

theorem List.NWkn.lift_tail {ρ : ℕ → ℕ} (h : List.NWkn (left :: Γ) (right :: Δ) (Nat.liftWk ρ))
    : List.NWkn Γ Δ ρ
  := λi hΔ => have ⟨hΔ, hρ⟩ := h i.succ (Nat.succ_lt_succ hΔ); ⟨Nat.lt_of_succ_lt_succ hΔ, hρ⟩

theorem List.NWkn.lift_head {ρ : ℕ → ℕ} (h : List.NWkn (left :: Γ) (right :: Δ) (Nat.liftWk ρ))
  : left ≤ right
  := (h 0 (Nat.zero_lt_succ _)).2

theorem List.NWkn.lift_iff (A B) (Γ Δ : List α) (ρ : ℕ → ℕ)
  : List.NWkn (A :: Γ) (B :: Δ) (Nat.liftWk ρ) ↔ A ≤ B ∧ List.NWkn Γ Δ ρ
  := ⟨
    λh => ⟨h.lift_head, List.NWkn.lift_tail h⟩,
    λ⟨hAB, hρ⟩ => List.NWkn.lift hAB hρ
  ⟩

theorem List.NWkn.lift_id (hρ : List.NWkn Γ Δ _root_.id) (h : A ≤ B)
  : List.NWkn (A :: Γ) (B :: Δ) _root_.id := Nat.liftWk_id ▸ hρ.lift h

theorem List.NWkn.lift_id_tail (h : List.NWkn (left :: Γ) (right :: Δ) _root_.id)
    : List.NWkn Γ Δ _root_.id
  := (Nat.liftWk_id ▸ h).lift_tail

theorem List.NWkn.lift_id_head (h : List.NWkn (left :: Γ) (right :: Δ) _root_.id)
  : left ≤ right
  := (Nat.liftWk_id ▸ h).lift_head

theorem List.NWkn.lift_id_iff (h : List.NWkn (left :: Γ) (right :: Δ) _root_.id)
  : left ≤ right ∧ List.NWkn Γ Δ _root_.id
  := ⟨h.lift_id_head, h.lift_id_tail⟩

theorem List.NWkn.lift₂ {ρ : ℕ → ℕ} (hAB₁ : A₁ ≤ B₁) (hAB₂ : A₂ ≤ B₂) (hρ : List.NWkn Γ Δ ρ)
    : List.NWkn (A₁ :: A₂ :: Γ) (B₁ :: B₂ :: Δ) (Nat.liftWk (Nat.liftWk ρ))
  := (hρ.lift hAB₂).lift hAB₁

theorem List.NWkn.liftn₂ {ρ : ℕ → ℕ} (hAB₁ : A₁ ≤ B₁) (hAB₂ : A₂ ≤ B₂) (hρ : List.NWkn Γ Δ ρ)
    : List.NWkn (A₁ :: A₂ :: Γ) (B₁ :: B₂ :: Δ) (Nat.liftnWk 2 ρ)
  := by rw [Nat.liftnWk_eq_iterate_liftWk]; exact lift₂ hAB₁ hAB₂ hρ

theorem List.NWkn.liftn_append {ρ : ℕ → ℕ} (Ξ : List α) (hρ : List.NWkn Γ Δ ρ)
    : List.NWkn (Ξ ++ Γ) (Ξ ++ Δ) (Nat.liftnWk Ξ.length ρ) := by
  induction Ξ with
  | nil => exact hρ
  | cons A Ξ I =>
    rw [List.length, Nat.liftnWk_succ']
    exact I.lift (le_refl _)

theorem List.NWkn.liftn_append' {ρ : ℕ → ℕ} (Ξ : List α) (hΞ : Ξ.length = n) (hρ : List.NWkn Γ Δ ρ)
    : List.NWkn (Ξ ++ Γ) (Ξ ++ Δ) (Nat.liftnWk n ρ)
  := hΞ ▸ hρ.liftn_append Ξ

-- TODO: pointwise liftn

theorem List.NWkn.step {ρ : ℕ → ℕ} (A : α) (hρ : List.NWkn Γ Δ ρ)
    : List.NWkn (A :: Γ) Δ (Nat.succ ∘ ρ)
  := λn hΔ => have ⟨hΔ, hρ⟩ := hρ n hΔ; ⟨Nat.succ_lt_succ hΔ, hρ⟩

theorem List.NWkn.step_tail {ρ : ℕ → ℕ} (h : List.NWkn (A :: Γ) Δ (Nat.succ ∘ ρ)) : List.NWkn Γ Δ ρ
  := λi hΔ => have ⟨hΔ, hρ⟩ := h i hΔ; ⟨Nat.lt_of_succ_lt_succ hΔ, hρ⟩

theorem List.NWkn.step_iff (A) (Γ Δ : List α) (ρ : ℕ → ℕ)
  : List.NWkn (A :: Γ) Δ (Nat.succ ∘ ρ) ↔ List.NWkn Γ Δ ρ
  := ⟨
    List.NWkn.step_tail,
    List.NWkn.step A
  ⟩

theorem List.NWkn.stepn_append {ρ : ℕ → ℕ} (Ξ : List α) (hρ : List.NWkn Γ Δ ρ)
    : List.NWkn (Ξ ++ Γ) Δ (Nat.stepnWk Ξ.length ρ)
  := by induction Ξ with
    | nil => exact hρ
    | cons A Ξ I =>
      rw [List.length, Nat.stepnWk_succ']
      exact I.step _

theorem List.NWkn.stepn_append' {ρ : ℕ → ℕ} (Ξ : List α) (hΞ : Ξ.length = n) (hρ : List.NWkn Γ Δ ρ)
  : List.NWkn (Ξ ++ Γ) Δ (Nat.stepnWk n ρ) := hΞ ▸ hρ.stepn_append Ξ

-- TODO: step₂, stepn₂, stepn

-- TODO: if the order is discrete, weakenings are unique iff there are no duplicates in the source

-- TODO: if the order is discrete and there are no duplicates in the source, then the are none
--       in the target

theorem List.IsWk.toNWkn (Γ Δ : List α) (ρ : ℕ → ℕ)
  (h : List.IsWk Γ Δ ρ) : List.NWkn Γ Δ ρ
  := λn hΔ => match h n hΔ with | ⟨hΓ, h⟩ => ⟨hΓ, le_of_eq h⟩

/-- The list Γ has a member compatible with `A` at index `n` -/
def List.FVar (Γ : List α) (n : Fin Γ.length) (A : α) : Prop := Γ.get n ≤ A

theorem List.FVar.le_trg {A A' : α} {n : Fin Γ.length} (h : List.FVar Γ n A) (hA : A ≤ A')
  : List.FVar Γ n A' := le_trans h hA

theorem List.FVar.head_le {A A' : α} (h : A ≤ A') : List.FVar (A :: Γ) ⟨0, by simp⟩ A'
  := h

theorem List.FVar.head (A : α) : List.FVar (A :: Γ) ⟨0, by simp⟩ A := le_refl _

theorem List.FVar.tail (A : α) (h : List.FVar Γ n B) : List.FVar (A :: Γ) n.succ B
  := h

/-- The list Γ has a member compatible with `A` at index `n` -/
structure List.Var (Γ : List α) (n : ℕ) (A : α) : Prop where
  length : n < Γ.length
  get : Γ.FVar ⟨n, length⟩ A

theorem List.Var.le_trg {A A' : α} {n : ℕ} (h : List.Var Γ n A) (hA : A ≤ A') : List.Var Γ n A'
  := ⟨h.length, le_trans h.get hA⟩

theorem List.Var.head_le {A A' : α} (h : A ≤ A') : List.Var (A :: Γ) 0 A'
  := ⟨Nat.zero_lt_succ _, h⟩

theorem List.Var.head (A : α) : List.Var (A :: Γ) 0 A := ⟨Nat.zero_lt_succ _, le_refl _⟩

theorem List.Var.tail (A : α) (h : List.Var Γ n B) : List.Var (A :: Γ) (n+1) B
  := ⟨Nat.succ_lt_succ h.length, h.get⟩

-- TODO: Var.wkn

-- TODO: inductive weakening, associated lore
