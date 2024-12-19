import Discretion.Wk.Nat
import Discretion.Wk.Fin
import Discretion.Wk.NatInductive
import Discretion.Fin.Preimage
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

theorem List.Wk.ix_nw {α} {Γ Δ : List α} (ρ : Wk Γ Δ) : ρ.nw.ix = ρ.ix := by
  induction ρ <;> simp only [nw, ix, Nat.Wk.ix, *]

theorem List.Wk.ix_comp_nw {α Γ Δ} : Nat.Wk.ix ∘ nw = ix (α := α) (Γ := Γ) (Δ := Δ)
  := funext ix_nw

theorem List.Wk.ix_injective {α} {Γ Δ : List α} : Function.Injective (@List.Wk.ix α Γ Δ) := by
  rw [<-ix_comp_nw]; apply Function.Injective.comp; apply Nat.Wk.ix_injective; apply nw_injective

theorem List.Wk.ix_inj {α} {Γ Δ : List α} {ρ σ : Wk Γ Δ} : List.Wk.ix ρ = List.Wk.ix σ ↔ ρ = σ
  := ix_injective.eq_iff

def List.Wk.ixf {α} : ∀{Γ Δ : List α}, Wk Γ Δ → Fin Δ.length → Fin Γ.length
  | _, _, .nil => Fin.elim0
  | _, _, .step A ρ => Fin.stepWk ρ.ixf
  | _, _, .lift A ρ => Fin.liftWk ρ.ixf

theorem List.Wk.ixf_nw {α} {Γ Δ : List α} (ρ : Wk Γ Δ) : ρ.nw.ixf = ρ.ixf := by
  induction ρ with
  | nil => funext i; exact i.elim0
  | _ => simp only [nw, ixf, Nat.Wk.ixf, *]

theorem List.Wk.ixf_comp_nw {α Γ Δ} : Nat.Wk.ixf ∘ nw = ixf (α := α) (Γ := Γ) (Δ := Δ)
  := funext ixf_nw

theorem List.Wk.ixf_injective {α} {Γ Δ : List α} : Function.Injective (@ixf α Γ Δ) := by
  rw [<-ixf_comp_nw]; apply Function.Injective.comp; apply Nat.Wk.ixf_injective; apply nw_injective

theorem List.Wk.ixf_inj {α} {Γ Δ : List α} {ρ σ : Wk Γ Δ} : List.Wk.ixf ρ = List.Wk.ixf σ ↔ ρ = σ
  := ixf_injective.eq_iff

def List.Wk.ixf0 {α} {Γ Δ : List α} {A} : Wk Γ (A::Δ) → Fin Γ.length
  | .step A ρ => ρ.ixf0.succ
  | .lift A ρ => (0 : Fin (_ + 1))

theorem List.Wk.ixf0_eq {α} {Γ Δ : List α} {A} (ρ : Wk Γ (A::Δ))
  : ρ.ixf (0 : Fin (_ + 1)) = ρ.ixf0 := by induction Γ <;> cases ρ <;> simp [ixf0, ixf, *]

def List.Wk.ix0 {α} {Γ Δ : List α} {A} : Wk Γ (A::Δ) → ℕ
  | .step A ρ => ρ.ix0 + 1
  | .lift A ρ => 0

theorem List.Wk.ix0_eq {α} {Γ Δ : List α} {A} (ρ : Wk Γ (A::Δ))
  : ρ.ix 0 = ρ.ix0 := by induction Γ <;> cases ρ <;> simp [ix0, ix, *]

def List.Wk.varIx {α} {Γ : List α} (i : ℕ) (hi : i < Γ.length) : Wk Γ [Γ[i]]
  := match Γ, i, hi with
  | A::Γ, 0, _ => (drop Γ).lift A
  | A::_, n + 1, hi => (varIx n (Nat.lt_of_succ_lt_succ hi)).step A

def List.Wk.varIx' {α} {Γ : List α} {A} (i : ℕ) (hi : i < Γ.length) (hA : Γ[i] = A) : Wk Γ [A]
  := hA ▸ varIx i hi

theorem List.Wk.ix0_varIx {α} {Γ : List α} (i : ℕ) (hi : i < Γ.length)
  : (varIx i hi).ix0 = i := by
  induction Γ generalizing i with
  | nil => cases hi
  | cons A Γ I => cases i with
  | zero => rfl
  | succ i => simp only [ix0, getElem_cons_succ, add_left_inj, I]

def List.Wk.varFin {α} {Γ : List α} (i : Fin Γ.length) : Wk Γ [Γ[i]]
  := varIx i.val i.is_lt

-- TODO: varFin is a bijection

def List.Wk.varFin' {α} {Γ : List α} {A} (i : Fin Γ.length) (hA : Γ[i] = A) : Wk Γ [A]
  := hA ▸ varFin i

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

def List.Wk.minQ {α} : ∀{Γ Δ : List α}, Wk Γ Δ → Vector' EQuant Γ.length
  | _, _, .nil => .nil
  | _, _, .step _ ρ => (ρ.minQ).cons 0
  | _, _, .lift _ ρ => (ρ.minQ).cons 1

-- eΔ ≤ ρ.pv eΓ

-- TODO: Wk wf iff minQ leq qs...

-- TODO: Split wf iff sum minQ leq qs...

inductive List.QWk {α} : (Γ Δ : List α) →
  (qΓ : Vector' EQuant Γ.length) → (qΔ : Vector' EQuant Δ.length) → Type
  | nil : QWk [] [] .nil .nil
  | step (A qa) (h : qa = 0 ∨ .del ≤ qa) {Γ Δ qΓ qΔ}
    : QWk Γ Δ qΓ qΔ → QWk (A :: Γ) Δ (qΓ.cons qa) qΔ
  | lift (A lo hi) (h : lo ≤ hi) {Γ Δ qΓ qΔ}
    : QWk Γ Δ qΓ qΔ → QWk (A :: Γ) (A :: Δ) (qΓ.cons hi) (qΔ.cons lo)

def List.QWk.nw {α} {Γ Δ : List α} {qΓ qΔ} : QWk Γ Δ qΓ qΔ → Nat.Wk Γ.length Δ.length
  | .nil => .nil
  | .step _ _ _ ρ => ρ.nw.step
  | .lift _ _ _ _ ρ => ρ.nw.lift

def List.QWk.toWk {α} {Γ Δ : List α} {qΓ qΔ} : QWk Γ Δ qΓ qΔ → Wk Γ Δ
  | .nil => .nil
  | .step _ _ _ ρ => .step _ ρ.toWk
  | .lift _ _ _ _ ρ => .lift _ ρ.toWk

theorem List.QWk.nw_toWk {α} {Γ Δ : List α} {qΓ qΔ} (ρ : QWk Γ Δ qΓ qΔ)
  : ρ.toWk.nw = ρ.nw := by
  induction ρ <;> simp only [nw, toWk, Wk.nw, *]

-- TODO: independent inductive definitions?
def List.QWk.ix {α} {Γ Δ : List α} {qΓ qΔ} (ρ : QWk Γ Δ qΓ qΔ) : ℕ → ℕ := ρ.toWk.ix

def List.QWk.pv {α} {Γ Δ : List α} {qΓ qΔ} (ρ : QWk Γ Δ qΓ qΔ)
  : Vector' β Γ.length → Vector' β Δ.length := ρ.toWk.pv

def List.QWk.toWk_injective {α} {Γ Δ : List α} {qΓ qΔ}
  : Function.Injective (@List.QWk.toWk α Γ Δ qΓ qΔ)
  := λρ ρ' => by induction ρ <;> cases ρ' <;> simp [toWk] <;> apply_assumption

theorem List.QWk.nw_injective {α} {Γ Δ : List α} {qΓ qΔ}
  : Function.Injective (@List.QWk.nw α Γ Δ qΓ qΔ)
  := by convert Wk.nw_injective.comp toWk_injective; funext i; simp [nw_toWk]

theorem List.QWk.ix_injective {α} {Γ Δ : List α} {qΓ qΔ}
  : Function.Injective (@List.QWk.ix α Γ Δ qΓ qΔ)
  := Wk.ix_injective.comp toWk_injective

def List.QPWk (Γ Δ : List α) (qs : Vector' EQuant Γ.length) := {ρ : Wk Γ Δ | ρ.Wf qs}

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

open BoundedOn

instance List.succ_bounded_on_length {A : α} {Γ : List α}
  : BoundedOn Γ.length (A::Γ).length Nat.succ := ⟨by simp⟩

instance List.succ_bounded_from_length {A : α} {Γ : List α}
  : BoundedFrom Γ.length (A::Γ).length Nat.succ := ⟨by simp⟩

instance List.liftWk_bounded_on_length {A : α} {Γ Δ : List α} {ρ}
  [hρ : BoundedOn Γ.length Δ.length ρ] : BoundedOn (A::Γ).length (A::Δ).length (Nat.liftWk ρ)
  := Nat.liftWk_bounded_on (hρ := hρ)

instance List.liftWk_bounded_from_length {A : α} {Γ Δ : List α} {ρ}
  [hρ : BoundedFrom Γ.length Δ.length ρ] : BoundedFrom (A::Γ).length (A::Δ).length (Nat.liftWk ρ)
  := Nat.liftWk_bounded_from (hρ := hρ)

/-- The function `ρ` sends `Γ` to `Δ` -/
class List.IsRen (Γ Δ : List α) (ρ : ℕ → ℕ) extends BoundedOn Δ.length Γ.length ρ : Prop where
  getElem_eq : ∀i, (h : i < Δ.length) → Γ[ρ i]'(bounded_on i h) = Δ[i]

def List.IsRen.toFinWk {ρ : ℕ → ℕ} (h : List.IsRen Γ Δ ρ) : Fin (Δ.length) → Fin (Γ.length)
  := Fin.wkOfBounded ρ h.bounded_on

theorem List.IsRen.toIsFWk (Γ Δ : List α) (ρ : ℕ → ℕ)
  (h : List.IsRen Γ Δ ρ) : List.IsFWk Γ Δ (List.IsRen.toFinWk h)
  := funext λ⟨i, hi⟩ => h.getElem_eq i hi

-- ... TODO: IsRens

@[simp]
instance List.IsRen.id (Γ : List α) : List.IsRen Γ Γ id where
  getElem_eq := λ_ _ => rfl

-- ... TODO: len_le

@[simp]
instance List.IsRen.drop_all (Γ : List α) (ρ) : List.IsRen Γ [] ρ where
  bounded_on i h := by cases h
  getElem_eq i h := by cases h

theorem List.IsRen.comp (Γ Δ Ξ : List α) {ρ σ} [hρ : List.IsRen Γ Δ ρ] [hσ : List.IsRen Δ Ξ σ]
  : List.IsRen Γ Ξ (ρ ∘ σ) where
  toBoundedOn := BoundedOn.comp Ξ.length Δ.length Γ.length
  getElem_eq i h := hρ.getElem_eq (σ i) (hσ.bounded_on i h) ▸ hσ.getElem_eq i h

instance List.IsRen.lift {ρ : ℕ → ℕ} [hρ : List.IsRen Γ Δ ρ]
  : List.IsRen (A :: Γ) (A :: Δ) (Nat.liftWk ρ) where
  toBoundedOn := Nat.liftWk_bounded_on
  getElem_eq i h := match i with
  | 0 => rfl
  | i + 1 => hρ.getElem_eq i (Nat.lt_of_succ_lt_succ h)

theorem List.IsRen.lift_tail {ρ : ℕ → ℕ} (hρ : List.IsRen (A :: Γ) (B :: Δ) (Nat.liftWk ρ))
  : List.IsRen Γ Δ ρ where
  toBoundedOn := Nat.liftWk_bounded_on_tail (hρ := hρ.toBoundedOn)
  getElem_eq i h := hρ.getElem_eq (i + 1) (Nat.succ_lt_succ h)

theorem List.IsRen.lift_head {ρ : ℕ → ℕ} [hρ : List.IsRen (A :: Γ) (B :: Δ) (Nat.liftWk ρ)] : A = B
  := hρ.getElem_eq 0 (Nat.zero_lt_succ Δ.length)

theorem List.IsRen.lift_iff (A B) (Γ Δ : List α) (ρ : ℕ → ℕ)
  : List.IsRen (A :: Γ) (B :: Δ) (Nat.liftWk ρ) ↔ A = B ∧ List.IsRen Γ Δ ρ
  := ⟨λh => ⟨h.lift_head, h.lift_tail⟩, λ⟨rfl, hρ⟩ => hρ.lift⟩

theorem List.IsRen.lift_id (hρ : List.IsRen Γ Δ _root_.id)
  : List.IsRen (A :: Γ) (A :: Δ) _root_.id := Nat.liftWk_id ▸ hρ.lift

theorem List.IsRen.lift_id_tail (h : List.IsRen (left :: Γ) (right :: Δ) _root_.id)
  : List.IsRen Γ Δ _root_.id
  := (Nat.liftWk_id ▸ h).lift_tail

theorem List.IsRen.lift_id_head (h : List.IsRen (left :: Γ) (right :: Δ) _root_.id)
  : left = right
  := (Nat.liftWk_id ▸ h).lift_head

theorem List.IsRen.lift_id_iff (h : List.IsRen (left :: Γ) (right :: Δ) _root_.id)
  : left = right ∧ List.IsRen Γ Δ _root_.id
  := ⟨h.lift_id_head, h.lift_id_tail⟩

theorem List.IsRen.lift₂ (ρ : ℕ → ℕ) [hρ : List.IsRen Γ Δ ρ]
  : List.IsRen (A₁ :: A₂ :: Γ) (A₁ :: A₂ :: Δ) (Nat.liftWk (Nat.liftWk ρ))
  := inferInstance

instance List.IsRen.liftn₂ (ρ : ℕ → ℕ) [hρ : List.IsRen Γ Δ ρ]
  : List.IsRen (A₁ :: A₂ :: Γ) (A₁ :: A₂ :: Δ) (Nat.liftnWk 2 ρ)
  := by rw [Nat.liftnWk_two]; exact hρ.lift₂

instance List.IsRen.liftn_append (Ξ : List α) (ρ : ℕ → ℕ) (hρ : List.IsRen Γ Δ ρ)
  : List.IsRen (Ξ ++ Γ) (Ξ ++ Δ) (Nat.liftnWk Ξ.length ρ) := by
  induction Ξ with
  | nil => exact hρ
  | cons A Ξ I =>
    rw [List.length, Nat.liftnWk_succ']
    exact I.lift

theorem List.IsRen.liftn_append' (Ξ : List α) (ρ : ℕ → ℕ) (hΞ : Ξ.length = n)
  (hρ : List.IsRen Γ Δ ρ) : List.IsRen (Ξ ++ Γ) (Ξ ++ Δ) (Nat.liftnWk n ρ) := hΞ ▸ hρ.liftn_append Ξ

instance List.IsRen.step (A : α) (ρ : ℕ → ℕ) [hρ : List.IsRen Γ Δ ρ]
  : List.IsRen (A :: Γ) Δ (Nat.stepWk ρ) where
  bounded_on i h := Nat.succ_lt_succ (hρ.bounded_on i h)
  getElem_eq i h := hρ.getElem_eq i h

@[simp]
instance List.IsRen.succ (A : α) : List.IsRen (A :: Γ) Γ .succ
  := step (Γ := Γ) (Δ := Γ) (ρ := _root_.id) A

theorem List.IsRen.step_tail (A) (ρ : ℕ → ℕ) [hρ : List.IsRen (A :: Γ) Δ (Nat.stepWk ρ)]
  : List.IsRen Γ Δ ρ where
  bounded_on i h := Nat.lt_of_succ_lt_succ (hρ.bounded_on i h)
  getElem_eq i h := hρ.getElem_eq i h

theorem List.IsRen.step_iff (A) (Γ Δ : List α) (ρ : ℕ → ℕ)
  : List.IsRen (A :: Γ) Δ (Nat.stepWk ρ) ↔ List.IsRen Γ Δ ρ
  := ⟨
    λ_ => List.IsRen.step_tail A ρ,
    λ_ => List.IsRen.step A ρ
  ⟩

theorem List.IsRen.stepn_append {ρ : ℕ → ℕ} (Ξ : List α) (hρ : List.IsRen Γ Δ ρ)
    : List.IsRen (Ξ ++ Γ) Δ (Nat.stepnWk Ξ.length ρ)
  := by induction Ξ with
    | nil => exact hρ
    | cons A Ξ I =>
      rw [List.length, Nat.stepnWk_succ']
      exact I.step _

theorem List.IsRen.stepn_append' {ρ : ℕ → ℕ} (Ξ : List α) (hΞ : Ξ.length = n)
  (hρ : List.IsRen Γ Δ ρ) : List.IsRen (Ξ ++ Γ) Δ (Nat.stepnWk n ρ) := hΞ ▸ hρ.stepn_append Ξ

theorem List.IsRen.head (hρ : IsRen (α := α) Γ (A::Δ) ρ) : Γ[ρ 0]'(hρ.bounded_on 0 (by simp)) = A
  := hρ.getElem_eq 0 (by simp)

theorem List.IsRen.tail (hρ : IsRen (α := α) Γ (A::Δ) ρ) : IsRen Γ Δ (ρ ∘ .succ) where
  bounded_on i h := by apply hρ.bounded_on; simp [h]
  getElem_eq i h := hρ.getElem_eq (i + 1) (Nat.succ_lt_succ h)

instance List.IsRen.ix {Γ Δ : List α} (ρ : List.Wk Γ Δ) : List.IsRen Γ Δ ρ.ix where
  toBoundedOn := by convert ρ.nw.ix_bounded_on; rw [List.Wk.ix_nw]
  getElem_eq i h := by
    induction ρ generalizing i with
    | nil => cases h
    | step => simp [Wk.ix, *]
    | lift _ _ I => cases i with | zero => rfl | succ =>
      simp only [Wk.ix, Nat.liftWk_succ, getElem_cons_succ]
      rw [I]

-- theorem List.IsRen.cons {Γ Δ} (A i) {hi : i < Γ.length} (hρ : IsRen Γ Δ ρ) (hΓ : Γ[i] = A)
--   : IsRen (α := α) Γ Δ (λ| 0 => i | i + 1 => ρ i) where
--   bounded_on j h := by cases j <;> simp [hρ.bounded_on, *]
--   getElem_eq j h := by sorry

class List.IsQRen {Γ Δ : List α}
  (qΓ : Vector' EQuant Γ.length) (qΔ : Vector' EQuant Δ.length) (ρ : ℕ → ℕ)
  extends IsRen Γ Δ ρ where
  quant_le_sum : BoundedOn.pvSum ρ qΔ ≤ qΓ

theorem List.IsQRen.id_of_le {Γ : List α} {qΓ qΓ' : Vector' EQuant Γ.length} (hq : qΓ' ≤ qΓ)
  : List.IsQRen qΓ qΓ' _root_.id where
  quant_le_sum := by simp [hq]

instance List.IsQRen.id {Γ : List α} (qΓ : Vector' EQuant Γ.length)
  : List.IsQRen qΓ qΓ _root_.id := id_of_le (le_refl _)

theorem List.IsQRen.step_of_le {Γ Δ : List α}
  (A : α) (q : EQuant) (qΓ : Vector' EQuant Γ.length) (qΔ : Vector' EQuant Δ.length) (ρ)
  (hq : 0 ≤ q) [hρ : IsQRen qΓ qΔ ρ] : IsQRen (Γ := A::Γ) (qΓ.cons q) qΔ (Nat.stepWk ρ) where
  quant_le_sum := by simp [hq, hρ.quant_le_sum]

instance List.IsQRen.step {Γ Δ : List α}
  (A : α) (qΓ : Vector' EQuant Γ.length) (qΔ : Vector' EQuant Δ.length) (ρ)
  [hρ : IsQRen qΓ qΔ ρ] : IsQRen (Γ := A::Γ) (qΓ.cons 0) qΔ (Nat.stepWk ρ)
  := step_of_le A 0 qΓ qΔ ρ (le_refl _)

instance List.IsQRen.succ {Γ : List α}
  (A : α) (qΓ : Vector' EQuant Γ.length) : IsQRen (Γ := A::Γ) (qΓ.cons 0) qΓ .succ
  := step A qΓ qΓ _root_.id

theorem List.IsQRen.lift_of_le {Γ Δ : List α}
  (A : α) (q q' : EQuant) (qΓ : Vector' EQuant Γ.length) (qΔ : Vector' EQuant Δ.length) (ρ)
  (hq : q ≤ q') [hρ : IsQRen qΓ qΔ ρ]
  : IsQRen (Γ := A::Γ) (Δ := A::Δ) (qΓ.cons q') (qΔ.cons q) (Nat.liftWk ρ) where
  quant_le_sum := by simp [hq, hρ.quant_le_sum]

instance List.IsQRen.lift {Γ Δ : List α}
  (A : α) (q : EQuant) (qΓ : Vector' EQuant Γ.length) (qΔ : Vector' EQuant Δ.length) (ρ)
  [hρ : IsQRen qΓ qΔ ρ] : IsQRen (Γ := A::Γ) (Δ := A::Δ) (qΓ.cons q) (qΔ.cons q) (Nat.liftWk ρ)
  := lift_of_le A q q qΓ qΔ ρ (le_refl _)

theorem List.IsQRen.le_zero {Γ Δ : List α}
  (qΓ : Vector' EQuant Γ.length) (qΔ : Vector' EQuant Δ.length) (ρ)
  [hρ : IsQRen qΓ qΔ ρ] (h : 0 ≤ qΔ) : 0 ≤ qΓ := by
  apply le_trans _ hρ.quant_le_sum
  apply Vector'.le_of_get_le
  intro i
  simp [pvSum, finVSum, finSum, Fintype.preSum]
  generalize Finset.preimageF (hρ.toFin ρ) {i} = s
  induction s using Finset.induction with
  | empty => simp
  | insert =>
    simp only [not_false_eq_true, Finset.sum_insert, *]
    apply EQuant.zero_le_add
    convert (Vector'.get_le_of_le h) _
    simp
    assumption

instance List.IsQRen.zero_zero (Γ Δ : List α) (ρ) [hρ : IsRen Γ Δ ρ]
  : IsQRen (Γ := Γ) (Δ := Δ) 0 0 ρ where quant_le_sum := by simp

instance List.IsQRen.zero_nil (Γ : List α) (ρ) : IsQRen (Γ := Γ) (Δ := []) 0 .nil ρ
  := zero_zero Γ [] ρ

-- TODO: false; need pvsum lore here...
theorem List.IsQRen.tail_pvSum {Γ Δ : List α}
  {qΓ : Vector' EQuant Γ.length} {qΔ : Vector' EQuant Δ.length} (ρ)
  (hρ : IsQRen (Δ := A :: Δ) qΓ (qΔ.cons q) ρ)
  : IsQRen (Γ := Γ) ((hρ.comp_succ).pvSum (ρ ∘ .succ) qΔ) qΔ (ρ ∘ .succ) where
  toIsRen := hρ.toIsRen.tail
  quant_le_sum := by rfl

open BoundedOn

instance List.IsQRen.of_pvSum (Γ Δ : List α) (qΔ : Vector' EQuant Δ.length) {ρ}
  [hρ : IsRen Γ Δ ρ] : IsQRen (Γ := Γ) (pvSum ρ qΔ) qΔ ρ where
  quant_le_sum := le_refl _

theorem List.IsQRen.split_pvSum {Γ qΓ ρ Δ qΔl qΔr qΔ}
  (hqs : qΔl + qΔr ≤ qΔ) (hρ : IsQRen (α := α) (Γ := Γ) (Δ := Δ) qΓ qΔ ρ)
  : pvSum ρ qΔl + pvSum ρ qΔr ≤ qΓ
  := hρ.le_pvSum_of_le_sum (q := qΓ) (hlr := hqs) (hq := hρ.quant_le_sum)

structure List.IsQRen.Split (Γ : List α) (qΓ) (ρ) (Δ) (qΔl qΔr) where
  (qΓl qΓr : Vector' EQuant Γ.length)
  (hρl : IsQRen (Δ := Δ) qΓl qΔl ρ)
  (hρr : IsQRen (Δ := Δ) qΓr qΔr ρ)
  (hlr : qΓl + qΓr ≤ qΓ)

def List.IsQRen.split {Γ qΓ ρ Δ qΔl qΔr qΔ}
  (hqs : qΔl + qΔr ≤ qΔ) (hρ : IsQRen (α := α) (Γ := Γ) (Δ := Δ) qΓ qΔ ρ)
  : Split Γ qΓ ρ Δ qΔl qΔr where
  qΓl := pvSum ρ qΔl
  qΓr := pvSum ρ qΔr
  hρl := of_pvSum _ _ qΔl
  hρr := of_pvSum _ _ qΔr
  hlr := split_pvSum hqs hρ

structure Vector'.Var (qs : Vector' EQuant n) (i : ℕ) : Prop where
  is_lt : i < n
  use : 1 ≤ qs.get ⟨i, is_lt⟩
  select : ∀j : Fin n, i ≠ j → 0 ≤ qs.get j

theorem Vector'.Var.zero_head {q : EQuant} {qs : Vector' EQuant n}
  (h : Var (qs.cons q) 0) : 1 ≤ q := h.use

theorem Vector'.Var.zero_tail {q : EQuant} {qs : Vector' EQuant n}
  (h : Var (qs.cons q) 0) : 0 ≤ qs
  := le_of_get_le (λi => by convert h.select (i + 1) (by simp) using 1 <;> simp)

theorem Vector'.Var.succ_head {q : EQuant} {qs : Vector' EQuant n}
  (h : Var (qs.cons q) (i + 1)) : 0 ≤ q
  := h.select 0 (by simp)

theorem Vector'.Var.succ_tail {q : EQuant} {qs : Vector' EQuant n}
  (h : Var (qs.cons q) (i + 1)) : Var qs i where
  is_lt := Nat.lt_of_succ_lt_succ h.is_lt
  use := h.use
  select := λj hj => by convert h.select (j + 1) (by simp [*]) using 1; simp

theorem Vector'.Var.of_oneHot_le {qs : Vector' EQuant n} {i : ℕ}
  (hi : i < n) (hv : Vector'.oneHot ⟨i, hi⟩ 1 ≤ qs) : Vector'.Var qs i where
  is_lt := hi
  use := by convert Vector'.get_le_of_le hv ⟨i, hi⟩; simp [oneHot]
  select j hj := by
    convert Vector'.get_le_of_le hv j; cases j; simp at hj; simp [oneHot, Ne.symm hj]

theorem Vector'.Var.oneHot_le {qs : Vector' EQuant n} {i : ℕ}
   (hv : Vector'.Var qs i) : Vector'.oneHot ⟨i, hv.is_lt⟩ 1 ≤ qs := by
  apply Vector'.le_of_get_le
  intro ⟨j, hj⟩
  simp only [oneHot, get_ofFn, Fin.mk.injEq, ge_iff_le]
  split
  case isTrue h => cases h; exact hv.use
  case isFalse h => exact hv.select _ (by simp [Ne.symm h])

theorem Vector'.Var.oneHot_le_iff {qs : Vector' EQuant n} {i : ℕ} (hi : i < n)
  : Vector'.Var qs i ↔ Vector'.oneHot ⟨i, hi⟩ 1 ≤ qs
  := ⟨Vector'.Var.oneHot_le, Vector'.Var.of_oneHot_le hi⟩

structure List.QVar (Γ : List α) (qs : Vector' EQuant Γ.length) (i) (A : α)
  extends qs.Var i : Prop where
  ty_eq : Γ[i] = A

theorem List.QVar.zero_head_ty {A} {Γ : List α} {q : EQuant} {qs : Vector' EQuant Γ.length}
  (h : QVar (A::Γ) (qs.cons q) 0 B) : A = B := h.ty_eq

theorem List.QVar.zero_head_quant {A} {Γ : List α} {q : EQuant} {qs : Vector' EQuant Γ.length}
  (h : QVar (A::Γ) (qs.cons q) 0 B) : 1 ≤ q := h.use

theorem List.QVar.zero_tail {A} {Γ : List α} {q : EQuant} {qs : Vector' EQuant Γ.length}
  (h : QVar (A::Γ) (qs.cons q) 0 B) : 0 ≤ qs := h.toVar.zero_tail

theorem List.QVar.succ_head {A} {Γ : List α} {q : EQuant} {qs : Vector' EQuant Γ.length}
  (h : QVar (A::Γ) (qs.cons q) (i + 1) B) : 0 ≤ q := h.toVar.succ_head

theorem List.QVar.succ_tail {A} {Γ : List α} {q : EQuant} {qs : Vector' EQuant Γ.length}
  (h : QVar (A::Γ) (qs.cons q) (i + 1) B) : QVar Γ qs i B where
  toVar := h.toVar.succ_tail
  ty_eq := h.ty_eq

theorem List.QVar.wk {Γ Δ : List α} {qΓ : Vector' EQuant Γ.length} {qΔ : Vector' EQuant Δ.length}
  {ρ : ℕ → ℕ} (hρ : List.IsQRen qΓ qΔ ρ)
  {i} {A} (v : QVar Δ qΔ i A) : QVar Γ qΓ (ρ i) A where
  toVar := Vector'.Var.of_oneHot_le (hρ.bounded_on i v.is_lt) (by
    convert (hρ.pvSum_mono v.oneHot_le).trans hρ.quant_le_sum
    simp only [Vector'.oneHot, pvSum, finVSum, finSum, Vector'.get_ofFn]
    congr
    funext j
    simp only [Fintype.preSum, Finset.sum_ite_eq', Finset.mem_preimageF_iff, toFin,
      Finset.mem_singleton]
    congr 1
    ext
    tauto
  )
  ty_eq := by rw [hρ.getElem_eq, v.ty_eq]

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

theorem List.IsRen.toNWkn (Γ Δ : List α) (ρ : ℕ → ℕ)
  (h : List.IsRen Γ Δ ρ) : List.NWkn Γ Δ ρ
  := λn hΔ => ⟨h.bounded_on n hΔ, le_of_eq (h.getElem_eq n hΔ)⟩

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
