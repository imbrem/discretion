import Discretion.Wk.Fin
import Discretion.Wk.Quant
import Discretion.Vector.Basic

inductive Nat.Wk : Nat → Nat → Type
  | nil : Wk 0 0
  | step {n m} : Wk n m -> Wk (n + 1) m
  | lift {n m} : Wk n m -> Wk (n + 1) (m + 1)

def Nat.Wk.id : ∀n, Wk n n
  | 0 => .nil
  | n + 1 => (id n).lift

def Nat.Wk.drop : ∀n, Wk n 0
  | 0 => .nil
  | n + 1 => (drop n).step

@[simp]
def Nat.Wk.comp {n m k} : Nat.Wk n m → Nat.Wk m k → Nat.Wk n k
  | .nil, .nil => .nil
  | .step ρ, σ | .lift ρ, .step σ => .step (ρ.comp σ)
  | .lift ρ, .lift σ => .lift (ρ.comp σ)

@[simp]
def Nat.Wk.ix {n m} : Nat.Wk n m -> ℕ → ℕ
  | .nil => _root_.id
  | .step ρ => Nat.stepWk (ix ρ)
  | .lift ρ => Nat.liftWk (ix ρ)

@[simp]
def Nat.Wk.ixf {n m} : Nat.Wk n m -> Fin m → Fin n
  | .nil => _root_.id
  | .step ρ => Fin.stepWk (ixf ρ)
  | .lift ρ => Fin.liftWk (ixf ρ)

@[simp]
def Nat.Wk.pv {n m} : Nat.Wk n m → Vector' α n → Vector' α m
  | .nil, v => .nil
  | .step ρ, .cons h v => ρ.pv v
  | .lift ρ, .cons h v => .cons h (ρ.pv v)

abbrev Vector'.wk {n m} (v : Vector' α n) (ρ : Nat.Wk n m) : Vector' α m := ρ.pv v

@[simp]
theorem Nat.Wk.ix_id {n} : ix (id n) = _root_.id := by
  induction n <;> simp [id, ix, *]

@[simp]
theorem Nat.Wk.ixf_id {n} : ixf (id n) = _root_.id := by
  induction n <;> simp [id, ixf, *]

@[simp]
theorem Nat.Wk.ixf_comp {n m k} (ρ : Nat.Wk n m) (σ : Nat.Wk m k) : ixf (ρ.comp σ) = ixf ρ ∘ ixf σ := by
  induction ρ generalizing k <;> cases σ <;> funext i
  case lift.lift => cases i using Fin.cases <;> simp [*]
  all_goals simp [*]

theorem Nat.Wk.ixf_drop {n} : ixf (drop n) = Fin.elim0 := funext (λi => i.elim0)

theorem Nat.Wk.ixf_injective {n m} : Function.Injective (@ixf n m) := λρ σ h => by induction ρ with
  | nil => cases σ; rfl
  | step _ I => cases σ with
    | step =>
      simp only [ixf, Fin.stepWk_inj] at h
      rw [I _ h]
    | lift => simp at h
  | lift _ I => cases σ with
    | step => simp at h
    | lift =>
      simp only [ixf, Fin.liftWk_inj] at h
      rw [I _ h]

@[simp]
theorem Nat.Wk.ixf_apply_injective {n m} (ρ : Wk n m) : Function.Injective (ixf ρ) := by
  induction ρ with
  | nil => exact (λi => i.elim0)
  | step ρ I => exact Fin.stepWk_apply_injective I
  | lift ρ I => exact Fin.liftWk_apply_injective I

@[simp]
theorem Nat.Wk.comp_id {n m} (ρ : Nat.Wk n m) : ρ.comp (id m) = ρ := by apply ixf_injective; simp

@[simp]
theorem Nat.Wk.id_comp {n m} (ρ : Nat.Wk n m) : (id n).comp ρ = ρ := by apply ixf_injective; simp

theorem Nat.Wk.comp_assoc {n m k l} (ρ : Nat.Wk n m) (σ : Nat.Wk m k) (τ : Nat.Wk k l)
  : (ρ.comp σ).comp τ = ρ.comp (σ.comp τ) := by apply ixf_injective; simp [Function.comp_assoc]

theorem Nat.Wk.ixf_inj {n m} {ρ σ : Nat.Wk n m} : ixf ρ = ixf σ ↔ ρ = σ
  := ⟨λh => ixf_injective h, λh => by cases h; rfl⟩

@[simp]
theorem Nat.Wk.pv_id {n} (v : Vector' α n) : (id n).pv v = v := by induction v <;> simp [*]

@[simp]
theorem Nat.Wk.get_pv {n m} (ρ : Nat.Wk n m) (v : Vector' α n) (i : Fin m)
  : (ρ.pv v).get i = v.get (ρ.ixf i) := by induction ρ with
  | nil => exact i.elim0
  | step _ I => cases v; simp [I]
  | lift _ I => cases v; cases i using Fin.cases <;> simp [I]

@[simp]
theorem Nat.Wk.pv_ofFn {n m} (ρ : Nat.Wk n m) (f : Fin n -> α) :
  (ρ.pv (Vector'.ofFn f)) = Vector'.ofFn (f ∘ ρ.ixf) := by
  apply Vector'.get_injective
  funext i
  simp

theorem Nat.Wk.pv_rel_of_rel {n m} (ρ : Nat.Wk n m) {v w : Vector' α n} (hv : v.liftRel R w)
  : (ρ.pv v).liftRel R (ρ.pv w) := by induction ρ with
  | nil => constructor
  | step ρ I => cases v; cases w; exact I hv.tail
  | lift ρ I => cases v; cases w; exact (I hv.tail).cons hv.head

theorem Nat.Wk.pv_le_of_le [LE α] {n m} (ρ : Nat.Wk n m) {v w : Vector' α n} (hv : v ≤ w)
  : ρ.pv v ≤ ρ.pv w := ρ.pv_rel_of_rel hv

theorem Nat.Wk.le {n m} (ρ : Nat.Wk n m) : m ≤ n := by induction ρ <;> omega

def Nat.Wk.inductionId {motive : ∀{n}, Wk n n → Sort u}
  (nil : motive .nil)
  (lift : ∀{n} (ρ : Wk n n), motive ρ → motive (ρ.lift))
  {n} : ∀ (ρ : Wk n n), motive ρ
  | .nil => nil
  | .lift ρ => lift ρ (inductionId nil lift ρ)
  | .step ρ => have _ := ρ.le; by omega

def Nat.Wk.casesId {motive : ∀{n}, Wk n n → Sort u}
  (nil : motive .nil)
  (lift : ∀{n} (ρ : Wk n n), motive (ρ.lift))
  {n} : ∀ (ρ : Wk n n), motive ρ
  | .nil => nil
  | .lift ρ => lift ρ
  | .step ρ => have _ := ρ.le; by omega

@[simp]
theorem Nat.Wk.eq_id {n} (ρ : Nat.Wk n n) : ρ = id n
  := by induction ρ using inductionId <;> simp [id, *]

theorem Nat.Wk.ixf_id' {n} (ρ : Nat.Wk n n) : ixf ρ = _root_.id := by simp

instance Nat.Wk.idSubsingleton {n} : Subsingleton (Wk n n) := ⟨λ_ _ => by simp⟩

instance Nat.Wk.idInhabited {n} : Inhabited (Wk n n) := ⟨id n⟩

@[simp]
theorem Nat.Wk.eq_drop {n} : ∀(ρ : Nat.Wk n 0), ρ = drop n
  | .nil => rfl
  | .step ρ => by simp [drop, ρ.eq_drop]

instance Nat.Wk.dropSubsingleton {n} : Subsingleton (Wk n 0) := ⟨λ_ _ => by simp⟩

instance Nat.Wk.dropInhabited {n} : Inhabited (Wk n 0) := ⟨drop n⟩

def Nat.Split (n m k : ℕ):= Wk n m × Wk n k

abbrev Nat.Split.lwk {n m k} (ρ : Nat.Split n m k) : Wk n m := ρ.1

abbrev Nat.Split.rwk {n m k} (ρ : Nat.Split n m k) : Wk n k := ρ.2

def Nat.Split.wkIn {i n m k} (ρ : Wk i n) (σ : Nat.Split n m k) : Split i m k
  := ⟨ρ.comp σ.lwk, ρ.comp σ.rwk⟩

def Nat.Split.wkOut {n m k m' k'}
  (ρ : Nat.Split n m k) (σl : Wk m m') (σr : Wk k k') : Split n m' k'
  := ⟨ρ.lwk.comp σl, ρ.rwk.comp σr⟩

-- TODO: wkIn_wkOut = wkOut_wkIn

theorem Nat.Split.le {n m k} (ρ : Nat.Split n m k) : m ⊔ k ≤ n := by simp [ρ.lwk.le, ρ.rwk.le]

def Nat.Split.symm {n m k} (ρ : Nat.Split n m k) : Nat.Split n k m
  := ⟨ρ.rwk, ρ.lwk⟩

@[simp]
theorem Nat.Split.symm_pair {n m k} (ρ : Nat.Wk n m) (σ : Nat.Wk n k)
  : symm (ρ, σ) = (σ, ρ) := rfl

@[match_pattern]
def Nat.Split.nil : Nat.Split 0 0 0 := ⟨Wk.nil, Wk.nil⟩

@[match_pattern]
def Nat.Split.both {n m k} (ρ : Nat.Split n m k) : Nat.Split (n + 1) (m + 1) (k + 1)
  := ⟨ρ.lwk.lift, ρ.rwk.lift⟩

@[match_pattern]
def Nat.Split.left {n m k} (ρ : Nat.Split n m k) : Nat.Split (n + 1) (m + 1) k
  := ⟨ρ.lwk.lift, ρ.rwk.step⟩

@[match_pattern]
def Nat.Split.right {n m k} (ρ : Nat.Split n m k) : Nat.Split (n + 1) m (k + 1)
  := ⟨ρ.lwk.step, ρ.rwk.lift⟩

@[match_pattern]
def Nat.Split.skip {n m k} (ρ : Nat.Split n m k) : Nat.Split (n + 1) m k
  := ⟨ρ.lwk.step, ρ.rwk.step⟩

@[simp]
theorem Nat.Split.symm_nil : Nat.Split.symm nil = nil := rfl

@[simp]
theorem Nat.Split.symm_left {n m k} (ρ : Nat.Split n m k)
  : Nat.Split.symm (left ρ) = right (symm ρ) := rfl

@[simp]
theorem Nat.Split.symm_right {n m k} (ρ : Nat.Split n m k)
  : Nat.Split.symm (right ρ) = left (symm ρ) := rfl

@[simp]
theorem Nat.Split.symm_both {n m k} (ρ : Nat.Split n m k)
  : Nat.Split.symm (both ρ) = both (symm ρ) := rfl

@[simp]
theorem Nat.Split.symm_symm {n m k} (ρ : Nat.Split n m k)
  : Nat.Split.symm (symm ρ) = ρ := rfl

@[elab_as_elim, induction_eliminator]
def Nat.Split.induction {motive : ∀{n m k}, Nat.Split n m k → Sort u}
  (nil : motive nil)
  (both : ∀{n m k} (ρ : Nat.Split n m k), motive ρ → motive (both ρ))
  (left : ∀{n m k} (ρ : Nat.Split n m k), motive ρ → motive (left ρ))
  (right : ∀{n m k} (ρ : Nat.Split n m k), motive ρ → motive (right ρ))
  (skip : ∀{n m k} (ρ : Nat.Split n m k), motive ρ → motive (skip ρ))
  : ∀{n m k} (ρ : Nat.Split n m k), motive ρ
  | _, _, _, .nil => nil
  | _, _, _, ⟨.lift ρ, .lift σ⟩ => both (ρ, σ) (induction nil both left right skip (ρ, σ))
  | _, _, _, ⟨.lift ρ, .step σ⟩ => left (ρ, σ) (induction nil both left right skip (ρ, σ))
  | _, _, _, ⟨.step ρ, .lift σ⟩ => right (ρ, σ) (induction nil both left right skip (ρ, σ))
  | _, _, _, ⟨.step ρ, .step σ⟩ => skip (ρ, σ) (induction nil both left right skip (ρ, σ))

def Nat.Split.cases' {motive : ∀{n m k}, Nat.Split n m k → Sort u}
  (nil : motive nil)
  (both : ∀{n m k} (ρ : Nat.Split n m k), motive (both ρ))
  (left : ∀{n m k} (ρ : Nat.Split n m k), motive (left ρ))
  (right : ∀{n m k} (ρ : Nat.Split n m k), motive (right ρ))
  (skip : ∀{n m k} (ρ : Nat.Split n m k), motive (skip ρ))
  : ∀{n m k} (ρ : Nat.Split n m k), motive ρ
  | _, _, _, .nil => nil
  | _, _, _, ⟨.lift ρ, .lift σ⟩ => both (ρ, σ)
  | _, _, _, ⟨.lift ρ, .step σ⟩ => left (ρ, σ)
  | _, _, _, ⟨.step ρ, .lift σ⟩ => right (ρ, σ)
  | _, _, _, ⟨.step ρ, .step σ⟩ => skip (ρ, σ)

abbrev Nat.Wk.sb (ρ : Wk n m) : Nat.Split n m m := ⟨ρ, ρ⟩

abbrev Nat.Wk.sl (ρ : Wk n m) : Nat.Split n m 0 := ⟨ρ, Wk.drop n⟩

abbrev Nat.Wk.sr (ρ : Wk n m) : Nat.Split n 0 m := ⟨Wk.drop n, ρ⟩

instance Nat.Split.bidSubsingleton {n} : Subsingleton (Nat.Split n n n)
  := (inferInstance : Subsingleton (Wk n n × Wk n n))

instance Nat.Split.bidInhabited {n} : Inhabited (Nat.Split n n n) := ⟨(Wk.id n).sb⟩

instance Nat.Split.lidSubsingleton {n} : Subsingleton (Nat.Split n n 0)
  := (inferInstance : Subsingleton (Wk n n × Wk n 0))

instance Nat.Split.lidInhabited {n} : Inhabited (Nat.Split n n 0) := ⟨(Wk.id n).sl⟩

instance Nat.Split.ridSubsingleton {n} : Subsingleton (Nat.Split n 0 n)
  := (inferInstance : Subsingleton (Wk n 0 × Wk n n))

instance Nat.Split.ridInhabited {n} : Inhabited (Nat.Split n 0 n) := ⟨(Wk.id n).sr⟩

def Nat.Wk.ixfu {n m} : Nat.Wk n m → Fin n → Bool
  | .nil => Fin.elim0
  | .step ρ => Fin.cases false ρ.ixfu
  | .lift ρ => Fin.cases true ρ.ixfu

inductive Nat.Wk.uv : ∀{n m}, (bs : Vector' Bool n) → Wk n m → Prop
  | nil : uv .nil .nil
  | step {n m} {bs : Vector' Bool n} {ρ : Wk n m} : uv bs ρ -> uv (bs.cons false) (ρ.step)
  | lift {n m} {bs : Vector' Bool n} {ρ : Wk n m} : uv bs ρ -> uv (bs.cons true) (ρ.lift)

inductive Nat.Split.Strict : ∀{n m k}, Nat.Split n m k → Prop
  | nil : Strict .nil
  | left {n m k} {ρ : Nat.Split n m k} : Strict ρ -> Strict (ρ.left)
  | right {n m k} {ρ : Nat.Split n m k} : Strict ρ -> Strict (ρ.right)

attribute [simp] Nat.Split.Strict.nil Nat.Split.Strict.left Nat.Split.Strict.right

theorem Nat.Split.Strict.add_eq {n m k} {ρ : Split n m k} (h : Strict ρ) : m + k = n
  := by induction h <;> omega

@[simp]
theorem Nat.Split.Strict.symm {n m k} {ρ : Nat.Split n m k} (h : Strict ρ) : Strict ρ.symm
  := by induction h <;> simp [*]

inductive Nat.Split.Wf : ∀{n m k}, Nat.Split n m k → Vector' Quant n → Prop
  | nil : Wf .nil .nil
  | both {n m k} {ρ : Nat.Split n m k} {q : Quant} {qs}
    : q.is_copy → Wf ρ qs -> Wf (ρ.both) (qs.cons q)
  | left {n m k} {ρ : Nat.Split n m k} {q : Quant} {qs}
    : Wf ρ qs  -> Wf (ρ.left) (qs.cons q)
  | right {n m k} {ρ : Nat.Split n m k} {q : Quant} {qs}
    : Wf ρ qs -> Wf (ρ.right) (qs.cons q)
  | skip {n m k} {ρ : Nat.Split n m k} {q : Quant} {qs}
    : q.is_del → Wf ρ qs -> Wf (ρ.left) (qs.cons q)

theorem Nat.Split.Strict.wf
  {n m k} {ρ : Nat.Split n m k} {qs : Vector' Quant n} (h : Strict ρ) : Wf ρ qs
  := by induction h <;> cases qs <;> constructor <;> apply_assumption
