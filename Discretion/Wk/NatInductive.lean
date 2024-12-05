import Discretion.Wk.Fin
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
def Nat.Wk.ix {n m} : Nat.Wk n m -> Fin m → Fin n
  | .nil => _root_.id
  | .step ρ => Fin.stepWk (ix ρ)
  | .lift ρ => Fin.liftWk (ix ρ)

@[simp]
def Nat.Wk.pv {n m} : Nat.Wk n m → Vector' α n → Vector' α m
  | .nil, v => .nil
  | .step ρ, .cons h v => ρ.pv v
  | .lift ρ, .cons h v => .cons h (ρ.pv v)

abbrev Vector'.wk {n m} (v : Vector' α n) (ρ : Nat.Wk n m) : Vector' α m := ρ.pv v

@[simp]
theorem Nat.Wk.ix_id {n} : ix (id n) = _root_.id := by
  induction n <;> simp [id, ix, Fin.liftWk_id, *]

theorem Nat.Wk.ix_drop {n} : ix (drop n) = Fin.elim0 := funext (λi => i.elim0)

theorem Nat.Wk.ix_injective {n m} : Function.Injective (@ix n m) := λρ σ h => by induction ρ with
  | nil => cases σ; rfl
  | step _ I => cases σ with
    | step =>
      simp only [ix, Fin.stepWk_inj] at h
      rw [I _ h]
    | lift => simp at h
  | lift _ I => cases σ with
    | step => simp at h
    | lift =>
      simp only [ix, Fin.liftWk_inj] at h
      rw [I _ h]

theorem Nat.Wk.ix_inj {n m} {ρ σ : Nat.Wk n m} : ix ρ = ix σ ↔ ρ = σ
  := ⟨λh => ix_injective h, λh => by cases h; rfl⟩

@[simp]
theorem Nat.Wk.pv_id {n} (v : Vector' α n) : (id n).pv v = v := by induction v <;> simp [*]

@[simp]
theorem Nat.Wk.get_pv {n m} (ρ : Nat.Wk n m) (v : Vector' α n) (i : Fin m)
  : (ρ.pv v).get i = v.get (ρ.ix i) := by induction ρ with
  | nil => exact i.elim0
  | step _ I => cases v; simp [I]
  | lift _ I => cases v; cases i using Fin.cases <;> simp [I]

@[simp]
theorem Nat.Wk.pv_ofFn {n m} (ρ : Nat.Wk n m) (f : Fin n -> α) :
  (ρ.pv (Vector'.ofFn f)) = Vector'.ofFn (f ∘ ρ.ix) := by
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

theorem Nat.Wk.ix_id' {n} (ρ : Nat.Wk n n) : ix ρ = _root_.id := by simp

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

theorem Nat.Split.le {n m k} (ρ : Nat.Split n m k) : m ⊔ k ≤ n := by simp [ρ.lwk.le, ρ.rwk.le]

def Nat.Split.symm {n m k} (ρ : Nat.Split n m k) : Nat.Split n k m
  := ⟨ρ.rwk, ρ.lwk⟩

@[match_pattern]
def Nat.Split.nil : Nat.Split 0 0 0 := ⟨Wk.nil, Wk.nil⟩

@[match_pattern]
def Nat.Split.left {n m k} (ρ : Nat.Split n m k) : Nat.Split (n + 1) (m + 1) k
  := ⟨ρ.lwk.lift, ρ.rwk.step⟩

@[match_pattern]
def Nat.Split.right {n m k} (ρ : Nat.Split n m k) : Nat.Split (n + 1) m (k + 1)
  := ⟨ρ.lwk.step, ρ.rwk.lift⟩

@[match_pattern]
def Nat.Split.both {n m k} (ρ : Nat.Split n m k) : Nat.Split (n + 1) (m + 1) (k + 1)
  := ⟨ρ.lwk.lift, ρ.rwk.lift⟩

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
