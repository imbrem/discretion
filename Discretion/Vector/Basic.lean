import Mathlib.Logic.Function.Defs
import Mathlib.Data.Vector.Basic

inductive Vector' (α : Type) : Nat → Type
  | nil : Vector' α 0
  | cons {n : Nat} : α → Vector' α n → Vector' α (n+1)

namespace Vector'

def toList {α : Type} {n : Nat} : Vector' α n → List α
  | .nil => []
  | .cons a v => a :: v.toList

@[simp]
theorem toList_length {α : Type} {n : Nat} (v : Vector' α n) : v.toList.length = n
  := by induction v <;> simp [toList, *]

@[simp]
theorem toList_nil {α : Type} : (nil : Vector' α 0).toList = [] := rfl

@[simp]
theorem toList_cons {α : Type} {n : Nat} (a : α) (v : Vector' α n)
  : (cons a v).toList = a :: v.toList := rfl

theorem toList_injective {α : Type} {n : Nat} : Function.Injective (toList (α := α) (n := n))
  := λa b h => by
  induction a <;> cases b
  case nil => rfl
  case cons I _ _ =>
    simp only [toList_cons, List.cons.injEq] at h
    rw [h.1, I _ h.2]

theorem toList_inj {α : Type} {n : Nat} {a b : Vector' α n} : a.toList = b.toList ↔ a = b
  := ⟨λh => toList_injective h, λh => by rw [h]⟩

def head {α : Type} {n : Nat} : Vector' α (n+1) → α
  | (cons a _) => a

@[simp]
theorem head_cons {α : Type} {n : Nat} (a : α) (v : Vector' α n)
  : (cons a v).head = a := rfl

def tail {α : Type} {n : Nat} : Vector' α (n+1) → Vector' α n
  | (cons _ v) => v

@[simp]
theorem tail_cons {α : Type} {n : Nat} (a : α) (v : Vector' α n)
  : (cons a v).tail = v := rfl

@[simp]
theorem cons_head_tail {α : Type} {n : Nat} (v : Vector' α (n+1))
  : cons v.head v.tail = v := by cases v; rfl

def get {α : Type} {n : Nat} (v : Vector' α n) (i : Fin n) : α := match v with
  | .nil => i.elim0
  | .cons a v => i.cases a v.get

@[simp]
theorem get_zero {α : Type} {n : Nat} (v : Vector' α (n + 1))
  : v.get 0 = v.head := by cases v; rfl

@[simp]
theorem get_cons_zero {α : Type} {n : Nat} (a : α) (v : Vector' α n)
  : (cons a v).get 0 = a := rfl

@[simp]
theorem get_succ {α : Type} {n : Nat} (v : Vector' α (n + 1)) (i : Fin n)
  : v.get i.succ = v.tail.get i := by cases v; rfl

@[simp]
theorem get_cons_succ {α : Type} {n : Nat} (a : α) (v : Vector' α n) (i : Fin n)
  : (cons a v).get i.succ = v.get i := rfl

@[simp]
theorem get_cons_comp_succ {α : Type} {n : Nat} (a : α) (v : Vector' α n)
  : (cons a v).get ∘ Fin.succ = v.get := funext (get_succ (cons a v))

theorem get_injective {α : Type} {n : Nat} : Function.Injective (get (α := α) (n := n))
  := λa b h => by
  induction a <;> cases b
  case nil => rfl
  case cons I _ _ =>
    congr
    exact congrFun h 0
    apply I
    funext i
    exact congrFun h i.succ

theorem get_inj {α : Type} {n : Nat} {a b : Vector' α n} : a.get = b.get ↔ a = b
  := ⟨λh => get_injective h, λh => by rw [h]⟩

def ofFn {α : Type} {n : Nat} (f : Fin n → α) : Vector' α n := match n with
  | 0 => nil
  | _ + 1 => cons (f 0) (ofFn (f ∘ Fin.succ))

@[simp]
theorem ofFn_zero {α : Type} (f : Fin 0 → α) : ofFn f = nil := rfl

theorem ofFn_succ {α : Type} {n : Nat} (f : Fin (n + 1) → α)
  : ofFn f = cons (f 0) (ofFn (f ∘ Fin.succ)) := rfl

@[simp]
theorem ofFn_get {α : Type} {n : Nat} (v : Vector' α n)
  : ofFn v.get = v := by induction v <;> simp [ofFn_succ, *]

theorem get_ofFn_applied {α : Type} {n : Nat} (f : Fin n → α) (i : Fin n)
  : (ofFn f).get i = f i := by
  induction n with
  | zero => exact i.elim0
  | succ n I => cases i using Fin.cases <;> simp [ofFn_succ, I]

@[simp]
theorem get_ofFn {α : Type} {n : Nat} (f : Fin n → α)
  : (ofFn f).get = f := funext (get_ofFn_applied f)

def equivFin {α : Type} {n : Nat} : Vector' α n ≃ (Fin n → α) := ⟨get, ofFn, ofFn_get, get_ofFn⟩

inductive liftRel (R : α → α → Prop) : ∀{n}, Vector' α n → Vector' α n → Prop
  | nil : liftRel R nil nil
  | cons {n : Nat} {a b : α} {v w : Vector' α n} (h₁ : R a b) (h₂ : liftRel R v w)
    : liftRel R (cons a v) (cons b w)

def map {α β : Type} (f : α → β) {n : Nat} : Vector' α n → Vector' β n
  | nil => nil
  | cons a v => cons (f a) (map f v)

@[simp]
theorem map_zero {α β : Type} (f : α → β) (v : Vector' α 0) : map f v = nil := by cases v; rfl

@[simp]
theorem map_cons {α β : Type} (f : α → β) {n : Nat} (a : α) (v : Vector' α n)
  : map f (cons a v) = cons (f a) (map f v) := rfl

theorem map_succ {α β : Type} (f : α → β) {n : Nat} (v : Vector' α (n + 1))
  : map f v = cons (f v.head) (map f v.tail) := by cases v; rfl

theorem map_comp {α β γ : Type} (f : α → β) (g : β → γ) {n : Nat} (v : Vector' α n)
  : map (g ∘ f) v = map g (map f v) := by induction v <;> simp [*]

@[simp]
theorem map_id {α : Type} {n : Nat} (v : Vector' α n) : map id v = v := by induction v <;> simp [*]

theorem toList_map {α β : Type} (f : α → β) {n : Nat} (v : Vector' α n)
  : (map f v).toList = List.map f v.toList := by induction v <;> simp [*]

theorem get_map_applied {α β : Type} (f : α → β) {n : Nat} (v : Vector' α n) (i : Fin n)
  : (map f v).get i = f (v.get i) := by
  induction v with
  | nil => exact i.elim0
  | cons => cases i using Fin.cases <;> simp [*]

@[simp]
theorem get_map {α β : Type} (f : α → β) {n : Nat} (v : Vector' α n)
  : (map f v).get = f ∘ v.get := funext (get_map_applied f v)

-- TODO: Vector' is an applicative functor, but the parameters are in the wrong order!

def zipWith {α β γ : Type} (f : α → β → γ) {n : Nat} : Vector' α n → Vector' β n → Vector' γ n
  | nil, nil => nil
  | cons a v, cons b w => cons (f a b) (zipWith f v w)

@[simp]
theorem zipWith_zero {α β γ : Type} (f : α → β → γ) (v : Vector' α 0) (w : Vector' β 0)
  : zipWith f v w = nil := by cases v; cases w; rfl

@[simp]
theorem zipWith_cons {α β γ : Type}
  (f : α → β → γ) {n : Nat} (a : α) (v : Vector' α n) (b : β) (w : Vector' β n)
  : zipWith f (cons a v) (cons b w) = cons (f a b) (zipWith f v w) := rfl

theorem zipWith_succ {α β γ : Type}
  (f : α → β → γ) {n : Nat} (v : Vector' α (n + 1)) (w : Vector' β (n + 1))
  : zipWith f v w = cons (f v.head w.head) (zipWith f v.tail w.tail) := by cases v; cases w; rfl

theorem toList_zipWith {α β γ : Type} (f : α → β → γ) {n : Nat} (v : Vector' α n) (w : Vector' β n)
  : (zipWith f v w).toList = List.zipWith f v.toList w.toList
  := by induction v <;> cases w <;> simp [*]

@[simp]
theorem get_zipWith {α β γ : Type}
  (f : α → β → γ) {n : Nat} (v : Vector' α n) (w : Vector' β n) (i : Fin n)
  : (zipWith f v w).get i = f (v.get i) (w.get i) := by
  induction v <;> cases w
  case nil => exact i.elim0
  case cons => cases i using Fin.cases <;> simp [*]

instance instMax {α : Type} [Max α] : Max (Vector' α n) where
  max := zipWith (· ⊔ ·)

theorem get_sup_applied {α : Type} [Max α] {n : Nat} (v w : Vector' α n) (i : Fin n)
  : (v ⊔ w).get i = v.get i ⊔ w.get i := by simp [Max.max]

@[simp]
theorem get_sup {α : Type} [Max α] {n : Nat} (v w : Vector' α n) : (v ⊔ w).get = v.get ⊔ w.get
  := funext (get_sup_applied v w)

instance instMin {α : Type} [Min α] : Min (Vector' α n) where
  min := zipWith (· ⊓ ·)

theorem get_inf_applied {α : Type} [Min α] {n : Nat} (v w : Vector' α n) (i : Fin n)
  : (v ⊓ w).get i = v.get i ⊓ w.get i := by simp [Min.min]

@[simp]
theorem get_inf {α : Type} [Min α] {n : Nat} (v w : Vector' α n) : (v ⊓ w).get = v.get ⊓ w.get
  := funext (get_inf_applied v w)

instance instTop {α : Type} [Top α] : Top (Vector' α n) where
  top := ofFn ⊤

@[simp]
theorem ofFn_top {α : Type} [Top α] {n : Nat} : ofFn ⊤ = (⊤ : Vector' α n) := rfl

@[simp]
theorem get_top {α : Type} [Top α] {n : Nat} : (⊤ : Vector' α n).get = ⊤ := by simp [Top.top]

theorem get_top_applied {α : Type} [Top α] {n : Nat} (i : Fin n) : (⊤ : Vector' α n).get i = ⊤
  := by simp

instance instBot {α : Type} [Bot α] : Bot (Vector' α n) where
  bot := ofFn ⊥

@[simp]
theorem ofFn_bot {α : Type} [Bot α] {n : Nat} : ofFn ⊥ = (⊥ : Vector' α n) := rfl

@[simp]
theorem get_bot {α : Type} [Bot α] {n : Nat} : (⊥ : Vector' α n).get = ⊥ := by simp [Bot.bot]

theorem get_bot_applied {α : Type} [Bot α] {n : Nat} (i : Fin n) : (⊥ : Vector' α n).get i = ⊥
  := by simp

instance instAdd {α : Type} [Add α] : Add (Vector' α n) where
  add := zipWith (· + ·)

instance instSub {α : Type} [Sub α] : Sub (Vector' α n) where
  sub := zipWith (· - ·)

instance instMul {α : Type} [Mul α] : Mul (Vector' α n) where
  mul := zipWith (· * ·)

section LE

variable [LE α]

instance instLE : LE (Vector' α n) where
  le := liftRel (· ≤ ·)

@[simp]
theorem nil_le_nil : nil (α := α) ≤ nil := .nil

@[simp]
theorem cons_le_cons {a b : α} {v w : Vector' α n}
  : cons a v ≤ cons b w ↔ a ≤ b ∧ v ≤ w := ⟨λ|.cons h h' => ⟨h, h'⟩, λ⟨h, h'⟩ => .cons h h'⟩

theorem get_le_of_le {a b : Vector' α n} (h : a ≤ b) : a.get ≤ b.get := by
  induction h with
  | nil => exact λi => i.elim0
  | cons h₁ h₂ I =>
    intro i
    cases i using Fin.cases
    apply h₁
    apply I _

theorem le_of_get_le {a b : Vector' α n} (h : a.get ≤ b.get) : a ≤ b := by
  induction a <;> cases b
  case nil => exact .nil
  case cons I _ _ => exact .cons (h 0) (I (λi => h i.succ))

theorem get_le_iff {a b : Vector' α n} : a.get ≤ b.get ↔ a ≤ b := ⟨le_of_get_le, get_le_of_le⟩

@[elab_as_elim, induction_eliminator]
theorem le_inductionOn {motive : ∀{n} (a b : Vector' α n), a ≤ b → Prop}
  (nil : motive nil nil nil_le_nil)
  (cons : ∀{n} {a b : α} {v w : Vector' α n},
    (h : a ≤ b) → (h' : v ≤ w) → motive v w h' → motive (cons a v) (cons b w) (.cons h h')
  ) {n} {a b : Vector' α n} (h : a ≤ b) : motive a b h := by
  induction h <;> apply_assumption <;> assumption

@[elab_as_elim, cases_eliminator]
theorem le_casesOn {motive : ∀{n} (a b : Vector' α n), a ≤ b → Prop}
  (nil : motive nil nil nil_le_nil)
  (cons : ∀{n} {a b : α} {v w : Vector' α n},
    (h : a ≤ b) → (h' : v ≤ w) → motive (cons a v) (cons b w) (.cons h h')
  ) {n} {a b : Vector' α n} (h : a ≤ b) : motive a b h := by
  cases h <;> apply_assumption <;> assumption

instance instOrderTop [OrderTop α] : OrderTop (Vector' α n) where
  le_top a := le_of_get_le (by simp)

instance instOrderBot  [OrderBot α] : OrderBot (Vector' α n) where
  bot_le a := le_of_get_le (by simp)

instance instBoundedOrder [BoundedOrder α] : BoundedOrder (Vector' α n) where

end LE

instance instPreorder {α : Type} [Preorder α] : Preorder (Vector' α n) where
  le_refl v := by induction v <;> simp [*]
  le_trans _ _ _ h h' := by
    induction h <;> cases h'
    case nil => exact nil_le_nil
    case cons h _ I _ _ h' hv => exact .cons (le_trans h h') (I _ hv)

instance instPartialOrder {α : Type} [PartialOrder α] : PartialOrder (Vector' α n) where
  le_antisymm _ _ h h' := by
    induction h <;> cases h'
    case nil => rfl
    case cons h _ I h' hv => rw [le_antisymm h h', I hv]

instance instSemilatticeSup {α : Type} [SemilatticeSup α] : SemilatticeSup (Vector' α n) where
  sup := (· ⊔ ·)
  le_sup_left a b := le_of_get_le (by simp)
  le_sup_right a b := le_of_get_le (by simp)
  sup_le a b c := by simp only [<-get_le_iff]; aesop

instance instSemilatticeInf {α : Type} [SemilatticeInf α] : SemilatticeInf (Vector' α n) where
  inf := (· ⊓ ·)
  inf_le_left a b := le_of_get_le (by simp)
  inf_le_right a b := le_of_get_le (by simp)
  le_inf a b c := by simp only [<-get_le_iff]; aesop

instance instLattice {α : Type} [Lattice α] : Lattice (Vector' α n) where
  inf := (· ⊓ ·)
  inf_le_left a b := le_of_get_le (by simp)
  inf_le_right a b := le_of_get_le (by simp)
  le_inf a b c := by simp only [<-get_le_iff]; aesop

instance instDistribLattice {α : Type} [DistribLattice α] : DistribLattice (Vector' α n) where
  le_sup_inf a b c := by
    simp only [← get_le_iff, get_inf, get_sup]
    apply le_sup_inf

instance instSDiff {α : Type} [SDiff α] : SDiff (Vector' α n) where
  sdiff := zipWith (· \ ·)

@[simp]
theorem get_sdiff {α : Type} [SDiff α] {n : Nat} (v w : Vector' α n)
  : (v \ w).get = v.get \ w.get := by funext i; simp [SDiff.sdiff]

instance instHasCompl {α : Type} [HasCompl α] : HasCompl (Vector' α n) where
  compl := map compl

@[simp]
theorem get_compl {α : Type} [HasCompl α] {n : Nat} (v : Vector' α n)
  : (vᶜ).get = v.getᶜ := by funext i; simp [HasCompl.compl]

instance instHImp {α : Type} [HImp α] : HImp (Vector' α n) where
  himp := zipWith (· ⇨ ·)

@[simp]
theorem get_himp {α : Type} [HImp α] {n : Nat} (v w : Vector' α n)
  : (v ⇨ w).get = v.get ⇨ w.get := by funext i; simp [HImp.himp]

-- TODO: generalized boolean algebra for extra points?

instance instBooleanAlgebra {α : Type} [BooleanAlgebra α] : BooleanAlgebra (Vector' α n) where
  inf_compl_le_bot x := le_of_get_le (by simp)
  top_le_sup_compl x := le_of_get_le (by simp)
  le_top := by simp
  bot_le := by simp
  sdiff_eq a b := get_injective (by simp [BooleanAlgebra.sdiff_eq])
  himp_eq a b := get_injective (by simp [BooleanAlgebra.himp_eq])

end Vector'
