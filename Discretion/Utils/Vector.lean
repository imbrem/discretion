import Mathlib.Data.Vector.Basic
import Mathlib.Data.Vector.Zip
import Mathlib.Order.Hom.Basic

namespace Mathlib.Vector

theorem get_ofFn' (f : Fin n → α) : (ofFn f).get = f := funext (get_ofFn f)

theorem ext_getElem (a b : Vector α n) (h : ∀(i : ℕ) (h : i < n), a[i] = b[i]) : a = b
  := Vector.eq a b (List.ext_getElem (by simp) (λi hi _ => h i (by convert hi; simp)))

theorem ext_getElem_fin (a b : Vector α n) (h : ∀(i : Fin n), a[i] = b[i]) : a = b
  := ext_getElem a b (λi hi => h ⟨i, hi⟩)

theorem ext_get (a b : Vector α n) (h : a.get = b.get) : a = b := ext_getElem_fin a b (congrFun h)

theorem getElem_eq_getElem_fin (a : Vector α n) (i : Fin n)
  : a[i] = a.toList[i] := a.get_eq_get i

theorem toList_head {a : Vector α (n + 1)}
  : a.toList.head (List.ne_nil_of_length_eq_add_one a.toList_length) = a.head := by
  cases a with | mk a h => cases a with
  | nil => cases h
  | cons => rfl

theorem toList_tail {a : Vector α (n + 1)}
  : a.toList.tail = a.tail.toList := by
  cases a with | mk a h => cases a with
  | nil => cases h
  | cons => rfl

theorem getElem_tail_succ (a : Vector α (n + 1)) (i : ℕ) {h : i < n}
  : a.tail[i] = a.toList.tail[i]'(by simpa) := by
  cases a with | mk a h => cases a with
  | nil => cases h
  | cons => rfl

theorem getElem_tail_succ_fin (a : Vector α (n + 1)) (i : Fin n)
  : a.tail[i] = a[i.succ] := by
  convert getElem_tail_succ (a := a) (i := i) (h := by simp)
  simp [getElem_def]

theorem getElem_tail_succ_fin' (a : Vector α (n + 1)) (i : Fin (n + 1 - 1))
  : a.tail[i] = a[i.succ] := getElem_tail_succ_fin a i

theorem head_eq_head {a : Vector α (n + 1)}
  : a.head = a.toList.head (List.ne_nil_of_length_eq_add_one a.toList_length) := by
  cases a with | mk a h => cases a with
  | nil => cases h
  | cons => rfl

theorem head_eq_getElem_zero {a : Vector α (n + 1)}
  : a.head = a[0] := by
  cases a with | mk a h => cases a with
  | nil => cases h
  | cons => rfl

section LE

variable [LE α]

instance instLE : LE (Vector α n) where
  le a b := ∀i : Fin n, a[i] ≤ b[i]

@[simp]
theorem nil_le : nil (α := α) ≤ nil := λi => i.elim0

@[simp]
theorem head_le {a b : Vector α (n + 1)} (h : a ≤ b) : a.head ≤ b.head := by
  cases a with | mk a p => cases a with | nil => cases p | _ =>
  cases b with | mk b p => cases b with | nil => cases p | _ =>
  exact h 0

@[simp]
theorem tail_le {a b : Vector α n} (h : a ≤ b) : tail a ≤ tail b := by cases n with
  | zero => simp [Vector.eq_nil]
  | succ n =>
    intro i; convert h i.succ using 1 <;> rw [getElem_tail_succ_fin'] <;> rfl

theorem cons_le {a b : Vector α n} {x y : α} (h₁ : x ≤ y) (h₂ : a ≤ b)
  : x ::ᵥ a ≤ y ::ᵥ b := λi => i.cases h₁ h₂

@[simp]
theorem cons_le_iff {a b : Vector α n} {x y : α}
  : x ::ᵥ a ≤ y ::ᵥ b ↔ x ≤ y ∧ a ≤ b := ⟨λh => ⟨head_le h, tail_le h⟩, λh => cons_le h.1 h.2⟩

theorem inductionOn_le {motive : ∀{n} (a b : Vector α n), a ≤ b → Prop}
  (nil : motive Vector.nil Vector.nil nil_le)
  (cons : ∀{n} (x y : α) (a b : Vector α n),
    (h : x ≤ y) → (h' : a ≤ b) → motive a b h' → motive (x ::ᵥ a) (y ::ᵥ b) (cons_le h h')
  ) {n} {a b : Vector α n} (h : a ≤ b) : motive a b h := by cases a, b using casesOn₂ with
  | nil => exact nil
  | cons x y xs ys =>
    exact cons x y xs ys (head_le h) (tail_le h) (inductionOn_le nil cons (tail_le h))

theorem casesOn_le {motive : ∀{n} (a b : Vector α n), a ≤ b → Prop}
  (nil : motive Vector.nil Vector.nil nil_le)
  (cons : ∀{n} (x y : α) (a b : Vector α n),
    (h : x ≤ y) → (h' : a ≤ b) → motive (x ::ᵥ a) (y ::ᵥ b) (cons_le h h')
  ) {n} {a b : Vector α n} (h : a ≤ b) : motive a b h := by cases a, b using casesOn₂ with
  | nil => exact nil
  | cons x y xs ys =>
    exact cons x y xs ys (head_le h) (tail_le h)

end LE

section Preorder

variable [Preorder α]

instance instPreorder : Preorder (Vector α n) where
  le_refl a i := le_refl a[i]
  le_trans a b c h h' i := le_trans (h i) (h' i)

theorem get_mono : Monotone (Vector.get (α := α) (n := n)) := λ_ _ h => h

theorem get_le_iff (a b : Vector α n) : a.get ≤ b.get ↔ a ≤ b := Iff.rfl

theorem ofFn_mono : Monotone (ofFn (α := α) (n := n)) := λf g h i => by simp [getElem_def, h i]

theorem get_strict_mono : StrictMono (Vector.get (α := α) (n := n)) := λa b => by
  simp only [lt_iff_le_not_le]
  intro ⟨h, h'⟩
  constructor
  exact h
  intro h
  apply h'
  convert ofFn_mono h <;> simp

theorem ofFn_strict_mono : StrictMono (ofFn (α := α) (n := n)) := λf g => by
  simp only [lt_iff_le_not_le]
  intro ⟨h, h'⟩
  constructor
  exact (ofFn_mono h)
  intro h
  apply h'
  convert get_mono h <;> simp [get_ofFn']

def orderIsoFin : Vector α n ≃o (Fin n → α) where
  toEquiv := Equiv.vectorEquivFin α n
  map_rel_iff' := get_le_iff _ _

end Preorder

instance instPartialOrder [PartialOrder α] : PartialOrder (Vector α n) where
  le_antisymm a b h h' := ext_getElem_fin a b (λi => le_antisymm (h i) (h' i))

def max [Max α] (a b : Vector α n) : Vector α n := a.zipWith (· ⊔ ·) b

def min [Min α] (a b : Vector α n) : Vector α n := a.zipWith (· ⊓ ·) b

instance instMax [Max α] : Max (Vector α n) where max := max

instance instMin [Min α] : Min (Vector α n) where min := min

@[simp]
theorem max_nil [Max α] : (nil (α := α)) ⊔ nil = nil := rfl

@[simp]
theorem max_cons [Max α] {x y : α} {xs ys : Vector α n}
  : (x ::ᵥ xs) ⊔ (y ::ᵥ ys) = (x ⊔ y) ::ᵥ xs ⊔ ys := rfl

@[simp]
theorem min_nil [Min α] : (nil (α := α)) ⊓ nil = nil := rfl

@[simp]
theorem min_cons [Min α] {x y : α} {xs ys : Vector α n}
  : (x ::ᵥ xs) ⊓ (y ::ᵥ ys) = (x ⊓ y) ::ᵥ xs ⊓ ys := rfl

@[simp]
theorem getElem_max [Max α] (a b : Vector α n) (i : ℕ) {h : i < n}
  : (a ⊔ b)[i] = a[i] ⊔ b[i] := by simp [Max.max, max, getElem_def]

@[simp]
theorem getElem_min [Min α] (a b : Vector α n) (i : ℕ) {h : i < n}
  : (a ⊓ b)[i] = a[i] ⊓ b[i] := by simp [Min.min, min, getElem_def]

instance instTop [Top α] : Top (Vector α n) where
  top := ofFn ⊤

instance instBot [Bot α] : Bot (Vector α n) where
  bot := ofFn ⊥

@[simp]
theorem getElem_top [Top α] (i : ℕ) {h : i < n} : (⊤ : Vector α n)[i] = ⊤
  := by simp [Top.top, getElem_def]

theorem getElem_top' [Top α] (i : Fin n) : (⊤ : Vector α n)[i] = ⊤
  := by simp [Top.top, getElem_def]

@[simp]
theorem getElem_bot [Bot α] (i : ℕ) {h : i < n} : (⊥ : Vector α n)[i] = ⊥
  := by simp [Bot.bot, getElem_def]

theorem getElem_bot' [Bot α] (i : Fin n) : (⊥ : Vector α n)[i] = ⊥
  := by simp [Bot.bot, getElem_def]

instance instOrderTop [LE α] [OrderTop α] : OrderTop (Vector α n) where
  le_top := λa i => by convert le_top (a := a[i]); simp

instance instOrderBot [LE α] [OrderBot α] : OrderBot (Vector α n) where
  bot_le := λa i => by convert bot_le (a := a[i]); simp

instance instBoundedOrder [LE α] [BoundedOrder α] : BoundedOrder (Vector α n) where

instance instSemilatticeSup [SemilatticeSup α] : SemilatticeSup (Vector α n) where
  sup := (· ⊔ ·)
  le_sup_left a b i := by simp
  le_sup_right a b i := by simp
  sup_le a b c ha hb i := by
    simp only [Fin.getElem_fin, getElem_max, sup_le_iff]
    exact ⟨ha i, hb i⟩

instance instSemilatticeInf [SemilatticeInf α] : SemilatticeInf (Vector α n) where
  inf := (· ⊓ ·)
  inf_le_left a b i := by simp
  inf_le_right a b i := by simp
  le_inf a b c ha hb i := by
    simp only [Fin.getElem_fin, getElem_min, le_inf_iff]
    exact ⟨ha i, hb i⟩

instance instLattice [Lattice α] : Lattice (Vector α n) where
  toSemilatticeSup := inferInstance
  inf := (· ⊓ ·)
  inf_le_left a b i := by simp
  inf_le_right a b i := by simp
  le_inf a b c ha hb i := by
    simp only [Fin.getElem_fin, getElem_min, le_inf_iff]
    exact ⟨ha i, hb i⟩

-- TODO: ye olde Complete/Distributive/Boolean lattice, and friends
