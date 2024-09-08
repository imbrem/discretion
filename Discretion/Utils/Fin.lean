import Mathlib.Data.Fin.Basic

def Fin.elim1
  {motive : Fin 1 → Sort u} (zero : motive 0) (i : Fin 1) : motive i
  := Fin.cases zero (λi => i.elim0) i

@[simp]
theorem Fin.elim1_zero
  {motive : Fin 1 → Sort u} {zero : motive 0} : Fin.elim1 zero 0 = zero := rfl

@[simp]
theorem Fin.elim1_const
  {motive : Sort u} {zero : motive} {i} : Fin.elim1 (motive := λ_ => motive) zero i = zero
  := by cases i using Fin.elim1; rfl

theorem Fin.dapply_elim1
  {motive' : Fin 1 → Sort v}
  {motive : Fin 1 → Sort u} {f : ∀{i : Fin 1}, motive i → motive' i}
  {zero : motive 0} {i : Fin 1} :
  f (Fin.elim1 zero i) = Fin.elim1 (f zero) i := by cases i using Fin.elim1; rfl

theorem Fin.apply_elim1 {f : α → β} {zero : α} {i : Fin 1}
   : f (Fin.elim1 (motive := λ_ => α) zero i)
   = Fin.elim1 (motive := λ_ => β) (f zero) i := by cases i using Fin.elim1; rfl

theorem Fin.comp_elim1 {f : α → β} {zero : α} : f ∘ Fin.elim1 zero = Fin.elim1 (f zero)
  := funext (Fin.elim1 rfl)

def Fin.elim2
  {motive : Fin 2 → Sort u} (zero : motive 0) (one : motive 1) (i : Fin 2) : motive i
  := Fin.cases zero (Fin.elim1 one) i

@[simp]
theorem Fin.elim2_zero
  {motive : Fin 2 → Sort u} {zero : motive 0} {one : motive 1} : Fin.elim2 zero one 0 = zero := rfl

@[simp]
theorem Fin.elim2_one
  {motive : Fin 2 → Sort u} {zero : motive 0} {one : motive 1} : Fin.elim2 zero one 1 = one := rfl

theorem Fin.apply_elim2 {f : α → β} {zero : α} {one : α} {i : Fin 2}
   : f (Fin.elim2 (motive := λ_ => α) zero one i)
   = Fin.elim2 (motive := λ_ => β) (f zero) (f one) i := by cases i using Fin.elim2 <;> rfl

theorem Fin.comp_elim2 {f : α → β} {zero : α} {one : α}
  : f ∘ Fin.elim2 zero one = Fin.elim2 (f zero) (f one)
  := funext (Fin.elim2 rfl rfl)

def Fin.elim3
  {motive : Fin 3 → Sort u}
  (zero : motive 0) (one : motive 1) (two : motive 2) (i : Fin 3) : motive i
  := Fin.cases zero (Fin.elim2 one two) i

@[simp]
theorem Fin.elim3_zero
  {motive : Fin 3 → Sort u} {zero : motive 0} {one : motive 1} {two : motive 2}
  : Fin.elim3 zero one two 0 = zero := rfl

@[simp]
theorem Fin.elim3_one
  {motive : Fin 3 → Sort u} {zero : motive 0} {one : motive 1} {two : motive 2}
  : Fin.elim3 zero one two 1 = one := rfl

@[simp]
theorem Fin.elim3_two
  {motive : Fin 3 → Sort u} {zero : motive 0} {one : motive 1} {two : motive 2}
  : Fin.elim3 zero one two 2 = two := rfl

theorem Fin.feq0 {motive : Fin 0 → Sort u} {f g : (i : Fin 0) → motive i}
  : f = g := funext (λi => i.elim0)

theorem Fin.feq1 {motive : Fin 1 → Sort u} {f g : (i : Fin 1) → motive i}
  : f = g ↔ f 0 = g 0 := ⟨
    λh => congrFun h 0,
    λh => funext (λi => by cases i using Fin.elim1; exact h)⟩

theorem Fin.feq2 {motive : Fin 2 → Sort u} {f g : (i : Fin 2) → motive i}
  : f = g ↔ f 0 = g 0 ∧ f 1 = g 1 := ⟨
    λh => ⟨congrFun h 0, congrFun h 1⟩,
    λ⟨_, _⟩ => funext (λi => by cases i using Fin.elim2 <;> simp [*])⟩

theorem Fin.feq3 {motive : Fin 3 → Sort u} {f g : (i : Fin 3) → motive i}
  : f = g ↔ f 0 = g 0 ∧ f 1 = g 1 ∧ f 2 = g 2 := ⟨
    λh => ⟨congrFun h 0, congrFun h 1, congrFun h 2⟩,
    λ⟨_, _, _⟩ => funext (λi => by cases i using Fin.elim3 <;> simp [*])⟩
