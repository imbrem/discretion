import Mathlib.Data.Fin.Basic

def Fin.elim1
  {motive : Fin 1 → Sort u} (zero : motive 0) (i : Fin 1) : motive i
  := Fin.cases zero (λi => i.elim0) i

def Fin.elim2
  {motive : Fin 2 → Sort u} (zero : motive 0) (one : motive 1) (i : Fin 2) : motive i
  := Fin.cases zero (Fin.elim1 one) i

def Fin.elim3
  {motive : Fin 3 → Sort u}
  (zero : motive 0) (one : motive 1) (two : motive 2) (i : Fin 3) : motive i
  := Fin.cases zero (Fin.elim2 one two) i

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
