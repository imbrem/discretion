import Discretion.Utils.Set
import Discretion.Utils.Tuple
import Discretion.Utils.Perm
import Discretion.Utils.Equiv
import Discretion.Utils.Multiset

@[simp]
def Nat.swap01 : ℕ → ℕ | 0 => 1 | 1 => 0 | n => n

@[simp]
theorem Nat.swap01_swap01 : ∀n, Nat.swap01 (Nat.swap01 n) = n
  | 0 => rfl
  | 1 => rfl
  | _ + 2 => rfl

@[simp]
theorem Nat.swap01_comp_swap01 : Nat.swap01 ∘ Nat.swap01 = id := funext Nat.swap01_swap01

theorem Function.comp_update_apply {α β γ} [DecidableEq α] {f : β → γ} {g : α → β}
  (a : _) (b : _) (c : _) : f (Function.update g a b c) = Function.update (f ∘ g) a (f b) c
  := by simp only [Function.update]; split <;> simp

theorem Nat.pred_comp_succ : Nat.pred ∘ Nat.succ = id := funext Nat.pred_succ

theorem Function.comp_left_mono {α β γ} [Preorder γ] {f : α → β} {g₁ g₂ : β → γ}
  (hg : g₁ ≤ g₂) : g₁ ∘ f ≤ g₂ ∘ f := λa => hg (f a)

theorem Fin.strictMono_id_le {n} {f : Fin n → Fin m} (h : StrictMono f)
  : ∀i : Fin n, (↑i : ℕ) ≤ (f i : ℕ) := by
  intro i
  cases n with
  | zero => exact i.elim0
  | succ n => induction i using Fin.induction with
    | zero => simp
    | succ i I => exact Nat.succ_le_of_lt $ lt_of_le_of_lt I $ Fin.lt_def.mp $ h i.castSucc_lt_succ

theorem Fin.strictMono_eq_id {n} {f : Fin n → Fin n} (h : StrictMono f) : f = id := by
  induction n with
  | zero => funext i; exact i.elim0
  | succ n I =>
    have hlast : f (Fin.last n) = (Fin.last n) := le_antisymm (Fin.le_last _) (strictMono_id_le h _)
    have lt_last : ∀i, i < Fin.last n → f i < Fin.last n := λi hi =>
      lt_of_le_of_ne (Fin.le_last _) (hlast ▸ h.injective.ne (ne_of_lt hi))
    let g : Fin n → Fin n := λi : Fin n => Fin.mk (f i) (lt_last i (Fin.lt_def.mpr (by simp)));
    have hg : StrictMono g := λ⟨i, hi⟩ ⟨j, hj⟩ hij => by
      have hf := @h ⟨i, Nat.lt_succ_of_lt hi⟩ ⟨j, Nat.lt_succ_of_lt hj⟩
        (Fin.lt_def.mpr (Fin.lt_def.mp hij))
      simp [g, hf]
    funext i
    cases Nat.lt_succ_iff_lt_or_eq.mp i.prop with
    | inl hi' =>
      have hfi : (f i : ℕ) = (g ⟨i, hi'⟩ : ℕ) := by simp
      ext
      rw [hfi, I hg]
      rfl
    | inr hn =>
      have hi : i = Fin.last n := Fin.ext hn
      rw [hi, hlast]; rfl
    -- apply Function.Surjective.injective_comp_right Fin.rev_surjective
    -- funext i
    -- simp only [Function.comp_apply]
    -- induction i using Fin.induction with
    -- | zero => sorry
    -- | succ i I => sorry

theorem Fin.strictMono_eq_cast {n} {f : Fin n → Fin m} (h : StrictMono f) (eq : n = m) : f = cast eq
  := by cases eq; exact Fin.strictMono_eq_id h
