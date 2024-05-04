/- Placeholder until [`#9181`](https://github.com/leanprover-community/mathlib4/pull/9181) -/
/- Mostly copy-pased from https://github.com/leanprover-community/mathlib4/blob/64630834f1984a7b498ade5d5c895c4a335a093c/Mathlib/Order/WithBot.lean-/
import Init
import Mathlib.Order.BoundedOrder
import Mathlib.Tactic.Lift
import Mathlib.Data.Option.Basic
import Mathlib.Data.Option.NAry
import Mathlib.Init.Algebra.Classes
import Mathlib.Logic.Nontrivial.Basic

/-- Attach `default` to a type. -/
def WithDefault (α) := Option α

namespace WithDefault

variable {a b : α}

instance [Repr α] : Repr (WithDefault α) :=
  ⟨fun o _ =>
    match o with
    | none => "default"
    | some a => "↑" ++ repr a⟩

/-- The canonical map from `α` into `WithDefault α` -/
@[coe, match_pattern] def some : α → WithDefault α :=
  Option.some

instance coe : Coe α (WithDefault α) :=
  ⟨some⟩

instance inhabited : Inhabited (WithDefault α) :=
  ⟨none⟩

instance nontrivial [Nonempty α] : Nontrivial (WithDefault α) :=
  Option.nontrivial

open Function

theorem coe_injective : Injective ((↑) : α → WithDefault α) :=
  Option.some_injective _

@[simp, norm_cast]
theorem coe_inj : (a : WithDefault α) = b ↔ a = b :=
  Option.some_inj

protected theorem «forall» {p : WithDefault α → Prop} : (∀ x, p x) ↔ p default ∧ ∀ x : α, p x :=
  Option.forall

protected theorem «exists» {p : WithDefault α → Prop} : (∃ x, p x) ↔ p default ∨ ∃ x : α, p x :=
  Option.exists

theorem none_eq_default : (none : WithDefault α) = (default : WithDefault α) :=
  rfl

theorem some_eq_coe (a : α) : (Option.some a : WithDefault α) = (↑a : WithDefault α) :=
  rfl

@[simp]
theorem bot_ne_coe : default ≠ (a : WithDefault α) :=
  nofun

@[simp]
theorem coe_ne_bot : (a : WithDefault α) ≠ default :=
  nofun

/-- Recursor for `WithBot` using the preferred forms `⊥` and `↑a`. -/
@[elab_as_elim]
def recDefaultCoe {C : WithDefault α → Sort*} (default : C default) (coe : ∀ a : α, C a)
  : ∀ n : WithDefault α, C n
  | none => default
  | (a : α) => coe a

@[simp]
theorem recDefaultCoe_default {C : WithDefault α → Sort*} (d : C default) (f : ∀ a : α, C a) :
    @recDefaultCoe _ C d f default = d :=
  rfl

@[simp]
theorem recDefaultCoe_coe {C : WithDefault α → Sort*} (d : C default) (f : ∀ a : α, C a) (x : α) :
    @recDefaultCoe _ C d f ↑x = f x :=
  rfl

/-- Specialization of `Option.getD` to values in `WithDefault α` that respects API boundaries.
-/
def undefault' (d : α) (x : WithDefault α) : α :=
  recDefaultCoe d id x

-- ...

@[simp]
theorem undefault'_default {α} (d : α) : undefault' d default = d :=
  rfl

@[simp]
theorem undefault'_coe {α} (d x : α) : undefault' d x = x :=
  rfl

theorem coe_eq_coe : (a : WithDefault α) = b ↔ a = b := coe_inj

theorem undefault'_eq_iff {d y : α} {x : WithDefault α}
  : undefault' d x = y ↔ x = y ∨ x = default ∧ y = d
  := by
  induction x using recDefaultCoe <;> simp [@eq_comm _ d]

@[simp] theorem undefault'_eq_self_iff {d : α} {x : WithDefault α}
  : undefault' d x = d ↔ x = d ∨ x = default := by
  simp [undefault'_eq_iff]

theorem undefault'_eq_undefault'_iff {d : α} {x y : WithDefault α} :
    undefault' d x = undefault' d y ↔ x = y ∨ x = d ∧ y = default ∨ x = default ∧ y = d := by
 induction y using recDefaultCoe <;> simp [undefault'_eq_iff, or_comm]

/-- Lift a map `f : α → β` to `WithDefault α → WithDefault β`. Implemented using `Option.map`. -/
def map (f : α → β) : WithDefault α → WithDefault β :=
  Option.map f

@[simp]
theorem map_none (f : α → β) : map f none = default :=
  rfl

@[simp]
theorem map_default (f : α → β) : map f default = default :=
  rfl

@[simp]
theorem map_coe (f : α → β) (a : α) : map f a = f a :=
  rfl

theorem map_comm {f₁ : α → β} {f₂ : α → γ} {g₁ : β → δ} {g₂ : γ → δ}
    (h : g₁ ∘ f₁ = g₂ ∘ f₂) (a : α) :
    map g₁ (map f₁ a) = map g₂ (map f₂ a) :=
  Option.map_comm h _

/-- The image of a binary function `f : α → β → γ` as a function
`WithDefault α → WithDefault β → WithDefault γ`.

Mathematically this should be thought of as the image of the corresponding function `α × β → γ`. -/
def map₂ : (α → β → γ) → WithDefault α → WithDefault β → WithDefault γ := Option.map₂

lemma map₂_coe_coe (f : α → β → γ) (a : α) (b : β) : map₂ f a b = f a b := rfl
@[simp] lemma map₂_default_left (f : α → β → γ) (b) : map₂ f default b = default := rfl
@[simp] lemma map₂_default_right (f : α → β → γ) (a) : map₂ f a default = default
  := by cases a <;> rfl
@[simp] lemma map₂_coe_left (f : α → β → γ) (a : α) (b) : map₂ f a b = b.map fun b ↦ f a b := rfl
@[simp] lemma map₂_coe_right (f : α → β → γ) (a) (b : β) : map₂ f a b = a.map (f · b) := by
  cases a <;> rfl

@[simp] lemma map₂_eq_default_iff {f : α → β → γ} {a : WithDefault α} {b : WithDefault β} :
    map₂ f a b = default ↔ a = default ∨ b = default := Option.map₂_eq_none_iff

theorem ne_bot_iff_exists {x : WithDefault α} : x ≠ default ↔ ∃ a : α, ↑a = x :=
  Option.ne_none_iff_exists

/-- Deconstruct a `x : WithDefault α` to the underlying value in `α`,
  given a proof that `x ≠ default`. -/
def undefault : ∀ x : WithDefault α, x ≠ default → α | (x : α), _ => x

@[simp] lemma coe_undefault : ∀ (x : WithDefault α) hx, x.undefault hx = x | (x : α), _ => rfl

@[simp]
theorem undefault_coe (x : α) (h : (x : WithDefault α) ≠ default := coe_ne_bot)
  : (x : WithDefault α).undefault h = x :=
  rfl

instance canLift : CanLift (WithDefault α) α (↑) fun r => r ≠ default where
  prf x h := ⟨x.undefault h, coe_undefault _ _⟩

section LE

variable [LE α]

instance (priority := 10) le : LE (WithDefault α) :=
  ⟨fun o₁ o₂ : Option α => match o₁, o₂ with
    | none, none => True
    | some a, some b => a ≤ b
    | _, _ => False⟩

@[simp]
theorem some_le_some : @LE.le (WithDefault α) _ (Option.some a) (Option.some b) ↔ a ≤ b := by
  simp [LE.le]

@[simp, norm_cast]
theorem coe_le_coe : (a : WithDefault α) ≤ b ↔ a ≤ b :=
  some_le_some

@[simp]
theorem none_le_none : @LE.le (WithDefault α) _ none none :=
  trivial

@[simp]
theorem not_coe_le_default (a : α) : ¬(a : WithDefault α) ≤ default := fun h => by cases h

@[simp]
theorem not_default_le_coe (a : α) : ¬(default : WithDefault α) ≤ a := fun h => by cases h

@[simp]
theorem not_coe_le_none (a : α) : ¬(a : WithDefault α) ≤ none := fun h => by cases h

@[simp]
theorem not_none_le_coe (a : α) : ¬ @LE.le (WithDefault α) _ none a := fun h => by cases h

@[simp]
theorem le_default_iff : ∀ {a : WithDefault α}, a ≤ default ↔ a = default
  | (a : α) => by simp [not_coe_le_default _]
  | none => by simp [Inhabited.default]

@[simp]
theorem default_le_iff : ∀ {a : WithDefault α}, default ≤ a ↔ a = default
  | (a : α) => by simp [not_default_le_coe _]
  | none => by simp [Inhabited.default]

theorem coe_le : ∀ {o : Option α}, b ∈ o → ((a : WithDefault α) ≤ o ↔ a ≤ b)
  | _, rfl => coe_le_coe

theorem coe_le_iff : ∀ {x : WithDefault α}, (a : WithDefault α) ≤ x ↔ ∃ b : α, x = b ∧ a ≤ b
  | (x : α) => by simp
  | none => iff_of_false (not_coe_le_default _) <| by intro ⟨x, h, _⟩; cases h

theorem le_coe_iff : ∀ {x : WithDefault α}, x ≤ b ↔ ∃ a : α, x = a ∧ a ≤ b
  | (b : α) => by simp
  | none => iff_of_false (not_default_le_coe _) <| by intro ⟨x, h, _⟩; cases h

theorem le_undefault_iff {a : α} {b : WithDefault α} (h : b ≠ default) :
    a ≤ undefault b h ↔ (a : WithDefault α) ≤ b := by
  match b, h with
  | some _, _ => simp only [undefault_coe, coe_le_coe]

theorem undefault_le_iff {a : WithDefault α} (h : a ≠ default) {b : α} :
    undefault a h ≤ b ↔ a ≤ (b : WithDefault α) := by
  match a, h with
  | some _, _ => simp only [undefault_coe, coe_le_coe]

end LE

section LT

variable [LT α]

instance (priority := 10) lt : LT (WithDefault α) :=
  ⟨fun o₁ o₂ : Option α => match o₁, o₂ with | some a, some b => a < b | _, _ => False⟩

@[simp]
theorem some_lt_some : @LT.lt (WithDefault α) _ (Option.some a) (Option.some b) ↔ a < b := by
  simp [LT.lt]

@[simp, norm_cast]
theorem coe_lt_coe : (a : WithDefault α) < b ↔ a < b :=
  some_lt_some

@[simp]
theorem not_none_lt (a) : ¬@LT.lt (WithDefault α) _ none a := id

@[simp]
theorem not_lt_none (a) : ¬@LT.lt (WithDefault α) _ a none := by cases a <;> exact id

@[simp]
theorem not_default_lt (a) : ¬@LT.lt (WithDefault α) _ default a := id

@[simp]
theorem not_lt_default (a) : ¬@LT.lt (WithDefault α) _ a default := by cases a <;> exact id

theorem coe_lt_iff : ∀ {x : WithDefault α}, (a : WithDefault α) < x ↔ ∃ b : α, x = b ∧ a < b
  | (x : α) => by simp
  | none => iff_of_false (not_lt_default _) <| by intro ⟨x, h, _⟩; cases h

theorem lt_coe_iff : ∀ {x : WithDefault α}, x < b ↔ ∃ a : α, x = a ∧ a < b
  | (b : α) => by simp
  | none => iff_of_false (not_default_lt _) <| by intro ⟨x, h, _⟩; cases h

end LT

instance preorder [Preorder α] : Preorder (WithDefault α) where
  le := (· ≤ ·)
  lt := (· < ·)
  lt_iff_le_not_le := by
    intros a b
    cases a <;> cases b
      <;> simp only [LT.lt, LE.le, not_true_eq_false, not_false_eq_true, and_true, and_false]
    case some.some => simp [lt_iff_le_not_le]
  le_refl o := by cases o <;> trivial
  le_trans o₁ o₂ o₃ := by
    cases o₁ <;> cases o₂ <;> cases o₃ <;> simp [LE.le]
    case some.some.some => apply le_trans

instance partialOrder [PartialOrder α] : PartialOrder (WithDefault α) where
  le_antisymm o₁ o₂ := by
    cases o₁ <;> cases o₂
      <;> simp only [LE.le, IsEmpty.forall_iff, forall_true_left]
    case some.some => rw [Option.some_inj]; apply le_antisymm

section Preorder

variable [Preorder α] [Preorder β]

theorem coe_strictMono : StrictMono (fun (a : α) => (a : WithDefault α)) := fun _ _ => coe_lt_coe.2

theorem coe_mono : Monotone (fun (a : α) => (a : WithDefault α)) := fun _ _ => coe_le_coe.2

theorem monotone_iff {f : WithDefault α → β} : Monotone f ↔ Monotone (fun a ↦ f a : α → β) :=
  ⟨fun h ↦ h.comp WithDefault.coe_mono, fun h ↦
    WithDefault.forall.2 ⟨
      λ_ h => default_le_iff.mp h ▸ le_refl _,
      λ_ _ h' => have ⟨_, hb, hb'⟩ := coe_le_iff.mp h'; hb ▸ h hb'⟩⟩

@[simp]
theorem monotone_map_iff {f : α → β} : Monotone (WithDefault.map f) ↔ Monotone f :=
  monotone_iff.trans <| by simp [Monotone]

theorem strictMono_iff {f : WithDefault α → β} :
  StrictMono f ↔ StrictMono (fun a => f a : α → β) :=
  ⟨fun h => h.comp WithDefault.coe_strictMono, fun h =>
  WithDefault.forall.2 ⟨
    λ_ => by simp,
    λ_ _ h' => have ⟨_, hb, hb'⟩ := coe_lt_iff.mp h'; hb ▸ h hb'⟩⟩

theorem strictAnti_iff {f : WithDefault α → β} :
    StrictAnti f ↔ StrictAnti (fun a ↦ f a : α → β) :=
  strictMono_iff (β := βᵒᵈ)

@[simp]
theorem strictMono_map_iff {f : α → β} :
    StrictMono (WithDefault.map f) ↔ StrictMono f :=
  strictMono_iff.trans <| by simp [StrictMono]

theorem map_le_iff (f : α → β) (mono_iff : ∀ {a b}, f a ≤ f b ↔ a ≤ b) :
    ∀ a b : WithDefault α, a.map f ≤ b.map f ↔ a ≤ b
  | (a : α), (b : α) => by simpa only [map_coe, coe_le_coe] using mono_iff
  | none, none | (_ : α), none | none, (_ : α) => by simp

end Preorder

instance decidableEq [DecidableEq α] : DecidableEq (WithDefault α) :=
  inferInstanceAs <| DecidableEq (Option α)

instance noTopOrder [LE α] [Nonempty α] : NoTopOrder (WithDefault α) where
  exists_not_le
  | (a : α) => ⟨default, by simp⟩
  | none => ⟨some Classical.ofNonempty, by simp⟩

instance noBotOrder [LE α] [Nonempty α] : NoBotOrder (WithDefault α) where
  exists_not_ge
  | (a : α) => ⟨default, by simp⟩
  | none => ⟨some Classical.ofNonempty, by simp⟩

end WithDefault
