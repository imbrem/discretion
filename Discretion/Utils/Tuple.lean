import Mathlib.Data.Set.Function
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Fin
import Batteries.Data.Fin.Lemmas
import Batteries.Data.Fin.Fold

import Discretion.Utils.Cast

theorem Fin.foldl_eq_foldr {α : Type u} {f : α → α → α} [Std.Commutative f] [Std.Associative f]
  (x : α) (xs : Fin n → α)
  : foldl n (λa i => f a (xs i)) x = foldr n (λi a => f (xs i) a) x := by
  rw [
    foldr_eq_foldr_finRange, foldl_eq_foldl_finRange,
    <-List.foldl_map, <-List.foldr_map,
    List.foldl_eq_foldr
  ]

-- TODO: foldl_eq_foldr'...

-- TODO: Fin.{minD, min, infD, inf}

-- @[inline] def natSub (n) (i : Fin (n + m)) (h : n ≤ i) : Fin m :=
--   ⟨i - n, by rw [Nat.add_comm]⟩

-- def Fin.casesAdd {m : Nat} {n : Nat}
--   {motive : Fin (m + n) → Sort u}
--   (left : (i : Fin m) → motive (Fin.addNat i n))
--   (right : (i : Fin n) → motive (i.castLE (by simp)))
--   (i : Fin (m + n)): motive i
--   := if h : i < n then right ⟨i, h⟩ else left ⟨i - n, sorry⟩

def Fin.maxD [Max α] (f : Fin n → α) (b : α) := Fin.foldr _ (λi v => max (f i) v) b

@[simp]
theorem Fin.maxD_zero [Max α] (f : Fin 0 → α) (b : α) : maxD f b = b := by simp [maxD]

theorem Fin.maxD_succ [Max α] (f : Fin (n+1) → α) (b : α)
  : maxD f b = max (f 0) (maxD (f ∘ Fin.succ) b)  := by simp [maxD, Fin.foldr_succ]

theorem Fin.maxD_succ' [LinearOrder α] (f : Fin (n+1) → α) (b : α)
    : maxD f b = maxD (f ∘ Fin.succ) (max b (f 0)) := by
  simp [maxD, <-foldl_eq_foldr, Fin.foldl_succ]

theorem Fin.base_le_maxD [LinearOrder α] (f : Fin n → α) (b : α)
  : b ≤ maxD f b := by induction n generalizing b with
  | zero => simp
  | succ n I => rw [maxD_succ]; exact le_trans (I _ _) (le_max_right _ _)

theorem Fin.elem_le_maxD [LinearOrder α] (f : Fin n → α) (b : α)
  : ∀(i : Fin n), f i ≤ maxD f b := by induction n generalizing b with
  | zero => simp
  | succ n I =>
    intro i
    cases i using induction with
    | zero => simp [maxD_succ]
    | succ i =>
      rw [maxD_succ]
      exact le_trans (I (f ∘ succ) b i) (le_max_right _ _)

theorem Fin.maxD_le [LinearOrder α] (f : Fin n → α) (b : α)
  : (∀i, f i ≤ c) → b ≤ c → maxD f b ≤ c := by
  induction n generalizing b with
  | zero => exact λ_ hb => by simp [hb]
  | succ n I =>
    intro hf hb
    rw [maxD_succ]
    exact max_le (hf 0) (I _ _ (λi => hf i.succ) hb)

def Fin.max [Max α] [Bot α] (f : Fin n → α) := maxD f ⊥

@[simp]
theorem Fin.max_zero [Max α] [Bot α] (f : Fin 0 → α) : max f = ⊥ := by simp [max]

theorem Fin.max_succ [Max α] [Bot α] (f : Fin (n+1) → α)
  : max f = Max.max (f 0) (max (f ∘ Fin.succ)) := by simp [max, maxD_succ]

theorem Fin.elem_le_max [LinearOrder α] [Bot α] (f : Fin n → α) : ∀(i : Fin n), f i ≤ max f
  := elem_le_maxD f ⊥

theorem Fin.max_le [LinearOrder α] [OrderBot α] (f : Fin n → α) (c : α) (hf : ∀i, f i ≤ c)
  : max f ≤ c := maxD_le f ⊥ hf (by simp)

theorem bot_comp_eq_bot {α β} [Bot γ] (f : α → β) : (⊥ : β → γ) ∘ f = ⊥ := rfl

-- theorem zero_comp_eq_zero {α β} [Zero γ] (f : α → β) : (0 : β → γ) ∘ f = (0 : α → γ) := rfl

@[simp]
theorem Fin.max_bot [LinearOrder α] [OrderBot α] : max (⊥ : Fin n → α) = ⊥ := by
  induction n <;> simp [Fin.max_succ, bot_comp_eq_bot, *]

theorem Fin.max_eq_bot [LinearOrder α] [OrderBot α] (f : Fin n → α) (hf : max f = ⊥)
  : ∀i, f i = ⊥ := by induction n with
  | zero => simp
  | succ n I =>
    rw [max_succ, _root_.max_eq_bot] at hf
    intro i
    cases i using Fin.cases with
    | zero => exact hf.1
    | succ i => exact (I _ hf.2) i

theorem Fin.max_eq_bot' [LinearOrder α] [OrderBot α] (f : Fin n → α) (hf : max f = ⊥)
  : f = ⊥ := funext (Fin.max_eq_bot f hf)

theorem Fin.max_eq_bot_iff [LinearOrder α] [OrderBot α] (f : Fin n → α)
  : max f = ⊥ ↔ ∀i, f i = ⊥ := by
  apply Iff.intro
  · apply Fin.max_eq_bot
  · intro hf
    cases (funext hf : f = ⊥)
    rw [max_bot]

theorem Fin.max_eq_bot_iff' [LinearOrder α] [OrderBot α] (f : Fin n → α)
  : max f = ⊥ ↔ f = ⊥ := (Fin.max_eq_bot_iff f).trans funext_iff.symm

theorem Fin.max_nat_eq_zero (f : Fin n → ℕ) (hf : max f = 0)
  : ∀i, f i = 0 := max_eq_bot f hf

theorem Fin.max_nat_eq_zero' (f : Fin n → ℕ) (hf : max f = 0)
  : f = 0 := max_eq_bot' f hf

theorem Fin.max_nat_eq_zero_iff (f : Fin n → ℕ)
  : max f = 0 ↔ ∀i, f i = 0 := max_eq_bot_iff f

theorem Fin.max_nat_eq_zero_iff' (f : Fin n → ℕ)
  : max f = 0 ↔ f = 0 := max_eq_bot_iff' f

instance singletonSetInhabited {a : α} : Inhabited ({a} : Set α) := ⟨⟨a, rfl⟩⟩

def Fin.supD [Max α] (f : Fin n → α) (b : α) : α := Fin.foldr n (λi v => (f i) ⊔ v) b

@[simp]
theorem Fin.supD_zero [Max α] (f : Fin 0 → α) (b : α) : supD f b = b := by simp [supD]

theorem Fin.supD_succ [Max α] (f : Fin (n+1) → α) (b : α)
  : supD f b = (f 0) ⊔ (supD (f ∘ Fin.succ) b)  := by simp [supD, Fin.foldr_succ]

theorem Fin.supD_succ' [SemilatticeSup α] (f : Fin (n+1) → α) (b : α)
    : supD f b = supD (f ∘ Fin.succ) (b ⊔ (f 0)) := by
  simp [supD, <-foldl_eq_foldr, Fin.foldl_succ]

theorem Fin.elem_le_supD [SemilatticeSup α] (f : Fin n → α) (b : α)
  : ∀(i : Fin n), f i ≤ supD f b := by
  induction n generalizing b with
  | zero => simp
  | succ n I =>
    intro i
    cases i using induction with
    | zero => simp [supD_succ]
    | succ i =>
      rw [supD_succ]
      exact le_sup_of_le_right <| I (f ∘ succ) _ i

theorem Fin.supD_le [SemilatticeSup α] (f : Fin n → α) (b : α)
  : (∀i, f i ≤ c) → b ≤ c → supD f b ≤ c := by
  induction n generalizing b with
  | zero => exact λ_ hb => by simp [hb]
  | succ n I =>
    intro hf hb
    rw [supD_succ]
    exact sup_le (hf 0) (I _ _ (λi => hf i.succ) hb)

def Fin.sup [Max α] [Bot α] (f : Fin n → α) := supD f ⊥

@[simp]
theorem Fin.sup_zero [Max α] [Bot α] (f : Fin 0 → α) : sup f = ⊥ := by simp [sup]

theorem Fin.sup_succ [Max α] [Bot α] (f : Fin (n+1) → α)
  : sup f = (f 0) ⊔ (sup (f ∘ Fin.succ)) := by simp [sup, supD_succ]

theorem Fin.elem_le_sup [SemilatticeSup α] [Bot α] (f : Fin n → α) : ∀(i : Fin n), f i ≤ sup f
  := elem_le_supD f ⊥

theorem Fin.sup_le [SemilatticeSup α] [OrderBot α] (f : Fin n → α) (c : α) (hf : ∀i, f i ≤ c)
  : sup f ≤ c := supD_le f ⊥ hf (by simp)

-- Note: this is basically Fin.sup mono; can do same with supD but order is wrong...

theorem Fin.sup_le_sup [SemilatticeSup α] [OrderBot α] (f g : Fin n → α)
  (h : ∀i, f i ≤ g i) : sup f ≤ sup g := by
  induction n with
  | zero => simp
  | succ n I =>
    rw [Fin.sup_succ, Fin.sup_succ]
    exact _root_.sup_le_sup (h 0) (I _ _ (λi => h i.succ))

theorem Fin.sup_left_le_sup_addCases [SemilatticeSup α] [OrderBot α] (f : Fin n → α) (g : Fin m → α)
  : sup f ≤ sup (addCases f g) := Fin.sup_le _ _ (λi => by
    have h := addCases_left i ▸ elem_le_sup (addCases f g) (i.castAdd _)
    exact h)

theorem Fin.sup_right_le_sup_addCases [SemilatticeSup α] [OrderBot α] (f : Fin n → α) (g : Fin m → α)
  : sup g ≤ sup (addCases f g) := Fin.sup_le _ _ (λi => by
    have h := addCases_right i ▸ elem_le_sup (addCases f g) (i.natAdd _)
    exact h)

theorem Fin.sup_addCases [SemilatticeSup α] [OrderBot α] (f : Fin n → α) (g : Fin m → α)
  : sup (addCases f g) = sup f ⊔ sup g
  := le_antisymm
    (Fin.sup_le _ _ (λi => by
      simp only [addCases, eq_rec_constant]
      split
      · apply le_sup_of_le_left
        apply elem_le_sup
      · apply le_sup_of_le_right
        apply elem_le_sup))
    (sup_le_iff.mpr ⟨sup_left_le_sup_addCases f g, sup_right_le_sup_addCases f g⟩)

theorem Fin.sup_addCases_swap [SemilatticeSup α] [OrderBot α] (f : Fin n → α) (g : Fin m → α)
  : sup (addCases f g) = sup (addCases g f) := by simp only [Fin.sup_addCases, sup_comm]

theorem Fin.sup_comp_le [SemilatticeSup α] [OrderBot α] (f : Fin n → α) (ρ : Fin m → Fin n)
  : sup (f ∘ ρ) ≤ sup f
  := sup_le _ _ (λi => elem_le_sup f (ρ i))

theorem Fin.sup_comp_surj [SemilatticeSup α] [OrderBot α]
  (f : Fin n → α) {ρ : Fin m → Fin n} (hρ : Function.Surjective ρ)
  : sup (f ∘ ρ) = sup f
  := le_antisymm
    (sup_comp_le f ρ)
    (sup_le _ _ (λi => have ⟨j, hj⟩ := hρ i; hj ▸ elem_le_sup (f ∘ ρ) j))

-- TODO: move to Tuple?

-- TODO: do Finset-style max'?

theorem Fin.sum_univ_list [AddCommMonoid α] (f : (Fin n) → α)
  : Finset.univ.sum f = (List.ofFn f).sum
  := by simp [Finset.sum]

theorem Fin.comp_addCases_apply
  (f : α → β) (l: Fin n → α) (r : Fin m → α) (i)
  : f (Fin.addCases l r i) = Fin.addCases (f ∘ l) (f ∘ r) i := by
  simp only [addCases, eq_rec_constant, Function.comp_apply]
  split <;> rfl

theorem Fin.comp_addCases (f : α → β) (l: Fin n → α) (r : Fin m → α)
  : f ∘ (Fin.addCases l r) = Fin.addCases (f ∘ l) (f ∘ r) :=
  funext (Fin.comp_addCases_apply f l r)

theorem Fin.addCases_castAdd_natAdd {n m}
  : Fin.addCases (Fin.castAdd n) (Fin.natAdd m) = id := by
  funext i
  simp [addCases]

theorem Fin.addCases_comp_addCases_natAdd_castAdd (l: Fin n → α) (r : Fin m → α)
  : Fin.addCases l r ∘ Fin.addCases (Fin.natAdd _) (Fin.castAdd _) = Fin.addCases r l
  := by
  funext i
  simp only [addCases, eq_rec_constant, Function.comp_apply]
  split
  case h.isTrue h => simp
  case h.isFalse h =>
    simp only [coe_castAdd, coe_subNat, coe_cast, castLT_castAdd, not_lt]
    rw [dite_cond_eq_true]
    simp
    rw [Nat.sub_lt_iff_lt_add (Nat.le_of_not_lt h)]
    exact i.prop

theorem Fin.addCases_natAdd_castAdd_nil {n m}
  : addCases (natAdd n) (castAdd m) ∘ addCases (natAdd m) (castAdd n) = id := by
  rw [Fin.addCases_comp_addCases_natAdd_castAdd, Fin.addCases_castAdd_natAdd]

theorem Fin.addCases_natAdd_castAdd_left_inverse {n m}
  : Function.LeftInverse
    (addCases (natAdd m) (castAdd n))
    (addCases (natAdd n) (castAdd m))
  := congrFun Fin.addCases_natAdd_castAdd_nil

theorem Fin.addCases_natAdd_castAdd_right_inverse {n m}
  : Function.RightInverse
    (addCases (natAdd m) (castAdd n))
    (addCases (natAdd n) (castAdd m))
  := congrFun Fin.addCases_natAdd_castAdd_nil

theorem Fin.addCases_natAdd_castAdd_injective {n m}
  : Function.Injective (addCases (Fin.natAdd n) (Fin.castAdd m)) :=
  addCases_natAdd_castAdd_left_inverse.injective

theorem Fin.addCases_natAdd_castAdd_surjective {n m}
  : Function.Surjective (addCases (Fin.natAdd n) (Fin.castAdd m)) :=
    addCases_natAdd_castAdd_left_inverse.surjective

theorem Fin.addCases_natAdd_castAdd_bijective {n m}
  : Function.Bijective (addCases (Fin.natAdd n) (Fin.castAdd m))
    := ⟨addCases_natAdd_castAdd_injective, addCases_natAdd_castAdd_surjective⟩

def Fin.swapAdd (n m) : Fin (n + m) ≃ Fin (m + n) := ⟨
    addCases (Fin.natAdd m) (Fin.castAdd n),
    addCases (Fin.natAdd n) (Fin.castAdd m),
    addCases_natAdd_castAdd_left_inverse,
    addCases_natAdd_castAdd_right_inverse
  ⟩

theorem Fin.symm_swapAdd (n m)
  : (swapAdd n m).symm = swapAdd m n := rfl

@[simp]
theorem Fin.swapAdd_comp_swapAdd
  : swapAdd n m ∘ swapAdd m n = id := by rw [<-symm_swapAdd n m]; simp

theorem Fin.addCases_comp_swapAdd (l: Fin n → α) (r : Fin m → α)
  : addCases l r ∘ swapAdd m n = addCases r l := addCases_comp_addCases_natAdd_castAdd l r

theorem Fin.addCases_comp_symm_swapAdd (l: Fin n → α) (r : Fin m → α)
  : addCases l r ∘ (swapAdd n m).symm = addCases r l := addCases_comp_addCases_natAdd_castAdd l r

theorem Fin.addCases_zero {n} {motive : Fin n → Sort _}
  (l : (i : Fin n) → motive i) (r : (i : Fin 0) → motive (Fin.natAdd n i))
  : @addCases n 0 _ l r = l := by
  funext i
  simp only [addCases, Nat.add_zero, is_lt]
  rfl

theorem Fin.addCases_zero_right {n} (l : Fin 0 → α) (r : Fin n → α)
  : @addCases 0 n (λ_ => α) l r = r ∘ Fin.cast (by simp) := by
  funext ⟨i, _⟩
  simp [addCases, subNat, cast]

theorem Fin.addCases_comp_castAdd {n m} (l : Fin n → α) (r : Fin m → α)
  : addCases l r ∘ castAdd m = l := by funext i; simp

theorem Fin.addCases_comp_natAdd {n m} (l : Fin n → α) (r : Fin m → α)
  : addCases l r ∘ natAdd n = r := by funext i; simp

theorem Fin.addCases_surjective_left {n m} {l : Fin n → α}
  (hl : Function.Surjective l) (r : Fin m → α)
  : Function.Surjective (addCases l r) := λa => let ⟨i, hi⟩ := hl a; ⟨i.castAdd _, by simp [hi]⟩

theorem Fin.addCases_surjective_right {n m} (l : Fin n → α) {r : Fin m → α}
  (hr : Function.Surjective r)
  : Function.Surjective (addCases l r) := λa => let ⟨i, hi⟩ := hr a; ⟨i.natAdd _, by simp [hi]⟩

theorem Fin.addCases_injective {n m} {l : Fin n → α} {r : Fin m → α}
  (hl : Function.Injective l) (hr : Function.Injective r)
  (hlr : Disjoint (Set.range l) (Set.range r))
  : Function.Injective (addCases l r) := λa b => by
    simp only [addCases, eq_rec_constant]
    split
    case isTrue ha =>
      split
      case isTrue hb =>
        intro h
        have h := hl h;
        simp only [castLT, mk.injEq, Fin.ext_iff] at *
        exact h
      case isFalse hb =>
        intro h
        exact (Set.disjoint_right.mp hlr ⟨_, rfl⟩ ⟨_, h⟩).elim
    case isFalse ha =>
      split
      case isTrue hb =>
        intro h
        exact (Set.disjoint_left.mp hlr ⟨_, rfl⟩ ⟨_, h⟩).elim
      case isFalse hb =>
        intro h
        have h := hr h;
        simp only [subNat, cast,mk.injEq, Fin.ext_iff] at *
        rw [<-@Nat.add_left_inj _ _ n] at h
        simp only [coe_cast, Nat.sub_add_cancel (Nat.le_of_not_lt ha),
          Nat.sub_add_cancel (Nat.le_of_not_lt hb)] at h
        exact h

theorem Set.iUnion_addCases {n m} (l : Fin n → Set α) (r : Fin m → Set α)
  : ⋃i, Fin.addCases l r i = (⋃i, l i) ∪ (⋃i, r i) := by
  ext a
  simp only [mem_iUnion, mem_union]
  constructor
  intro ⟨i, hi⟩
  if h : i < n then
    simp only [Fin.addCases, h] at hi
    exact Or.inl ⟨_, hi⟩
  else
    simp only [Fin.addCases, h, eq_rec_constant] at hi
    exact Or.inr ⟨_, hi⟩
  intro h
  cases h with
  | inl h =>
    have ⟨i, hi⟩ := h;
    exists i.castAdd _
    simp [hi]
  | inr h =>
    have ⟨i, hi⟩ := h;
    exists i.natAdd _
    simp [hi]

def Fin.addCases3
  {motive : Fin (n + m + k) → Sort u}
  (left : (i : Fin n) → motive ((i.castAdd _).castAdd _))
  (mid : (i : Fin m) → motive ((i.natAdd n).castAdd _))
  (right : (i : Fin k) → motive ((i.natAdd (n + m))))
  (i : Fin (n + m + k)) : motive i
  := i.addCases (λi => i.addCases left mid) right

theorem Fin.cast_assoc_castAdd_castAdd
  {n m k} {i : Fin n}
  : ((i.castAdd m).castAdd k).cast (Nat.add_assoc n m k) = i.castAdd (m + k)
  := Fin.ext rfl

theorem Fin.cast_assoc_castAdd_natAdd
  {n m k} {i : Fin m}
  : ((i.natAdd n).castAdd k).cast (Nat.add_assoc n m k) = (i.castAdd k).natAdd n
  := Fin.ext rfl

theorem Fin.cast_assoc_natAdd
  {n m k} {i : Fin k}
  : (i.natAdd (n + m)).cast (Nat.add_assoc n m k) = (i.natAdd m).natAdd n
  := Fin.ext (Nat.add_assoc n m i)

theorem Fin.cast_assoc_castAdd
  {n m k} {i : Fin n}
  : (i.castAdd (m + k)).cast (Nat.add_assoc n m k).symm = (i.castAdd m).castAdd k
  := Fin.ext rfl

theorem Fin.cast_assoc_natAdd_castAdd
  {n m k} {i : Fin m}
  : ((i.castAdd k).natAdd n).cast (Nat.add_assoc n m k).symm = (i.natAdd n).castAdd k
  := Fin.ext rfl

theorem Fin.cast_assoc_natAdd_natAdd
  {n m k} {i : Fin k}
  : ((i.natAdd m).natAdd n).cast (Nat.add_assoc n m k).symm = i.natAdd (n + m)
  := Fin.ext (Nat.add_assoc n m i).symm

theorem Fin.addCases_cast_assoc
  {motive : Fin (n + (m + k)) → Sort u}
  {left : (i : Fin n) → motive (i.castAdd _)}
  {mid : (i : Fin m) → motive (((i.castAdd _).natAdd n))}
  {right : (i : Fin k) → motive ((i.natAdd m).natAdd n)}
  (i : Fin ((n + m) + k))
  : (i.cast (Nat.add_assoc n m k)).addCases (motive := motive) left (λi => i.addCases mid right)
  = i.addCases (λi => i.addCases left mid)
      (_root_.cast (pi_congr (λ_ => by rw [cast_assoc_natAdd])) right)
  := by
  cases i using Fin.addCases3 <;>
  simp only [addCases_left, addCases_right]
  case left => simp only [addCases, coe_cast, coe_castAdd, is_lt, ↓reduceDIte]; rfl
  case mid i =>
    apply Eq.trans
    exact addCases_right (left := left) (i.castAdd k)
    rw [addCases_left]
  case right i =>
    convert addCases_right (left := left) (i.natAdd m)
    rw [cast_assoc_natAdd]
    rw [cast_assoc_natAdd]
    simp only [addCases_right]
    apply heq_of_eq_cast (by rw [cast_assoc_natAdd])
    exact cast_apply_uniform (by simp [cast_assoc_natAdd]) right i

def Fin.addCases3'
  {motive : Fin (n + (m + k)) → Sort u}
  (left : (i : Fin n) → motive (i.castAdd _))
  (mid : (i : Fin m) → motive (((i.castAdd _).natAdd n)))
  (right : (i : Fin k) → motive ((i.natAdd m).natAdd n))
  (i : Fin (n + (m + k))) : motive i
  := i.addCases left (λi => i.addCases mid right)

theorem Fin.addCases_cast_assoc'
  {motive : Fin ((n + m) + k) → Sort u}
  {left : (i : Fin n) → motive ((i.castAdd _).castAdd _)}
  {mid : (i : Fin m) → motive ((i.natAdd n).castAdd _)}
  {right : (i : Fin k) → motive ((i.natAdd (n + m)))}
  (i : Fin (n + (m + k)))
  : (i.cast (Nat.add_assoc n m k).symm).addCases (motive := motive)
      (λi => i.addCases left mid) right
  = i.addCases left (λi => i.addCases mid
    (_root_.cast (pi_congr (λi => by rw [cast_assoc_natAdd_natAdd])) right))
  := by
  have hi : i = (i.cast (Nat.add_assoc n m k).symm).cast (Nat.add_assoc n m k) := by simp
  rw [hi, addCases_cast_assoc]
  simp

-- TODO: addCases associator + inverse associator, to go with symmetry...

-- TODO: addCases unitors...

def Fin.flatten
  {n}
  {arity : Fin n → ℕ}
  (tuples : ∀i, Fin (arity i) → α)
  (i : Fin (∑i, arity i)) : α
  := match n with
  | 0 => i.elim0
  | n + 1 =>
    if h : i < arity 0
    then tuples 0 ⟨i, h⟩
    else flatten (arity := arity ∘ Fin.succ) (λi k => tuples i.succ k) ⟨i - arity 0, calc
      _ < ∑i, arity i - arity 0 := by omega
      _ = _ := by simp [Finset.sum]
    ⟩

@[simp]
theorem Fin.flatten_zero : flatten (n := 0) (arity := arity) tuples = Fin.elim0 := rfl

theorem Fin.flatten_succ_cast {arity tuples} (i : Fin (arity 0 + ∑i, arity (succ i)))
  : flatten (n := n + 1) (α := α) (arity := arity) tuples (i.cast (by simp [Finset.sum]))
  = i.addCases (tuples 0)
    (flatten (n := n) (arity := arity ∘ Fin.succ) (λi => tuples i.succ))
  := by
  cases i using Fin.addCases <;>
  simp [flatten]

theorem Fin.flatten_succ {arity tuples} (i : Fin (∑i, arity i))
  : flatten (n := n + 1) (α := α) (arity := arity) tuples i
  = (i.cast (m := arity 0 + ∑i, arity (succ i)) (by simp [Finset.sum])).addCases (tuples 0)
    (flatten (n := n) (arity := arity ∘ Fin.succ) (λi => tuples i.succ))
  := flatten_succ_cast (i.cast (by simp [Finset.sum]))

theorem Fin.flatten_cons {n m} {arity tuples} (head : Fin m → α) (i : Fin (∑i, cons m arity i))
  : flatten (n := n + 1) (α := α) (arity := (cons m arity)) (cons head tuples) i
  = (i.cast (m := m + ∑i, arity i) (by simp)).addCases head (flatten tuples)
  := flatten_succ_cast (i.cast (by simp [Finset.sum]))

-- TODO: flatten_snoc

@[simp]
theorem Fin.flatten_one : flatten (n := 1) (α := α) (arity := arity) tuples = tuples 0 := by
  funext i; rw [flatten_succ, addCases_zero]; rfl

-- theorem Fin.sum_castLE {m n} (h : m ≤ n) (f : Fin n → ℕ)
--   : ∑i: Fin m, f (i.castLE h) = ∑i : {i : Fin n // i < m}, f i
--   := by induction h with
--   | refl =>
--     have h : Finset.univ (α := Fin m)
--       = (Finset.univ (α := {i : Fin m // i < m})).map ⟨Subtype.val, Subtype.val_injective⟩
--       := Finset.ext (λ_ => by simp)
--     simp only [castLE_rfl, id_eq, h, Finset.sum_map]
--     rfl
--   | step h I =>
--     convert I (λi => f i) using 2
--     sorry
--     sorry
--     sorry
--     sorry

-- theorem Fin.sum_castLE_le {m n} (h : m ≤ n) (f : Fin n → ℕ) : ∑i: Fin m, f (i.castLE h) ≤ ∑i, f i
--   := sorry

-- def Fin.partition {n} {arity : Fin n → ℕ}
--   (tuple : Fin (∑i, arity i) → α) (i : Fin n) (j : Fin (arity i)) : α
--   := tuple ⟨j + ∑k: Fin i, arity (k.castLT (lt_trans k.isLt i.isLt)), by
--     clear tuple
--     calc
--     _ < ∑k: Fin (↑i + 1), snoc (λk => arity (k.castLT (lt_trans k.isLt i.isLt))) (arity i) k
--       := by simp [Nat.add_comm]
--     _ = ∑k: Fin (↑i + 1), arity (k.castLE (Nat.succ_le_of_lt i.isLt))
--       := by congr; funext k; cases k using Fin.lastCases <;> simp only [snoc_last, snoc_castSucc,
--         Nat.succ_eq_add_one, castLE_castSucc] <;> rfl
--     _ ≤ _ := Fin.sum_castLE_le _ _
--     ⟩

def Fin.dflatten
  {n}
  {arity : Fin n → ℕ}
  {motive : ∀i, Fin (arity i) → Sort u}
  (tuples : ∀i k, motive i k)
  (i : Fin (∑i, arity i))
  : flatten motive i
  := match n with
  | 0 => i.elim0
  | n + 1 =>
    if h : i < arity 0
    then _root_.cast (by simp [flatten, h]) (tuples 0 ⟨i, h⟩)
    else _root_.cast (by simp [flatten, h]) (dflatten
      (arity := arity ∘ Fin.succ)
      (λi k => tuples i.succ k)
      ⟨i - arity 0, calc
        _ < ∑i, arity i - arity 0 := by omega
        _ = ∑i, Fin.cons (arity 0) (arity ∘ Fin.succ) i - arity 0 := by
          congr; funext i; cases i using Fin.cases <;> rfl
        _ = _ := by simp
      ⟩
    )
