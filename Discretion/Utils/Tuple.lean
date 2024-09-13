import Mathlib.Data.Set.Function
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset
import Batteries.Data.Fin.Lemmas

theorem Fin.foldl_eq_foldr {α : Type u} {f : α → α → α} [Std.Commutative f] [Std.Associative f]
  (x : α) (xs : Fin n → α)
  : foldl n (λa i => f a (xs i)) x = foldr n (λi a => f (xs i) a) x := by
  rw [
    foldr_eq_foldr_list, foldl_eq_foldl_list,
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
  : max f = ⊥ ↔ f = ⊥ := (Fin.max_eq_bot_iff f).trans Function.funext_iff.symm

theorem Fin.max_nat_eq_zero (f : Fin n → ℕ) (hf : max f = 0)
  : ∀i, f i = 0 := max_eq_bot f hf

theorem Fin.max_nat_eq_zero' (f : Fin n → ℕ) (hf : max f = 0)
  : f = 0 := max_eq_bot' f hf

theorem Fin.max_nat_eq_zero_iff (f : Fin n → ℕ)
  : max f = 0 ↔ ∀i, f i = 0 := max_eq_bot_iff f

theorem Fin.max_nat_eq_zero_iff' (f : Fin n → ℕ)
  : max f = 0 ↔ f = 0 := max_eq_bot_iff' f

instance singletonSetInhabited {a : α} : Inhabited ({a} : Set α) := ⟨⟨a, rfl⟩⟩

def Fin.supD [Sup α] (f : Fin n → α) (b : α) : α := Fin.foldr n (λi v => (f i) ⊔ v) b

@[simp]
theorem Fin.supD_zero [Sup α] (f : Fin 0 → α) (b : α) : supD f b = b := by simp [supD]

theorem Fin.supD_succ [Sup α] (f : Fin (n+1) → α) (b : α)
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

def Fin.sup [Sup α] [Bot α] (f : Fin n → α) := supD f ⊥

@[simp]
theorem Fin.sup_zero [Sup α] [Bot α] (f : Fin 0 → α) : sup f = ⊥ := by simp [sup]

theorem Fin.sup_succ [Sup α] [Bot α] (f : Fin (n+1) → α)
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

theorem Fin.addCases_zero {n} {α : Fin n → Type _}
  (l : (i : Fin n) → α i) (r : (i : Fin 0) → α (Fin.natAdd n i))
  : @addCases n 0 _ l r = l := by
  funext i
  simp only [addCases, Nat.add_zero, is_lt]
  rfl

theorem Fin.addCases_zero_right {n} (l : Fin 0 → α) (r : Fin n → α)
  : @addCases 0 n (λ_ => α) l r = r ∘ cast (by simp) := by
  funext i
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
        rw [Nat.sub_add_cancel (Nat.le_of_not_lt ha), Nat.sub_add_cancel (Nat.le_of_not_lt hb)] at h
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

-- TODO: addCases associator + inverse associator, to go with symmetry...

-- TODO: addCases unitors...
