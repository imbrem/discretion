import Mathlib.Data.Set.Function
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset

theorem Nat.pred_comp_succ : Nat.pred ∘ Nat.succ = id := funext Nat.pred_succ

@[simp]
theorem Set.eqOn_insert {s : Set α} {f₁ f₂ : α → β}
  : (insert a s).EqOn f₁ f₂ ↔ s.EqOn f₁ f₂ ∧ f₁ a = f₂ a := by
  rw [<-union_singleton, eqOn_union]
  simp [*]

-- TODO: think about this...
@[simp]
theorem Set.eqOn_insert' {s : Set α} {f₁ f₂ : α → β}
  : (s.insert a).EqOn f₁ f₂ ↔ s.EqOn f₁ f₂ ∧ f₁ a = f₂ a := eqOn_insert

theorem Set.EqOn.insert {s : Set α} {f₁ f₂ : α → β} (heq : s.EqOn f₁ f₂) (ha : f₁ a = f₂ a)
  : (insert a s).EqOn f₁ f₂ := eqOn_insert.mpr ⟨heq, ha⟩

theorem Set.eqOn_comp_left_iff_of_eqOn_injOn_image
  {s : Set α} {f₁ f₂ : α → β} {g₁ g₂ : β → γ}
  (hf₁ : (f₁ '' s ∪ f₂ '' s).InjOn g₁)
  (hg : (f₁ '' s ∪ f₂ '' s).EqOn g₁ g₂)
  : s.EqOn (g₁ ∘ f₁) (g₂ ∘ f₂) ↔ s.EqOn f₁ f₂ := by
  simp only [EqOn, iff_iff_eq]
  apply forall_congr
  intro a
  apply propext
  simp only [Function.comp_apply]
  . constructor
    . intro h ha
      apply hf₁
      . exact mem_union_left _ (mem_image_of_mem _ ha)
      . exact mem_union_right _ (mem_image_of_mem _ ha)
      . rw [<-hg] at h
        . exact h ha
        . exact mem_union_right _ (mem_image_of_mem _ ha)
    . intro h ha; rw [h ha, hg];  exact mem_union_right _ (mem_image_of_mem _ ha)

theorem Set.eqOn_comp_left_iff_of_injOn_image
  {s : Set α} {f₁ f₂ : α → β} {g : β → γ} (hf : (f₁ '' s ∪ f₂ '' s).InjOn g)
  : s.EqOn (g ∘ f₁) (g ∘ f₂) ↔ s.EqOn f₁ f₂
  := eqOn_comp_left_iff_of_eqOn_injOn_image hf (λ_ _ => rfl)

theorem Set.eqOn_comp_left_iff_of_injective
  {s : Set α} {f₁ f₂ : α → β} {g : β → γ} (hf : Function.Injective g)
  : s.EqOn (g ∘ f₁) (g ∘ f₂) ↔ s.EqOn f₁ f₂
  := eqOn_comp_left_iff_of_injOn_image (injOn_of_injective hf)

theorem Fin.foldl_eq_foldr {α} {f : α → α → α} (hcomm : Commutative f) (hassoc : Associative f)
  (x : α) (xs : Fin n → α)
  : foldl n (λa i => f a (xs i)) x = foldr n (λi a => f (xs i) a) x := by
  rw [
    foldr_eq_foldr_list, foldl_eq_foldl_list,
    <-List.foldl_map, <-List.foldr_map,
    List.foldl_eq_foldr hcomm hassoc
  ]

-- TODO: foldl_eq_foldr'...

-- TODO: Fin.{minD, min, infD, inf}

def Fin.maxD [Max α] (f : Fin n → α) (b : α) := Fin.foldr _ (λi v => max (f i) v) b

@[simp]
theorem Fin.maxD_zero [Max α] (f : Fin 0 → α) (b : α) : maxD f b = b := by simp [maxD]

theorem Fin.maxD_succ [Max α] (f : Fin (n+1) → α) (b : α)
  : maxD f b = max (f 0) (maxD (f ∘ Fin.succ) b)  := by simp [maxD, Fin.foldr_succ]

theorem Fin.maxD_succ' [LinearOrder α] (f : Fin (n+1) → α) (b : α)
    : maxD f b = maxD (f ∘ Fin.succ) (max b (f 0)) := by
  simp [maxD, <-foldl_eq_foldr max_commutative max_associative, Fin.foldl_succ]

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
  . apply Fin.max_eq_bot
  . intro hf
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
  simp [supD, <-foldl_eq_foldr sup_comm sup_assoc, Fin.foldl_succ]

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
      exact le_sup_of_le_right $ I (f ∘ succ) _ i

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

-- TODO: move to Tuple?

-- TODO: do Finset-style max'?

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

theorem Fin.sum_univ_list [AddCommMonoid α] (f : (Fin n) → α)
  : Finset.univ.sum f = (List.ofFn f).sum
  := by simp [Finset.sum]

open Classical in
theorem Finset.sum_nat_eq_zero (s : Finset α) (f : α → ℕ)
  : s.sum f = 0 ↔ ∀a ∈ s, f a = 0 := by induction s using Finset.induction with
    | empty => simp
    | insert ha I => simp [sum_insert ha, I]

theorem Finset.sum_nat_univ_eq_zero [Fintype α] (f : α → ℕ)
  : Finset.univ.sum f = 0 ↔ ∀a, f a = 0 := by
  rw [Finset.sum_nat_eq_zero]
  simp

theorem Multiset.map_finsum (i : Finset ι) (f : ι → Multiset α) (g : α → β)
  : (i.sum f).map g = i.sum (Multiset.map g ∘ f)
  := by
  open Classical in induction i using Finset.induction with
  | empty => rfl
  | insert =>
    rw [Finset.sum_insert]
    simp [*]
    assumption

theorem Multiset.not_mem_sum_map (s : Multiset ι) (f : ι → Multiset α) (a : α)
  : a ∉ Multiset.sum (s.map f) ↔ (∀i ∈ s, a ∉ f i) := by
  induction s using Multiset.induction <;> simp [*]

theorem Multiset.mem_sum_map (s : Multiset ι) (f : ι → Multiset α) (a : α)
  : a ∈ Multiset.sum (s.map f) ↔ (∃i ∈ s, a ∈ f i) := by
  induction s using Multiset.induction <;> simp [*]

theorem Multiset.not_mem_finsum (s : Finset ι) (f : ι → Multiset α) (a : α)
  : a ∉ s.sum f ↔ (∀i ∈ s, a ∉ f i) := not_mem_sum_map s.val f a

theorem Multiset.mem_finsum (s : Finset ι) (f : ι → Multiset α) (a : α)
  : a ∈ s.sum f ↔ (∃i ∈ s, a ∈ f i) := mem_sum_map s.val f a

theorem Multiset.not_mem_finsum_univ [Fintype ι] (f : ι → Multiset α) (a : α)
  : a ∉ Finset.univ.sum f ↔ (∀i, a ∉ f i) := by
  rw [Multiset.not_mem_finsum]
  simp

theorem Multiset.mem_finsum_univ [Fintype ι] (f : ι → Multiset α) (a : α)
  : a ∈ Finset.univ.sum f ↔ (∃i, a ∈ f i) := by
  rw [Multiset.mem_finsum]
  simp

theorem Fin.comp_addCases (f : α → β) (l: Fin n → α) (r : Fin m → α)
  : f ∘ (Fin.addCases l r) = Fin.addCases (f ∘ l) (f ∘ r) := by
  funext i
  simp only [addCases, eq_rec_constant, Function.comp_apply]
  split <;> rfl

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

theorem Fin.addCases_zero {n} (l : Fin n → α) (r : Fin 0 → α)
  : @addCases n 0 _ l r = l := by
  funext i
  simp only [addCases, Nat.add_zero, is_lt, ↓reduceDite]
  rfl

-- TODO: addCases associator + inverse associator, to go with symmetry...

-- TODO: addCases unitors...
