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
      . apply le_sup_of_le_left
        apply elem_le_sup
      . apply le_sup_of_le_right
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

theorem Fin.addCases_zero {n} {α : Fin n → Type _}
  (l : (i : Fin n) → α i) (r : (i : Fin 0) → α (Fin.natAdd n i))
  : @addCases n 0 _ l r = l := by
  funext i
  simp only [addCases, Nat.add_zero, is_lt, ↓reduceDite]
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

-- TODO: addCases associator + inverse associator, to go with symmetry...

-- TODO: addCases unitors...

def Fin.numMissedBefore (ρ : Fin n → Fin m) : ℕ → ℕ
  | 0 => 0
  | k + 1 => (if ∃i : Fin n, ρ i = k then 0 else 1) + numMissedBefore ρ k

@[simp]
theorem Fin.numMissedBefore_zero (ρ : Fin n → Fin m)
  : numMissedBefore ρ 0 = 0 := rfl

theorem Fin.numMissedBefore_le_numMissedBefore_succ (ρ : Fin n → Fin m) (k : ℕ)
  : numMissedBefore ρ k ≤ numMissedBefore ρ (k + 1) := by simp [numMissedBefore]

theorem Fin.numMissedBefore_mono (ρ : Fin n → Fin m) : Monotone (numMissedBefore ρ) := by
  intro i j hij
  induction hij with
  | refl => rfl
  | step _ I => exact I.trans (numMissedBefore_le_numMissedBefore_succ ρ _)

theorem Fin.numMissedBefore_le_succ (ρ : Fin n → Fin m) (k : ℕ)
  : numMissedBefore ρ (k + 1) ≤ numMissedBefore ρ k + 1
  := by simp only [numMissedBefore]; split <;> simp_arith

def Fin.numMissed (ρ : Fin n → Fin m) : ℕ := numMissedBefore ρ m

@[simp]
theorem Fin.numMissed_to_zero (ρ : Fin n → Fin 0)
  : numMissed ρ = 0 := by simp [numMissed]

@[simp]
theorem Fin.numMissedBefore_from_zero (ρ : Fin 0 → Fin m)
  : numMissedBefore ρ k = k := by induction k with
  | zero => rfl
  | succ k I => simp [numMissedBefore, Nat.add_comm, I]

@[simp]
theorem Fin.numMissed_from_zero (ρ : Fin 0 → Fin m)
  : numMissed ρ = m := numMissedBefore_from_zero ρ

def Fin.numHitBefore (ρ : Fin n → Fin m) : ℕ → ℕ
  | 0 => 0
  | k + 1 => (if ∃i : Fin n, ρ i = k then 1 else 0) + numHitBefore ρ k

def Fin.numHit (ρ : Fin n → Fin m) : ℕ := numHitBefore ρ m

theorem Fin.numMissedBefore_add_numHitBefore (ρ : Fin n → Fin m) (k : ℕ)
  : numMissedBefore ρ k + numHitBefore ρ k = k := by
  induction k with
  | zero => simp [numMissedBefore, numHitBefore]
  | succ n I =>
    simp only [numMissedBefore, numHitBefore]
    split <;> simp_arith [I]

theorem Fin.total_sub_numMissedBefore (ρ : Fin n → Fin m) (k : ℕ)
  : k - numMissedBefore ρ k = numHitBefore ρ k := by
  conv =>
    lhs
    lhs
    rw [<-Fin.numMissedBefore_add_numHitBefore ρ k]
  simp

theorem Fin.total_sub_numHitBefore (ρ : Fin n → Fin m) (k : ℕ)
  : k - numHitBefore ρ k = numMissedBefore ρ k := by
  conv =>
    lhs
    lhs
    rw [<-Fin.numMissedBefore_add_numHitBefore ρ k]
  simp

theorem Fin.numMissedBefore_eq_total_sub_numHitBefore (ρ : Fin n → Fin m) (k : ℕ)
  : numMissedBefore ρ k = k - numHitBefore ρ k := by
  rw [total_sub_numHitBefore ρ k]

theorem Fin.numHitBefore_eq_total_sub_numMissedBefore (ρ : Fin n → Fin m) (k : ℕ)
  : numHitBefore ρ k = k - numMissedBefore ρ k := by
  rw [total_sub_numMissedBefore ρ k]

theorem Fin.numMissed_add_numHit (ρ : Fin n → Fin m)
  : numMissed ρ + numHit ρ = m := numMissedBefore_add_numHitBefore ρ m

theorem Fin.total_sub_numMissed (ρ : Fin n → Fin m)
  : m - numMissed ρ = numHit ρ := total_sub_numMissedBefore ρ m

theorem Fin.total_sub_numHit (ρ : Fin n → Fin m)
  : m - numHit ρ = numMissed ρ := total_sub_numHitBefore ρ m

theorem Fin.numMissed_eq_total_sub_numHit (ρ : Fin n → Fin m)
  : numMissed ρ = m - numHit ρ := numMissedBefore_eq_total_sub_numHitBefore ρ m

theorem Fin.numHit_eq_total_sub_numMissed (ρ : Fin n → Fin m)
  : numHit ρ = m - numMissed ρ := numHitBefore_eq_total_sub_numMissedBefore ρ m

theorem Fin.numMissed_le_total (ρ : Fin n → Fin m)
  : numMissed ρ ≤ m := by
  rw [numMissed_eq_total_sub_numHit ρ]
  apply Nat.sub_le

theorem Fin.numHit_le_total (ρ : Fin n → Fin m)
  : numHit ρ ≤ m := by
  rw [numHit_eq_total_sub_numMissed ρ]
  apply Nat.sub_le

theorem Fin.numMissedBefore_surjective {ρ : Fin n → Fin m} (hρ : Function.Surjective ρ) (k : ℕ)
  : numMissedBefore ρ k = k - m := by induction k with
  | zero => simp [numMissedBefore]
  | succ k I =>
    simp only [numMissedBefore, I]
    if h : k < m then
      rw [ite_cond_eq_true]
      rw [Nat.sub_eq_zero_of_le h, Nat.sub_eq_zero_of_le (Nat.le_of_lt h)]
      rw [eq_iff_iff, iff_true]
      have ⟨i, hi⟩ := hρ ⟨k, h⟩
      exact ⟨i, val_eq_of_eq hi⟩
    else
      rw [ite_cond_eq_false, Nat.one_add, Nat.succ_sub (Nat.le_of_not_lt h)]
      rw [eq_iff_iff, iff_false]
      intro ⟨i, hi⟩
      cases hi
      exact h (ρ i).prop

theorem Fin.numMissed_surjective {ρ : Fin n → Fin m} (hρ : Function.Surjective ρ)
  : numMissed ρ = 0 := by simp [numMissed, numMissedBefore_surjective hρ]

theorem Fin.numHit_surjective {ρ : Fin n → Fin m} (hρ : Function.Surjective ρ)
  : numHit ρ = m := by simp [numHit_eq_total_sub_numMissed, numMissed_surjective hρ]

theorem Fin.numMissedBefore_cast_succ_below (ρ : Fin (n + 1) → Fin m) (k : ℕ) (hk : k ≤ ρ 0)
  : numMissedBefore (ρ ∘ Fin.succ) k = numMissedBefore ρ k
  := by induction k with
  | zero => rfl
  | succ k I =>
    simp only [numMissedBefore, I (Nat.le_of_succ_le hk)]
    apply congrFun
    apply congrArg
    congr 1
    simp only [Function.comp_apply, eq_iff_iff]
    exact ⟨
      λ⟨i, hi⟩ => ⟨i.succ, hi⟩,
      λ⟨i, hi⟩ => ⟨
        i.pred (λh => by cases h; cases hi; exact Nat.not_succ_le_self _ hk),
        by simp [hi]⟩⟩

theorem Fin.numMissedBefore_cast_succ_above (ρ : Fin (n + 1) → Fin m) (k : ℕ)
  (hρ : ∀⦃i⦄, ρ 0 = ρ i -> 0 = i) (hk : ρ 0 < k)
  : numMissedBefore (ρ ∘ Fin.succ) k = numMissedBefore ρ k + 1
  := by induction k with
  | zero => cases hk
  | succ k I =>
    simp only [numMissedBefore]
    if h : ρ 0 = k then
      cases h
      rw [numMissedBefore_cast_succ_below ρ _ (le_refl _), ite_cond_eq_false, ite_cond_eq_true]
      . simp_arith
      . rw [eq_iff_iff, iff_true]
        exact ⟨0, rfl⟩
      . simp only [Function.comp_apply, eq_iff_iff, iff_false, not_exists]
        intro i hi
        cases hρ (Fin.eq_of_val_eq hi.symm)
    else
      have he : (∃i, ρ i = k) ↔ ∃i : Fin n, ρ i.succ = k := ⟨
        λ⟨i, hi⟩ => ⟨i.pred (λhi' => by simp [<-hi, hi'] at h), by simp [hi]⟩,
        λ⟨i, hi⟩ => ⟨i.succ, hi⟩⟩
      simp_arith [he, I (Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hk) h)]

theorem Fin.numMissed_cast_succ (ρ : Fin (n + 1) → Fin m) (h : ∀⦃i⦄, ρ 0 = ρ i -> 0 = i)
  : numMissed (ρ ∘ Fin.succ) = numMissed ρ + 1
  := numMissedBefore_cast_succ_above ρ m h ((ρ 0).prop)

theorem Fin.numMissed_injective {ρ : Fin n → Fin m} (hρ : Function.Injective ρ)
  : numMissed ρ = m - n := by induction n with
  | zero => simp
  | succ n I =>
    have I := I (hρ.comp (Fin.succ_injective n))
    rw [numMissed_cast_succ] at I
    rw [Nat.sub_succ]
    exact (Nat.pred_eq_of_eq_succ I.symm).symm
    apply hρ

theorem Fin.le_of_injective {ρ : Fin n → Fin m} (hρ : Function.Injective ρ)
  : n ≤ m := by
  have h := Fintype.card_le_of_injective _ hρ;
  simp only [Fintype.card_fin] at h
  exact h

theorem Fin.le_of_surjective {ρ : Fin n → Fin m} (hρ : Function.Surjective ρ)
  : m ≤ n := by
  have h := Fintype.card_le_of_surjective _ hρ;
  simp only [Fintype.card_fin] at h
  exact h

theorem Fin.numHit_injective {ρ : Fin n → Fin m} (hρ : Function.Injective ρ)
  : numHit ρ = n := by
  rw [
    numHit_eq_total_sub_numMissed,
    numMissed_injective hρ,
    Nat.sub_sub_self (le_of_injective hρ)]

theorem Fin.numMissed_injective_add_source {ρ : Fin n → Fin m} (hρ : Function.Injective ρ)
    : numMissed ρ + n = m := by
  apply Eq.trans _ (numMissed_add_numHit ρ)
  rw [numHit_injective hρ]

def Fin.lastHitBefore (ρ : Fin n → Fin m) (k : ℕ) : ℕ → ℕ
  | 0 => Fin.numMissedBefore ρ k + n
  | a + 1 =>
    if ha : a < n then
      if ρ ⟨a, ha⟩ = k then a
      else lastHitBefore ρ k a
    else
      lastHitBefore ρ k a

@[simp]
theorem Fin.lastHitBefore_zero (ρ : Fin n → Fin m) (k : ℕ)
  : lastHitBefore ρ k 0 = numMissedBefore ρ k + n := rfl

theorem Fin.lastHitBefore_le_numMissedBefore_add_n (ρ : Fin n → Fin m) (k : ℕ) (i)
  : lastHitBefore ρ k i ≤ numMissedBefore ρ k + n := by induction i with
  | zero => simp
  | succ i I =>
    simp only [lastHitBefore]
    split
    case isTrue h =>
      split
      . exact (Nat.le_of_lt h).trans (Nat.le_add_left _ _)
      . exact I
    case _ => exact I

def Fin.lastHit (ρ : Fin n → Fin m) (k : ℕ) : ℕ
  := lastHitBefore ρ k n

theorem Fin.lastHit_le_numMissed_add_n (ρ : Fin n → Fin m) (k : ℕ) (hk : k ≤ m)
  : lastHit ρ k ≤ numMissed ρ + n := by
  rw [lastHit, numMissed]
  apply (lastHitBefore_le_numMissedBefore_add_n ρ k n).trans
  rw [Nat.add_le_add_iff_right]
  apply numMissedBefore_mono
  exact hk


theorem Fin.lastHitBefore_of_hit (ρ : Fin n → Fin m) (k : ℕ) (i : Fin n) (hi : ρ i = k)
  : lastHitBefore ρ k (↑i + 1) = i := by simp [lastHitBefore, hi]

theorem Fin.lastHitBefore_lt_of_hit (ρ : Fin n → Fin m) (k : ℕ) (i : Fin n) (hi : ρ i = k) (j : ℕ)
  (hj : i < j) : lastHitBefore ρ k j < n := by induction hj with
  | refl => simp [lastHitBefore_of_hit ρ k i hi]
  | step h I =>
    simp only [lastHitBefore]
    repeat first | assumption | split

theorem Fin.lastHit_lt_of_hit (ρ : Fin n → Fin m) (k : ℕ) (h : ∃i, ρ i = k) : lastHit ρ k < n :=
  have ⟨i, hi⟩ := h;
  lastHitBefore_lt_of_hit ρ k i hi n i.prop

theorem Fin.lastHitBefore_of_not_hit (ρ : Fin n → Fin m) (k : ℕ) (a : ℕ) (h : ¬∃i, ρ i = k)
  : lastHitBefore ρ k a = Fin.numMissedBefore ρ k + n := by
  induction a with
  | zero => rfl
  | succ n I =>
    simp only [lastHitBefore]
    split
    split
    case isTrue h' => exact (h ⟨_, h'⟩).elim
    assumption
    assumption

theorem Fin.lastHit_of_not_hit (ρ : Fin n → Fin m) (k : ℕ) (h : ¬∃i, ρ i = k)
  : lastHit ρ k = Fin.numMissedBefore ρ k + n := lastHitBefore_of_not_hit ρ k n h

theorem Fin.lastHit_lt_numMissed_add_src (ρ : Fin n → Fin m) (k : ℕ) (hk : k < m)
  : lastHit ρ k < numMissed ρ + n := by
  if h : ∃i, ρ i = k then
    exact Nat.lt_of_lt_of_le (lastHit_lt_of_hit ρ k h) (Nat.le_add_left _ _)
  else
    rw [lastHit_of_not_hit _ _ h, numMissed, Nat.add_lt_add_iff_right]
    apply Nat.lt_of_lt_of_le _ (numMissedBefore_mono ρ hk)
    simp [numMissedBefore, h]

theorem Fin.lastHit_lt_src_add_numMissed_add (ρ : Fin n → Fin m) (k : ℕ) (hk : k < m)
  : lastHit ρ k < n + numMissed ρ := by
  rw [Nat.add_comm]
  exact lastHit_lt_numMissed_add_src ρ k hk

def Fin.missedInv (ρ : Fin n → Fin m) (i : Fin m) : Fin (n + numMissed ρ)
  := ⟨lastHit ρ i, lastHit_lt_src_add_numMissed_add ρ i i.prop⟩

theorem Fin.lastHit_lt_target {ρ : Fin n → Fin m} (hρ : Function.Injective ρ) (k : ℕ) (hk : k < m)
  : lastHit ρ k < m := by
  have h := lastHit_lt_numMissed_add_src ρ k hk;
  rw [numMissed_injective_add_source hρ] at h
  exact h

def Fin.semiInv {ρ : Fin n → Fin m} (hρ : Function.Injective ρ) (i : Fin m) : Fin m
  := ⟨lastHit ρ i, lastHit_lt_target hρ i i.prop⟩

@[simp]
theorem Fin.cast_comp_missedInv {ρ : Fin n → Fin m} (hρ : Function.Injective ρ)
  : cast (by rw [Nat.add_comm, numMissed_injective_add_source hρ]) ∘ missedInv ρ = semiInv hρ
  := rfl

@[simp]
theorem Fin.cast_comp_semiInv {ρ : Fin n → Fin m} (hρ : Function.Injective ρ)
  : cast (by rw [Nat.add_comm, numMissed_injective_add_source hρ]) ∘ semiInv hρ = missedInv ρ
  := rfl

def Fin.missedBelow (ρ : Fin n → Fin m) (i : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 =>
    if ∃j, ρ j = k then
      missedBelow ρ i k
    else match i with
    | 0 => k
    | i + 1 => missedBelow ρ i k

theorem Fin.missedBelow_le (ρ : Fin n → Fin m) (i k : ℕ)
  : missedBelow ρ i k ≤ k := by induction k generalizing i with
  | zero => rfl
  | succ k I =>
    simp only [missedBelow]
    split
    exact (I i).trans (Nat.le_succ _)
    split
    exact Nat.le_succ _
    exact (I _).trans (Nat.le_succ _)

theorem Fin.missedBelow_le_of_le (ρ : Fin n → Fin m) (i k : ℕ) (h : k ≤ m)
  : missedBelow ρ i k ≤ m := (missedBelow_le ρ i k).trans h

theorem Fin.missedBelow_lt_of_ne (ρ : Fin n → Fin m) (i k : ℕ) (hk : k ≠ 0)
  : missedBelow ρ i k < k := by cases k with
  | zero => cases hk rfl
  | succ k =>
    simp only [missedBelow]
    split
    exact Nat.lt_of_le_of_lt (missedBelow_le ρ i k) (Nat.lt_succ_self _)
    split
    exact Nat.lt_succ_self _
    exact Nat.lt_of_le_of_lt (missedBelow_le ρ _ k) (Nat.lt_succ_self _)

theorem Fin.missedBelow_bounded (ρ : Fin n → Fin m) (i k : ℕ) (hi : i < numMissed ρ) (hk : k ≤ m)
  : missedBelow ρ i k < m := by induction k generalizing i with
  | zero =>
    apply Nat.lt_of_le_of_lt (Nat.zero_le i)
    apply Nat.lt_of_lt_of_le hi
    apply numMissed_le_total
  | succ k I =>
    simp only [missedBelow]
    split
    apply I
    exact hi
    exact Nat.le_of_succ_le hk
    split
    exact hk
    apply I
    exact Nat.lt_of_succ_lt hi
    exact Nat.le_of_succ_le hk

theorem Fin.missedBelow_not_hit
  (ρ : Fin n → Fin m) (i k : ℕ) (hi : i < numMissedBefore ρ k)
  : ¬∃j, ρ j = missedBelow ρ i k := by induction k generalizing i with
  | zero => cases hi
  | succ k I =>
    simp only [missedBelow]
    split
    case isTrue hj =>
      apply I
      simp only [numMissedBefore, hj, ↓reduceIte, zero_add] at hi
      exact hi
    case isFalse hj =>
      split
      exact hj
      apply I
      exact Nat.lt_of_succ_lt_succ $ Nat.lt_of_lt_of_le hi (numMissedBefore_le_succ ρ k)

def Fin.missed (ρ : Fin n → Fin m) (i : Fin (numMissed ρ)) : Fin m
  := ⟨missedBelow ρ i.rev m, missedBelow_bounded ρ i.rev m i.rev.prop (le_refl m)⟩

theorem Fin.missed_not_hit (ρ : Fin n → Fin m) (i : Fin (numMissed ρ))
  : ¬∃j, ρ j = (missed ρ i : ℕ) := missedBelow_not_hit ρ i.rev m i.rev.prop

-- theorem Fin.numMissedBefore_missedBelow (ρ : Fin n → Fin m) (i) (hi : i < numMissed ρ)
--   : numMissedBefore ρ (missedBelow ρ i k) = numMissedBefore ρ k - (i + 1) := by induction k with
--   | zero => simp [missedBelow]
--   | succ k I =>
--     simp only [numMissedBefore, missedBelow]
--     split
--     case isTrue h => simp [I]
--     case isFalse h =>
--     induction i with
--     | zero => simp
--     | succ i I2 =>
--       simp only
--       rw [Nat.add_comm 1]
--       simp only [Nat.reduceSubDiff]
--       have I2 := I2 (Nat.lt_of_succ_lt hi)
--       rw [<-I2]

-- theorem Fin.numMissedBefore_missedBelow' (ρ : Fin n → Fin m) (i : Fin (numMissed ρ))
--   : numMissedBefore ρ (missedBelow ρ i m) = i.rev
--   := by simp [numMissedBefore_missedBelow, numMissed]

-- theorem Fin.numMissedBefore_missed (ρ : Fin n → Fin m) (i : Fin (numMissed ρ))
--   : numMissedBefore ρ (missed ρ i) = i := by rw [missed, numMissedBefore_missedBelow', Fin.rev_rev]

-- theorem Fin.missedInv_missed (ρ : Fin n → Fin m) (i : Fin (numMissed ρ))
--   : missedInv ρ (missed ρ i) = i.natAdd n := by
--   simp only [missedInv, natAdd, mk.injEq]
--   rw [Nat.add_comm n, lastHit_of_not_hit, add_left_inj]
--   apply numMissedBefore_missed
--   apply missed_not_hit
