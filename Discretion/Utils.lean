import Mathlib.Data.Set.Function
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.List.Basic

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
  := eqOn_comp_left_iff_of_injOn_image (injOn_of_injective hf _)

theorem Fin.foldl_eq_foldr {α} {f : α → α → α} (hcomm : Commutative f) (hassoc : Associative f)
  (x : α) (xs : Fin n → α)
  : foldl n (λa i => f a (xs i)) x = foldr n (λi a => f (xs i) a) x := by
  rw [
    foldr_eq_foldr_list, foldl_eq_foldl_list,
    <-List.foldl_map, <-List.foldr_map,
    List.foldl_eq_foldr hcomm hassoc
  ]

-- TODO: foldl_eq_foldr'...

def Fin.maxD [Max α] (f : Fin n → α) (b : α) := Fin.foldr _ (λi v => max (f i) v) b

@[simp]
theorem Fin.maxD_zero [Max α] (f : Fin 0 → α) (b : α) : maxD f b = b := rfl

theorem Fin.maxD_succ [Max α] (f : Fin (n+1) → α) (b : α)
  : maxD f b = max (f 0) (maxD (f ∘ Fin.succ) b)  := by simp [maxD, Fin.foldr_succ]

theorem Fin.maxD_succ' [LinearOrder α] (f : Fin (n+1) → α) (b : α)
    : maxD f b = maxD (f ∘ Fin.succ) (max b (f 0)) := by
  simp [maxD, <-foldl_eq_foldr max_commutative max_associative, Fin.foldl_succ]

theorem Fin.base_le_maxD [LinearOrder α] (f : Fin n → α) (b : α)
  : b ≤ maxD f b := by induction n generalizing b with
  | zero => rfl
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
  | zero => exact λ_ hb => hb
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

-- TODO: can do likewise for min, inf, and sup

-- TODO: move to Tuple?

-- TODO: do Finset-style max'?
