import Mathlib.Order.CompleteLattice.Basic

open Classical

theorem Set.not_subset_singleton {α} {a : α} {s : Set α} : ¬s ⊆ {a} ↔ ∃b ∈ s, b ≠ a := by
  simp only [Set.subset_singleton_iff, Set.mem_singleton_iff, not_forall, exists_prop]

noncomputable instance {α} [CompleteSemilatticeSup α] : CompleteSemilatticeSup (WithTop α) where
  sSup as := if ⊤ ∈ as then ⊤ else sSup (α := α) (WithTop.some ⁻¹' as)
  le_sSup as x hx := by
    simp only [sSup]; split; simp; cases x; contradiction; rw [WithTop.coe_le_coe]
    exact le_sSup hx
  sSup_le as x hx a ha := by
    cases ha
    have has : ⊤ ∉ as := λc => by have hc := hx _ c; simp at hc
    simp only [sSup, has, ↓reduceIte, WithTop.coe_eq_coe, exists_eq_left', sSup_le_iff,
      Set.mem_preimage]
    intro b hb; convert hx b hb; simp

noncomputable instance {α} [CompleteSemilatticeInf α] : CompleteSemilatticeInf (WithTop α) where
  sInf as := if as ⊆ {⊤} then ⊤ else sInf (α := α) (WithTop.some ⁻¹' as)
  le_sInf as x hx := by
    simp only [sInf]
    split
    case isTrue => simp
    case isFalse h =>
      rw [Set.not_subset_singleton] at h
      have ⟨b, hb, hb'⟩ := h
      cases b with
      | top => contradiction
      | coe b => cases x with
      | top => have h := hx _ hb; simp at h
      | coe a =>
        simp only [WithTop.coe_le_coe, le_sInf_iff, Set.mem_preimage]
        intro b hb; convert hx b hb; simp
  sInf_le as x hx := by
    simp only [sInf]
    split
    case isTrue h =>
      have hx := Set.mem_singleton_iff.mp <| h hx
      simp [hx]
    case isFalse h =>
      cases x with
      | top => simp
      | coe a =>
        simp only [WithTop.coe_le_coe]
        exact sInf_le hx

noncomputable instance {α} [CompleteLattice α] : CompleteLattice (WithTop α) where
  le_sSup := CompleteSemilatticeSup.le_sSup
  sSup_le := CompleteSemilatticeSup.sSup_le
  sInf_le := CompleteSemilatticeInf.sInf_le
  le_sInf := CompleteSemilatticeInf.le_sInf
  le_top := by simp
  bot_le := by simp

noncomputable instance {α} [CompleteSemilatticeSup α] : CompleteSemilatticeSup (WithBot α) where
  sSup as := if as ⊆ {⊥} then ⊥ else sSup (α := α) (WithBot.some ⁻¹' as)
  le_sSup as x hx := by
    simp only [sSup]
    split
    case isTrue h =>
      have hx := Set.mem_singleton_iff.mp <| h hx
      simp [hx]
    case isFalse h =>
      cases x with
      | bot => simp
      | coe a =>
        simp only [WithBot.coe_le_coe]
        exact le_sSup hx
  sSup_le as x hx := by
    simp only [sSup]
    split
    case isTrue h => simp
    case isFalse h =>
      rw [Set.not_subset_singleton] at h
      have ⟨b, hb, hb'⟩ := h
      cases b with
      | bot => contradiction
      | coe b => cases x with
      | bot => have h := hx _ hb; simp at h
      | coe a =>
        simp only [WithBot.coe_le_coe, sSup_le_iff, Set.mem_preimage]
        intro b hb; convert hx b hb; simp

noncomputable instance {α} [CompleteSemilatticeInf α] : CompleteSemilatticeInf (WithBot α) where
  sInf as := if ⊥ ∈ as then ⊥ else sInf (α := α) (WithBot.some ⁻¹' as)
  le_sInf as x hx a ha := by
    cases ha
    have has : ⊥ ∉ as := λc => by have hc := hx _ c; simp at hc
    simp only [sInf, has, ↓reduceIte, WithBot.coe_inj, exists_eq_left', le_sInf_iff,
      Set.mem_preimage]
    intro b hb; convert hx b hb; simp
  sInf_le as x hx := by
    simp only [sInf]; split; simp; cases x; contradiction; rw [WithBot.coe_le_coe]
    exact sInf_le hx

noncomputable instance {α} [CompleteLattice α] : CompleteLattice (WithBot α) where
  le_sSup := CompleteSemilatticeSup.le_sSup
  sSup_le := CompleteSemilatticeSup.sSup_le
  sInf_le := CompleteSemilatticeInf.sInf_le
  le_sInf := CompleteSemilatticeInf.le_sInf
  le_top := by simp
  bot_le := by simp
