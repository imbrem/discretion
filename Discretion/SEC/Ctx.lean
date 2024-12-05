-- import Mathlib.CategoryTheory.Monoidal.Free.Basic
-- import Mathlib.Order.CompleteBooleanAlgebra
-- import Mathlib.Data.Fintype.Order

-- import Discretion.Vector.Basic

-- open Mathlib

-- open CategoryTheory.MonoidalCategory

-- namespace SEC

-- local notation "Ty" => CategoryTheory.FreeMonoidalCategory

-- local notation "tyOf" => CategoryTheory.FreeMonoidalCategory.of

-- def Ctx (τ : Type _) := List τ

-- @[match_pattern]
-- def Ctx.nil {τ} : Ctx τ := []

-- @[match_pattern]
-- def Ctx.cons {τ} (Γ : Ctx τ) (A : τ) : Ctx τ := A :: Γ

-- infixr:67 " ;; " => Ctx.cons

-- inductive Nat.Split : ℕ → ℕ → ℕ → Type where
--   | nil : Split 0 0 0
--   | both {n m k} (ρ : Split n m k) : Split (n + 1) (m + 1) (k + 1)
--   | left {n m k} (ρ : Split n m k) : Split (n + 1) (m + 1) k
--   | right {n m k} (ρ : Split n m k) : Split (n + 1) m (k + 1)
--   | skip {n m k} (ρ : Split n m k) : Split (n + 1) m k

-- def Nat.Wk (n m : ℕ) := Nat.Split n 0 m

-- -- TODO: and friends... but also, just a Wk pair might work? might even be cleaner?

-- inductive Ctx.Split {τ} : Ctx τ → Ctx τ → Ctx τ → Type where
--   | nil : Split [] [] []
--   | both (ρ : Split Γ Δ Ξ) (A) : Split (Γ ;; A) (Δ ;; A) (Ξ ;; A)
--   | left (ρ : Split Γ Δ Ξ) (A) : Split (Γ ;; A) (Δ ;; A) Ξ
--   | right (ρ : Split Γ Δ Ξ) (A) : Split (Γ ;; A) Δ (Ξ ;; A)
--   | skip (ρ : Split Γ Δ Ξ) (A) : Split (Γ ;; A) Δ Ξ

-- theorem Ctx.Split.length_left_le {τ} {Γ Δ Ξ : Ctx τ}
--   (ρ : Γ.Split Δ Ξ) : Δ.length ≤ Γ.length := by
--   induction ρ <;> simp only [cons, List.length_cons, List.length_nil] <;> omega

-- theorem Ctx.Split.length_right_le {τ} {Γ Δ Ξ : Ctx τ}
--   (ρ : Γ.Split Δ Ξ) : Ξ.length ≤ Γ.length := by
--   induction ρ <;> simp only [cons, List.length_cons, List.length_nil] <;> omega

-- def Ctx.Wk {τ} (Γ : Ctx τ) (Δ : Ctx τ) := Ctx.Split Γ [] Δ

-- @[match_pattern]
-- def Ctx.Wk.nil : Ctx.Wk (τ := τ) [] [] := Ctx.Split.nil

-- @[match_pattern]
-- def Ctx.Wk.skip (ρ : Γ.Wk Δ) (A) : Ctx.Wk (Γ ;; A) Δ := Ctx.Split.skip ρ A

-- @[match_pattern]
-- def Ctx.Wk.cons (ρ : Γ.Wk Δ) (A) : Ctx.Wk (Γ ;; A) (Δ ;; A) := Ctx.Split.right ρ A

-- @[elab_as_elim, induction_eliminator]
-- def Ctx.Wk.inductionOn {τ}
--   {motive : ∀{Γ Δ}, Ctx.Wk Γ Δ → Sort _}
--   (nil : motive Ctx.Wk.nil)
--   (skip : ∀(Γ Δ : Ctx τ) (ρ : Γ.Wk Δ) (A), motive ρ → motive (Ctx.Wk.skip ρ A))
--   (cons : ∀(Γ Δ : Ctx τ) (ρ : Γ.Wk Δ) (A), motive ρ → motive (Ctx.Wk.cons ρ A))
--   {Γ Δ : Ctx τ} : ∀ρ : Γ.Wk Δ, motive ρ
--   | .nil => nil
--   | .skip ρ a => skip _ _ ρ a (inductionOn nil skip cons ρ)
--   | .cons ρ a => cons _ _ ρ a (inductionOn nil skip cons ρ)


-- -- TODO: dc/q/c are monotone, join/meet preserving, etc

-- inductive Ctx.Split.WQ {τ}
--   : ∀{Γ Δ Ξ : Ctx τ}, Γ.Split Δ Ξ
--     → Vector' Quant Γ.length
--     → Vector' Quant Δ.length
--     → Vector' Quant Ξ.length → Prop
--   | nil : WQ Split.nil Vector'.nil Vector'.nil Vector'.nil
--   | both {ρ : Split Γ Δ Ξ} (h : WQ ρ qΓ qΔ qΞ) (A) (q q' q'')
--     : q.is_copy → q ≥ q' → q ≥ q'' → WQ (Split.both ρ A) (qΓ.cons q) (qΔ.cons q') (qΞ.cons q'')
--   | left {ρ : Split Γ Δ Ξ} (h : WQ ρ qΓ qΔ qΞ) (A) (q q')
--     : q ≥ q' → WQ (Split.left ρ A) (qΓ.cons q) (qΔ.cons q') qΞ
--   | right {ρ : Split Γ Δ Ξ} (h : WQ ρ qΓ qΔ qΞ) (A) (q q')
--     : q ≥ q' → WQ (Split.right ρ A) (qΓ.cons q) qΔ (qΞ.cons q')
--   | skip {ρ : Split Γ Δ Ξ} (h : WQ ρ qΓ qΔ qΞ) (A) (q)
--     : q.is_del → WQ (Split.skip ρ A) (qΓ.cons q) qΔ qΞ

-- theorem Ctx.Split.WQ.le_congr
--   {τ} {Γ Δ Ξ : Ctx τ} {ρ : Γ.Split Δ Ξ} {qΓ qΔ qΞ} {qΓ' qΔ' qΞ'}
--   (h : WQ ρ qΓ qΔ qΞ) (hΓ : qΓ ≤ qΓ') (hΔ : qΔ' ≤ qΔ) (hΞ : qΞ' ≤ qΞ)
--   : WQ ρ qΓ' qΔ' qΞ' := by
--   induction h with
--   | nil => cases qΓ'; cases qΔ'; cases qΞ'; constructor
--   | both _ _ _ _ _ hd hxy hxz I =>
--     cases hΓ; cases hΔ; cases hΞ
--     constructor
--     apply I <;> assumption
--     apply Quant.is_copy_mono _ hd
--     assumption
--     apply le_trans _ (le_trans hxy _) <;> assumption
--     apply le_trans _ (le_trans hxz _) <;> assumption
--   | left _ _ _ _ hxy I =>
--     cases hΓ; cases hΔ;
--     constructor
--     apply I <;> assumption
--     apply le_trans _ (le_trans hxy _) <;> assumption
--   | right _ _ _ _ hxy I =>
--     cases hΓ; cases hΞ;
--     constructor
--     apply I <;> assumption
--     apply le_trans _ (le_trans hxy _) <;> assumption
--   | skip _ _ _ hd I =>
--     cases hΓ
--     constructor
--     apply I <;> assumption
--     apply Quant.is_del_mono _ hd
--     assumption

-- inductive Ctx.Split.Q {τ}
--   : ∀{Γ Δ Ξ : Ctx τ}, Γ.Split Δ Ξ
--     → Vector' Quant Γ.length
--     → Vector' Quant Δ.length
--     → Vector' Quant Ξ.length → Prop
--   | nil : Q Split.nil Vector'.nil Vector'.nil Vector'.nil
--   | both {ρ : Split Γ Δ Ξ} (h : Q ρ qΓ qΔ qΞ) (A) (q)
--     : q.is_copy → Q (Split.both ρ A) (qΓ.cons q) (qΔ.cons q) (qΞ.cons q)
--   | left {ρ : Split Γ Δ Ξ} (h : Q ρ qΓ qΔ qΞ) (A) (q)
--     : Q (Split.left ρ A) (qΓ.cons q) (qΔ.cons q) qΞ
--   | right {ρ : Split Γ Δ Ξ} (h : Q ρ qΓ qΔ qΞ) (A) (q)
--     : Q (Split.right ρ A) (qΓ.cons q) qΔ (qΞ.cons q)
--   | skip {ρ : Split Γ Δ Ξ} (h : Q ρ qΓ qΔ qΞ) (A) (q)
--     : q.is_del → Q (Split.skip ρ A) (qΓ.cons q) qΔ qΞ

-- theorem Ctx.Split.Q.toWQ {τ} {Γ Δ Ξ : Ctx τ} {ρ : Γ.Split Δ Ξ}
--   {qΓ qΔ qΞ} (h : Q ρ qΓ qΔ qΞ) : WQ ρ qΓ qΔ qΞ := by induction h <;> constructor <;> simp [*]

-- inductive Ctx.Split.WV {τ} {ε} [LE ε]
--   : ∀{Γ Δ Ξ : Ctx τ}, Γ.Split Δ Ξ
--     → Vector' ε Γ.length
--     → Vector' ε Δ.length
--     → Vector' ε Ξ.length → Prop
--   | nil : WV Split.nil Vector'.nil Vector'.nil Vector'.nil
--   | both {ρ : Split Γ Δ Ξ} (h : WV ρ qΓ qΔ qΞ) (A) (q q' q'')
--     : q ≤ q' → q' ≤ q'' → WV (Split.both ρ A) (qΓ.cons q) (qΔ.cons q') (qΞ.cons q'')
--   | left {ρ : Split Γ Δ Ξ} (h : WV ρ qΓ qΔ qΞ) (A) (q q')
--     : q ≤ q' → WV (Split.left ρ A) (qΓ.cons q) (qΔ.cons q') qΞ
--   | right {ρ : Split Γ Δ Ξ} (h : WV ρ qΓ qΔ qΞ) (A) (q q')
--     : q ≤ q' → WV (Split.right ρ A) (qΓ.cons q) qΔ (qΞ.cons q')
--   | skip {ρ : Split Γ Δ Ξ} (h : WV ρ qΓ qΔ qΞ) (A) (q)
--     : WV (Split.skip ρ A) (qΓ.cons q) qΔ qΞ

-- def Ctx.Split.leftV {τ ε} {Γ Δ Ξ : Ctx τ}
--   : Γ.Split Δ Ξ → Vector' ε Γ.length → Vector' ε Δ.length
--   | .nil, .nil => .nil
--   | .both ρ _, .cons a v
--   | .left ρ _, .cons a v => (ρ.leftV v).cons a
--   | .right ρ _, .cons a v
--   | .skip ρ _, .cons a v => ρ.leftV v

-- def Ctx.Split.rightV {τ ε} {Γ Δ Ξ : Ctx τ}
--   : Γ.Split Δ Ξ → Vector' ε Γ.length → Vector' ε Ξ.length
--   | .nil, .nil => .nil
--   | .both ρ _, .cons a v
--   | .right ρ _, .cons a v => (ρ.rightV v).cons a
--   | .left ρ _, .cons a v
--   | .skip ρ _, .cons a v => ρ.rightV v

-- inductive Ctx.Split.V {τ} {ε}
--   : ∀{Γ Δ Ξ : Ctx τ}, Γ.Split Δ Ξ
--     → Vector' ε Γ.length
--     → Vector' ε Δ.length
--     → Vector' ε Ξ.length → Prop
--   | nil : V Split.nil Vector'.nil Vector'.nil Vector'.nil
--   | both {ρ : Split Γ Δ Ξ} (h : V ρ qΓ qΔ qΞ) (A) (q)
--     : V (Split.both ρ A) (qΓ.cons q) (qΔ.cons q) (qΞ.cons q)
--   | left {ρ : Split Γ Δ Ξ} (h : V ρ qΓ qΔ qΞ) (A) (q)
--     : V (Split.left ρ A) (qΓ.cons q) (qΔ.cons q) qΞ
--   | right {ρ : Split Γ Δ Ξ} (h : V ρ qΓ qΔ qΞ) (A) (q)
--     : V (Split.right ρ A) (qΓ.cons q) qΔ (qΞ.cons q)
--   | skip {ρ : Split Γ Δ Ξ} (h : V ρ qΓ qΔ qΞ) (A) (q)
--     : V (Split.skip ρ A) (qΓ.cons q) qΔ qΞ

-- theorem Ctx.Split.V.toWV {τ ε} [Preorder ε] {Γ Δ Ξ : Ctx τ} {ρ : Γ.Split Δ Ξ}
--   {qΓ qΔ qΞ} (h : V (ε := ε) ρ qΓ qΔ qΞ) : WV ρ qΓ qΔ qΞ
--   := by induction h <;> constructor <;> simp [*]
