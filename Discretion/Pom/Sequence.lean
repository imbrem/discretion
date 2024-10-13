import Discretion.Pom.FiniteHeight

structure GPoseq (α : Type u) where
  actions : ℕ → α
  order : PartialOrder ℕ

structure Poseq (α : Type u) extends GPoseq α where
  finite_height : FiniteHeight ℕ (p := order.toPreorder)
