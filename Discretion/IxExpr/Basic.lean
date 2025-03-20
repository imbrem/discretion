inductive IxExpr (α : Type u) : Type u
  | empty : IxExpr α
  | unit : IxExpr α
  | prod : IxExpr α → IxExpr α → IxExpr α
  | coprod : IxExpr α → IxExpr α → IxExpr α
  | of : α → IxExpr α

inductive SeqExpr (α : Type u) : Type u
  | empty : SeqExpr α
  | unit : SeqExpr α
  | prod : SeqExpr α → SeqExpr α → SeqExpr α
  | coprod : SeqExpr α → SeqExpr α → SeqExpr α
  | seq : (ℕ → SeqExpr α) → SeqExpr α
  | of : α → SeqExpr α
