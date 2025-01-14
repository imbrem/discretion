import Mathlib.Logic.Relation
import Mathlib.Combinatorics.Quiver.Path

-- TODO: start thinking about epis and monos
-- TODO: so... a natural extension of a correspondence is a bundled category then...

namespace Corr

section Basic

def Rel {α : Sort*} {β : Sort*} (r : α → β → Sort*) : α → β → Prop := λa b => Nonempty (r a b)

@[ext]
structure BimodHom (r : α → β → Sort v) (s : α' → β' → Sort w) where
  objIn : α → β → α'
  objOut : α → β → β'
  map : r a b → s (objIn a b) (objOut a b)

end Basic

namespace BimodHom

infixl:50 " ⥤C " => BimodHom

def id (r : α → β → Sort*) : BimodHom r r where
  objIn a _ := a
  objOut _ b := b
  map := _root_.id

notation "𝟭C" => id

def comp (F : BimodHom r s) (G : BimodHom s t) : BimodHom r t where
  objIn a b := G.objIn (F.objIn a b) (F.objOut a b)
  objOut a b := G.objOut (F.objIn a b) (F.objOut a b)
  map := G.map ∘ F.map

infixl:60 " ⋙C " => comp

@[simp]
theorem comp_id (F : r ⥤C s) : F ⋙C 𝟭C _ = F := rfl

@[simp]
theorem id_comp (F : r ⥤C s) : 𝟭C _ ⋙C F = F := rfl

theorem comp_assoc (F : r ⥤C s) (G : s ⥤C t) (H : t ⥤C u)
  : (F ⋙C G) ⋙C H = F ⋙C (G ⋙C H) := rfl

@[simp]
theorem objIn_comp (F : r ⥤C s) (G : s ⥤C t)
  : (F ⋙C G).objIn a b = G.objIn (F.objIn a b) (F.objOut a b) := rfl

@[simp]
theorem objOut_comp (F : r ⥤C s) (G : s ⥤C t)
  : (F ⋙C G).objOut a b = G.objOut (F.objIn a b) (F.objOut a b) := rfl

@[simp]
theorem map_comp (F : r ⥤C s) (G : s ⥤C t) (x : r a b)
  : (F ⋙C G).map x = G.map (F.map x) := rfl

-- theorem toLiftFun (F : r ⥤C s) : (Rel r ⇒ Rel s) F.objIn F.objOut := λ_ _ ⟨p⟩ => ⟨F.map p⟩

def IsAligned {r : α → α → Sort v} {s : β → β → Sort w} (F : r ⥤C s)
  : Prop := ∀a, F.objIn a a = F.objOut a a

theorem IsAligned.id (r : α → α → Sort*) : IsAligned (𝟭C r) := λ_ => rfl

theorem IsAligned.comp {F : r ⥤C s} {G : s ⥤C t} (hF : IsAligned F) (hG : IsAligned G)
  : IsAligned (F ⋙C G) := λa => by
    simp [objIn_comp, objOut_comp, hF a, hG (F.objOut a a)]

end BimodHom

def Op {α : Sort u} {β : Sort v} (r : α → β → Sort w) : β → α → Sort w := λb a => r a b

@[simp]
theorem op_op : Op (Op r) = r := rfl

@[simp]
theorem op_comp_op : Op ∘ Op = @id (α → β → Sort*) := rfl

def toOp : r a b → Op r b a := _root_.id

def toOpH (r : α → β → Sort*) : r ⥤C Op r where
  objIn _ a := a
  objOut b _ := b
  map := toOp

theorem toOpH_comp_toOpH (r : α → β → Sort*)
  : toOpH r ⋙C toOpH (Op r) = 𝟭C r := by
  ext
  . rfl
  . rfl
  . simp only [toOpH, BimodHom.objIn_comp, BimodHom.objOut_comp, heq_eq_eq]
    funext _ _ p
    rfl

def Sum (r : α → β → Type u) (s : α → β → Type v) : α → β → Type (max u v)
  := λa b => r a b ⊕ s a b

@[match_pattern]
def Sum.inl {r : α → β → Type*} {s : α → β → Type*} : r a b → Sum r s a b := _root_.Sum.inl

@[match_pattern]
def Sum.inr {r : α → β → Type*} {s : α → β → Type*} : s a b → Sum r s a b := _root_.Sum.inr

def Prod (r : α → β → Type u) (s : α → β → Type v) : α → β → Type (max u v)
  := λa b => r a b × s a b

inductive DSum {α : Type*} {β : Type*} (r : α → β → Type*) (s : α' → β' → Type*)
  : (α ⊕ α') → (β ⊕ β') → Type _
  | inl : r a b → DSum r s (_root_.Sum.inl a) (_root_.Sum.inl b)
  | inr : s a' b' → DSum r s (_root_.Sum.inr a') (_root_.Sum.inr b')

inductive DProd {α : Type*} {β : Type*} (r : α → β → Type*) (s : α' → β' → Type*)
  : (α × α') → (β × β') → Type _
  | mk : r a b → s a' b' → DProd r s (a, a') (b, b')

def Comp {α : Type*} {β : Type*} {γ : Type*} (r : α → β → Type*) (s : β → γ → Type*)
  : α → γ → Type _ := λa c => Σb, r a b × s b c

inductive Path.{u, v} {α : Type u} (r : α → α → Sort v) : α → α → Sort (max (u + 1) v)
  | nil (a) : Path r a a
  | cons : Path r a b → r b c → Path r a c

inductive SPath.{u, v} {α : Type u} (r : α → α → Sort v) : α → α → Sort (max (u + 1) v)
  | single : r a b → SPath r a b
  | cons : SPath r a b → r b c → SPath r a c

section Rel

variable {α : Type u} {r : α → α → Sort v}

-- TODO: this should not be necessary
set_option linter.unusedVariables false in
theorem Path.rel : Path r a b → Relation.ReflTransGen (Rel r) a b
  | nil _ => Relation.ReflTransGen.refl
  | cons p s => Relation.ReflTransGen.tail p.rel ⟨s⟩

theorem Path.of_rel (h : Relation.ReflTransGen (Rel r) a b) : Rel (Path r) a b := by
  induction h with
  | refl => exact ⟨nil _⟩
  | tail _ s ih => exact let ⟨p⟩ := ih; let ⟨s⟩ := s; ⟨cons p s⟩

theorem rel_path (r : α → α → Sort v) : Rel (Path r) = Relation.ReflTransGen (Rel r) := by
  ext a b
  constructor
  intro ⟨h⟩
  exact h.rel
  exact Path.of_rel

-- TODO: likewise for TransGen

end Rel

namespace Path

def single : r a b → Path r a b := cons (nil _)

def cast (ha : a = a') (hb : b = b') (p : Path r a b) : Path r a' b'
  := ha ▸ hb ▸ p

@[simp]
def cast_trg (p : Path r a b) (h : b = c) : Path r a c := cast rfl h p

@[simp]
def cast_src (h : a = b) (p : Path r b c) : Path r a c := cast h.symm rfl p

def of_eq (h : a = b) : Path r a b := cast_trg (nil a) h

@[simp]
theorem cast_of_eq (h : a = a') (h' : b = b') (h'' : a = b)
  : cast h h' (of_eq h'') = @of_eq _ _ _ r (h ▸ h' ▸ h'')
  := by cases h; cases h'; rfl

@[simp]
theorem cast_cast (ha : a = a') (hb : b = b') (ha' : a' = a'') (hb' : b' = b'') (p : Path r a b)
  : cast ha' hb' (cast ha hb p) = cast (ha ▸ ha') (hb ▸ hb') p
  := by cases ha; cases ha'; cases hb; cases hb'; rfl

@[simp]
theorem cast_nil {ha : a = b} {ha' : a = c}
  : cast ha ha' (@nil _ r a) = of_eq (ha.symm.trans ha') := by cases ha; rfl

theorem cast_cons {ha : a = a'} {hc : c = c'} {p : Path r a b} {s : r b c}
  : cast ha hc (cons p s) = cons (cast ha rfl p) (hc ▸ s)
  := by cases ha; cases hc; rfl

theorem cast_cons' {ha : a = a'} {hb : b = b'} {p : Path r a b} {s : r b' c}
 : cons (cast ha hb p) s = cast ha rfl (cons p (hb ▸ s))
  := by cases ha; cases hb; rfl

@[simp]
theorem cast_rfl (p : Path r a b) : cast rfl rfl p = p := rfl

theorem cast_trg_of_eq (h : a = b) (h' : b = c)
  : cast_trg (of_eq h) h' = (@of_eq _ _ _ r (h' ▸ h)) := by cases h; cases h'; rfl

theorem cast_trg_cast_trg (p : Path r a b) (h : b = c) (h' : c = d)
  : cast_trg (cast_trg p h) h' = cast_trg p (h ▸ h')
  := by cases h; cases h'; rfl

theorem cast_trg_rfl : cast_trg p rfl = p := rfl

theorem cast_src_of_eq (h : a = b) (h' : b = c)
  : cast_src h (of_eq h') = (@of_eq _ _ _ r (h ▸ h')) := by cases h; cases h'; rfl

theorem cast_src_cast_src (h : a = b) (h' : b = c) (p : Path r c d)
  : cast_src h (cast_src h' p) = cast_src (h ▸ h') p
  := by cases h; cases h'; rfl

theorem cast_src_rfl : cast_src rfl p = p := rfl

-- TODO: this should not be necessary
set_option linter.unusedVariables false in
def comp : Path r a b → Path r b c → Path r a c
  | p, nil _ => p
  | p, cons q s => cons (comp p q) s

@[simp]
theorem comp_nil (p : Path r a b) : comp p (nil _) = p := rfl

@[simp]
theorem comp_cons (p : Path r a b) (q : Path r b c) (s : r c d)
  : comp p (cons q s) = cons (comp p q) s := rfl

@[simp]
theorem nil_comp (p : Path r a b) : comp (nil _) p = p := by induction p with
  | nil => rfl
  | cons => simp [comp_cons, *]

theorem comp_assoc (p : Path r a b) (q : Path r b c) (s : Path r c d)
  : comp p (comp q s) = comp (comp p q) s := by induction s generalizing p <;> simp [*]

theorem cast_comp : cast ha hc (comp p q) = comp (cast ha hb p) (cast hb hc q)
  := by cases ha; cases hb; cases hc; rfl

def snoc (s : r a b) : Path r b c → Path r a c := comp (single s)

-- TODO: cast_snoc

instance pathTrans : Trans (Path r) (Path r) (Path r) where
  trans := comp

instance pathTransCorr : Trans (Path r) r (Path r) where
  trans := cons

instance corrTransPath : Trans r (Path r) (Path r) where
  trans := snoc

end Path

namespace SPath

variable {r : α → α → Sort v}

def cast (ha : a = a') (hb : b = b') (p : SPath r a b) : SPath r a' b'
  := ha ▸ hb ▸ p

@[simp]
def cast_trg (p : SPath r a b) (h : b = c) : SPath r a c := cast rfl h p

@[simp]
def cast_src (h : a = b) (p : SPath r b c) : SPath r a c := cast h.symm rfl p

@[simp]
theorem cast_cast (ha : a = a') (hb : b = b') (ha' : a' = a'') (hb' : b' = b'') (p : SPath r a b)
  : cast ha' hb' (cast ha hb p) = cast (ha ▸ ha') (hb ▸ hb') p
  := by cases ha; cases ha'; cases hb; cases hb'; rfl

theorem cast_single (ha : a = a') (hb : b = b') (s : r a b)
  : cast ha hb (single s) = single (ha ▸ hb ▸ s)
  := by cases ha; cases hb; rfl

theorem cast_cons {ha : a = a'} {hc : c = c'} {p : SPath r a b} {s : r b c}
  : cast ha hc (cons p s) = cons (cast ha rfl p) (hc ▸ s)
  := by cases ha; cases hc; rfl

theorem cast_cons' {ha : a = a'} {hb : b = b'} {p : SPath r a b} {s : r b' c}
 : cons (cast ha hb p) s = cast ha rfl (cons p (hb ▸ s))
  := by cases ha; cases hb; rfl

@[simp]
theorem cast_rfl (p : SPath r a b) : cast rfl rfl p = p := rfl

def comp : SPath r a b → SPath r b c → SPath r a c
  | p, single s => cons p s
  | p, cons q s => (comp p q).cons s

@[simp]
theorem comp_single (p : SPath r a b) (s : r b c) : comp p (single s) = cons p s := rfl

@[simp]
theorem comp_cons (p : SPath r a b) (q : SPath r b c) (s : r c d)
  : comp p (cons q s) = cons (comp p q) s := rfl

@[simp]
theorem comp_assoc (p : SPath r a b) (q : SPath r b c) (s : SPath r c d)
  : comp p (comp q s) = comp (comp p q) s := by induction s generalizing p <;> simp [*]

@[simp]
theorem cast_comp : cast ha hc (comp p q) = comp (cast ha hb p) (cast hb hc q)
  := by cases ha; cases hb; cases hc; rfl

def snoc (s : r a b) : SPath r b c → SPath r a c := comp (single s)

@[simp]
def toPath : SPath r a b → Path r a b
  | single s => Path.single s
  | cons p s => Path.cons p.toPath s

theorem toPath_single (s : r a b) : (single s).toPath = Path.single s := rfl

theorem toPath_cons (p : SPath r a b) (s : r b c) : (cons p s).toPath = Path.cons p.toPath s := rfl

-- theorem toPath_comp (p : SPath r a b) (q : SPath r b c)
--   : (comp p q).toPath = Path.comp p.toPath q.toPath := by
--   induction q generalizing p <;> simp [Path.comp, *]

-- theorem toPath_snoc (s : r a b) (p : SPath r b c) : (snoc s p).toPath = p.toPath.snoc s
--   := by simp [snoc, toPath_comp, Path.snoc]

-- end SPath

-- @[ext]
-- structure Prefunctor (r : α → α → Sort v) (s : β → β → Sort w) where
--   obj : α → β
--   map : r a b → s (obj a) (obj b)

-- namespace Prefunctor

-- infixl:50 " ⥤Q " => Prefunctor

-- def id (r : α → α → Sort v) : Prefunctor r r where
--   obj := _root_.id
--   map := _root_.id

-- notation "𝟭Q" => id

-- @[simp]
-- theorem obj_id (r : α → α → Sort v) : (𝟭Q r).obj = _root_.id := rfl

-- @[simp]
-- theorem map_id (r : α → α → Sort v) (x : r a b) : (𝟭Q r).map x = x := rfl

-- def comp (F : Prefunctor r s) (G : Prefunctor s t) : Prefunctor r t where
--   obj := G.obj ∘ F.obj
--   map := G.map ∘ F.map

-- infixl:60 " ⋙Q " => comp

-- @[simp]
-- theorem comp_id (F : r ⥤Q s) : F ⋙Q 𝟭Q s = F := rfl

-- @[simp]
-- theorem id_comp (F : r ⥤Q s) : 𝟭Q r ⋙Q F = F := rfl

-- theorem comp_assoc (F : r ⥤Q s) (G : s ⥤Q t) (H : t ⥤Q u)
--   : (F ⋙Q G) ⋙Q H = F ⋙Q (G ⋙Q H) := rfl

-- @[simp]
-- theorem obj_comp (F : r ⥤Q s) (G : s ⥤Q t) : (F ⋙Q G).obj = G.obj ∘ F.obj := rfl

-- @[simp]
-- theorem map_comp (F : r ⥤Q s) (G : s ⥤Q t) (x : r a b)
--   : (F ⋙Q G).map x = G.map (F.map x) := rfl

-- theorem toLiftFun (F : r ⥤Q s) : (Rel r ⇒ Rel s) F.obj F.obj := λ_ _ ⟨p⟩ => ⟨F.map p⟩

-- def toBimodHom (F : r ⥤Q s) : r ⥤C s where
--   objIn a _ := F.obj a
--   objOut _ b := F.obj b
--   map := F.map

-- instance coeToBimodHom : Coe (r ⥤Q s) (r ⥤C s) := ⟨toBimodHom⟩

-- @[simp]
-- def coe_id : ↑(𝟭Q r) = (𝟭C r) := rfl

-- @[simp]
-- def coe_comp (F : r ⥤Q s) (G : s ⥤Q t) : ↑(F ⋙Q G) = (F : r ⥤C s) ⋙C (G : s ⥤C t) := rfl

-- -- TODO: coe_inj

-- end Prefunctor

-- namespace Prefunctor

-- def mapPath (F : r ⥤Q s) : Path r a b → Path s (F.obj a) (F.obj b)
--   | Path.nil a => Path.nil (F.obj a)
--   | Path.cons p s => Path.cons (mapPath F p) (F.map s)

-- @[simp]
-- theorem mapPath_nil {r : α → α → Sort*} (F : r ⥤Q s) (a : α)
--   : F.mapPath (Path.nil a) = Path.nil _ := rfl

-- @[simp]
-- theorem mapPath_cons {r : α → α → Sort*} (F : r ⥤Q s) (p : Path r a b) (s : r b c)
--   : F.mapPath (Path.cons p s) = Path.cons (F.mapPath p) (F.map s) := rfl

-- @[simp]
-- theorem comp_mapPath {r : α → α → Sort*} (F : r ⥤Q s) (G : s ⥤Q t) (p : Path r a b)
--   : (F ⋙Q G).mapPath p = G.mapPath (F.mapPath p) := by induction p <;> simp [*]

-- @[simp]
-- theorem mapPath_id {r : α → α → Sort*} (p : Path r a b)
--   : (𝟭Q r).mapPath p = p
--   := by induction p <;> simp [*]

-- @[simp]
-- theorem mapPath_comp {r : α → α → Sort*} (F : r ⥤Q s) (p : Path r a b) (q : Path r b c)
--   : F.mapPath (p.comp q) = (F.mapPath p).comp (F.mapPath q) := by
--   induction q generalizing p <;> simp [Path.comp, Prefunctor.mapPath_cons, *]

-- @[simp]
-- theorem mapPath_single {r : α → α → Sort*} (F : r ⥤Q s) (s : r a b)
--   : F.mapPath (Path.single s) = Path.single (F.map s) := rfl

-- def toPath (F : r ⥤Q s) : Path r ⥤Q Path s where
--   obj := F.obj
--   map := F.mapPath

-- @[simp]
-- theorem obj_toPath (F : r ⥤Q s) : (F.toPath).obj = F.obj := rfl

-- -- TODO: should this be a simp lemma? the other way around?
-- theorem map_toPath (F : r ⥤Q s) (p : Path r a b) : (F.toPath).map p = F.mapPath p := rfl

-- @[simp]
-- theorem toPath_map_nil (F : r ⥤Q s) (a)
--   : (F.toPath).map (Path.nil a) = Path.nil _ := rfl

-- @[simp]
-- theorem toPath_map_cons (F : r ⥤Q s) (p : Path r a b) (s : r b c)
--   : (F.toPath).map (Path.cons p s) = Path.cons ((F.toPath).map p) (F.map s) := rfl

-- @[simp]
-- theorem toPath_map_comp (F : r ⥤Q s) (p : Path r a b) (q : Path r b c)
--   : (F.toPath).map (p.comp q) = ((F.toPath).map p).comp ((F.toPath).map q)
--   := mapPath_comp F p q

-- @[simp]
-- theorem toPath_map_single (F : r ⥤Q s) (s : r a b)
--   : (F.toPath).map (Path.single s) = Path.single (F.map s) := rfl

-- @[simp]
-- def toPath_comp (F : r ⥤Q s) (G : s ⥤Q t) : toPath (F ⋙Q G) = toPath F ⋙Q toPath G := by
--   ext
--   . rfl
--   . simp only [obj_comp, Function.comp_apply, heq_eq_eq]
--     funext _ _ p
--     exact comp_mapPath F G p

-- @[simp]
-- def toPath_id : toPath (𝟭Q r) = 𝟭Q (Path r) := by
--   ext
--   . rfl
--   . simp only [obj_id, Function.comp_apply, heq_eq_eq]
--     funext _ _ p
--     exact mapPath_id p

-- -- TODO: mapSPath; toSPath

-- end Prefunctor

-- namespace SPath

-- def toPathF : SPath r ⥤Q Path r where
--   obj := _root_.id
--   map := toPath

-- end SPath

-- section Quiver

-- variable [Qκ : Quiver κ] [QΘ : Quiver θ] [QΦ : Quiver Φ]

-- def Src (_r : α → β → Sort*) := α

-- def toSrc (r : α → β → Sort*) (a : α) : Src r := a

-- def Trg (_r : α → β → Sort*) := β

-- def toTrg (r : α → β → Sort*) (b : β) : Trg r := b

-- @[simp]
-- instance toQuiver {r : α → α → Sort*} : Quiver (Src r) := ⟨r⟩

-- namespace Path

-- -- TODO: this should not be necessary
-- set_option linter.unusedVariables false in
-- def toQuiver : Path r a b → Quiver.Path (toSrc r a) (toSrc r b)
--   | nil _ => Quiver.Path.nil
--   | cons p s => Quiver.Path.cons p.toQuiver s

-- @[simp]
-- theorem toQuiver_nil : toQuiver (@nil _ r a) = Quiver.Path.nil := rfl

-- @[simp]
-- theorem toQuiver_cons (p : Path r a b) (s : r b c)
--   : toQuiver (cons p s) = Quiver.Path.cons p.toQuiver s := rfl

-- @[simp]
-- theorem toQuiver_comp (p : Path r a b) (q : Path r b c)
--   : toQuiver (p.comp q) = Quiver.Path.comp p.toQuiver q.toQuiver := by
--   induction q generalizing p <;> simp [*]

-- -- NOTE: this is here for termination checker hax...
-- def ofQuiver {a b : κ} : Quiver.Path a b → Path Quiver.Hom a b
--   | Quiver.Path.nil => nil _
--   | Quiver.Path.cons p s => cons (ofQuiver p) s

-- def ofSrc : Quiver.Path (toSrc r a) (toSrc r b) → Path r a b := ofQuiver

-- @[simp]
-- theorem ofQuiver_nil {a : κ} : ofQuiver (Quiver.Path.nil : Quiver.Path a a) = nil _ := rfl

-- @[simp]
-- theorem ofQuiver_cons {a b c : κ} (p : Quiver.Path a b) (s : b ⟶ c)
--   : ofQuiver (Quiver.Path.cons p s) = cons (ofQuiver p) s := rfl

-- @[simp]
-- theorem ofSrc_nil : ofSrc (Quiver.Path.nil : Quiver.Path (toSrc r a) (toSrc r a)) = nil _ := rfl

-- @[simp]
-- theorem ofQuiver_comp {a b c : κ} (p : Quiver.Path a b) (q : Quiver.Path b c)
--   : ofQuiver (Quiver.Path.comp p q) = (ofQuiver p).comp (ofQuiver q) := by
--   induction q generalizing p <;> simp [*]

-- @[simp]
-- theorem ofSrc_comp {a b c : Src r} (p : Quiver.Path a b) (q : Quiver.Path b c)
--   : ofSrc (Quiver.Path.comp p q) = (ofSrc p).comp (ofSrc q) := ofQuiver_comp p q

-- @[simp]
-- theorem toQuiver_ofQuiver_apply {a b : κ} (p : Quiver.Path a b)
--     : toQuiver (ofQuiver p) = p := by induction p <;> simp [*]

-- @[simp]
-- theorem toQuiver_ofSrc_apply {a b : Src r} (p : Quiver.Path a b)
--     : toQuiver (ofSrc p) = p := toQuiver_ofQuiver_apply p

-- end Path

-- namespace Sum

-- def inlH {r : α → β → Type*} {s : α → β → Type*} : r ⥤C Sum r s where
--   objIn a _ := a
--   objOut _ b := b
--   map := inl

-- def inlF {r s : α → α → Type*} : r ⥤Q Sum r s where
--   obj := id
--   map := inl

-- @[simp]
-- theorem coe_inlF : (@inlF _ r s : r ⥤C Sum r s) = inlH := rfl

-- def inrH {r : α → β → Type*} {s : α → β → Type*} : s ⥤C Sum r s where
--   objIn a _ := a
--   objOut _ b := b
--   map := inr

-- def inrF {r s : α → α → Type*} : s ⥤Q Sum r s where
--   obj := id
--   map := inr

-- @[simp]
-- theorem coe_inrF : (@inrF _ r s : s ⥤C Sum r s) = inrH := rfl

-- @[simp]
-- def swap : Sum r s a b -> Sum s r a b
--   | inl x => inr x
--   | inr x => inl x

-- @[simp]
-- theorem swap_comp_swap : swap ∘ swap = @_root_.id (Sum r s a b) := by
--   funext x
--   cases x <;> rfl

-- @[simp]
-- theorem swap_swap {p : Sum r s a b} : (swap (swap p)) = p := by cases p <;> rfl

-- def swapH : Sum r s ⥤C Sum s r where
--   objIn a _ := a
--   objOut _ b := b
--   map := swap

-- @[simp]
-- theorem swapH_comp_swapH : swapH ⋙C swapH = 𝟭C (Sum r s) := by
--   ext
--   . rfl
--   . rfl
--   . simp only [swapH, BimodHom.objIn_comp, BimodHom.objOut_comp, heq_eq_eq]
--     funext _ _ p
--     cases p <;> rfl

-- def swapF : Sum r s ⥤Q Sum s r where
--   obj := id
--   map := swap

-- @[simp]
-- theorem swapF_comp_swapF : swapF ⋙Q swapF = 𝟭Q (Sum r s) := by
--   ext
--   . rfl
--   . simp only [swapF, Function.comp_apply, heq_eq_eq]
--     funext _ _ p
--     cases p <;> rfl

-- theorem coe_swapF : (@swapF _ r s : Sum r s ⥤C Sum s r) = swapH := rfl

-- @[simp]
-- def flip : Sum r (Op r) a b → Sum r (Op r) b a
--   | inl x => inr x
--   | inr x => inl x

-- @[simp]
-- def flip_flip {p : Sum r (Op r) a b} : flip (flip p) = p := by
--   cases p <;> rfl

-- @[simp]
-- theorem flip_comp_flip : flip ∘ flip = @_root_.id (Sum r (Op r) a b) := by
--   funext x
--   cases x <;> rfl

-- def flipH : Sum r (Op r) ⥤C Sum r (Op r) where
--   objIn _ a := a
--   objOut b _ := b
--   map := flip

-- @[simp]
-- def flipH_comp_flipH : flipH ⋙C flipH = 𝟭C (Sum r (Op r)) := by
--   ext
--   . rfl
--   . rfl
--   . simp only [flipH, BimodHom.objIn_comp, BimodHom.objOut_comp, heq_eq_eq]
--     funext _ _ p
--     cases p <;> rfl

-- end Sum

-- namespace Prefunctor

-- def toQuiver (F : r ⥤Q s) : (Src r) ⥤q (Src s) where
--   obj := F.obj
--   map := F.map

-- def ofQuiver (F : κ ⥤q θ) : Qκ.Hom ⥤Q QΘ.Hom where
--   obj := F.obj
--   map := F.map

-- -- TODO: ofSrc specifically

-- @[simp]
-- theorem toQuiver_id : toQuiver (𝟭Q r) = 𝟭q (Src r) := rfl

-- @[simp]
-- theorem ofQuiver_id : ofQuiver (𝟭q κ) = 𝟭Q Qκ.Hom := rfl

-- @[simp]
-- theorem toQuiver_comp (F : r ⥤Q s) (G : s ⥤Q t)
--   : toQuiver (F ⋙Q G) = toQuiver F ⋙q toQuiver G := rfl

-- @[simp]
-- theorem ofQuiver_comp (F : κ ⥤q θ) (G : θ ⥤q Φ)
--   : ofQuiver (F ⋙q G) = ofQuiver F ⋙Q ofQuiver G := rfl

-- @[simp]
-- theorem toQuiver_ofQuiver_apply (F : r ⥤Q s)
--   : Prefunctor.ofQuiver (Prefunctor.toQuiver F) = F := rfl

-- @[simp]
-- theorem toQuiver_ofQuiver
--   : @Prefunctor.toQuiver _ r _ s ∘ Prefunctor.ofQuiver = _root_.id := rfl

-- @[simp]
-- theorem ofQuiver_toQuiver_apply (F : κ ⥤q θ)
--   : Prefunctor.toQuiver (Prefunctor.ofQuiver F) = F := rfl

-- @[simp]
-- theorem ofQuiver_toQuiver
--   : Prefunctor.ofQuiver ∘ @Prefunctor.toQuiver _ r _ s = _root_.id := rfl

-- @[simp]
-- theorem obj_toQuiver (F : r ⥤Q s) : (Prefunctor.toQuiver F).obj = F.obj := rfl

-- @[simp]
-- theorem map_toQuiver (F : r ⥤Q s) : (Prefunctor.toQuiver F).map p = F.map p := rfl

-- end Prefunctor

-- end Quiver

-- end Corr
