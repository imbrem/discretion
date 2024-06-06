import Mathlib.Logic.Relation
import Mathlib.Combinatorics.Quiver.Path

namespace Corr

section Basic

def Rel {α : Sort*} {β : Sort*} (r : α → β → Sort*) : α → β → Prop := λa b => Nonempty (r a b)

def Comp {α : Type*} {β : Type*} {γ : Type*} (r : α → β → Type*) (s : β → γ → Type*)
  : α → γ → Type _ := λa c => Σb, (_ : r a b) ×' s b c

structure Transformer (r : α → β → Sort v) (s : α' → β' → Sort w) where
  objIn : α → α'
  objOut : β → β'
  map : r a b → s (objIn a) (objOut b)

end Basic

namespace Transformer

infixl:50 " ⥤C " => Transformer

def id : Transformer r r where
  objIn := _root_.id
  objOut := _root_.id
  map := _root_.id

notation "𝟭C" => id

def comp (F : Transformer r s) (G : Transformer s t) : Transformer r t where
  objIn := G.objIn ∘ F.objIn
  objOut := G.objOut ∘ F.objOut
  map := G.map ∘ F.map

infixl:60 " ⋙C " => comp

@[simp]
theorem comp_id (F : r ⥤C s) : F ⋙C 𝟭C = F := rfl

@[simp]
theorem id_comp (F : r ⥤C s) : 𝟭C ⋙C F = F := rfl

theorem comp_assoc (F : r ⥤C s) (G : s ⥤C t) (H : t ⥤C u)
  : (F ⋙C G) ⋙C H = F ⋙C (G ⋙C H) := rfl

@[simp]
theorem objIn_comp (F : r ⥤C s) (G : s ⥤C t) : (F ⋙C G).objIn = G.objIn ∘ F.objIn := rfl

@[simp]
theorem objOut_comp (F : r ⥤C s) (G : s ⥤C t) : (F ⋙C G).objOut = G.objOut ∘ F.objOut := rfl

@[simp]
theorem map_comp (F : r ⥤C s) (G : s ⥤C t) (x : r a b)
  : (F ⋙C G).map x = G.map (F.map x) := rfl

theorem toLiftFun (F : r ⥤C s) : (Rel r ⇒ Rel s) F.objIn F.objOut := λ_ _ ⟨p⟩ => ⟨F.map p⟩

end Transformer

inductive Path.{u, v} {α : Type u} (r : α → α → Sort v) : α → α → Sort (max (u + 1) v)
  | nil (a) : Path r a a
  | cons : Path r a b → r b c → Path r a c

inductive TransGen.{u, v} {α : Type u} (r : α → α → Sort v) : α → α → Sort (max (u + 1) v)
  | single : r a b → TransGen r a b
  | cons : TransGen r a b → r b c → TransGen r a c

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
  : comp p (comp q s) = comp (comp p q) s := by induction s generalizing p <;> simp [comp_cons, *]

def snoc (s : r a b) : Path r b c → Path r a c := comp (single s)

instance : Trans (Path r) (Path r) (Path r) where
  trans := comp

instance : Trans (Path r) r (Path r) where
  trans := cons

instance : Trans r (Path r) (Path r) where
  trans := snoc

end Path

structure Prefunctor (r : α → α → Sort v) (s : β → β → Sort w) where
  obj : α → β
  map : r a b → s (obj a) (obj b)

namespace Prefunctor

infixl:50 " ⥤Q " => Prefunctor

def id (r : α → α → Sort v) : Prefunctor r r where
  obj := _root_.id
  map := _root_.id

notation "𝟭Q" => id

def comp (F : Prefunctor r s) (G : Prefunctor s t) : Prefunctor r t where
  obj := G.obj ∘ F.obj
  map := G.map ∘ F.map

infixl:60 " ⋙Q " => comp

@[simp]
theorem comp_id (F : r ⥤Q s) : F ⋙Q 𝟭Q s = F := rfl

@[simp]
theorem id_comp (F : r ⥤Q s) : 𝟭Q r ⋙Q F = F := rfl

theorem comp_assoc (F : r ⥤Q s) (G : s ⥤Q t) (H : t ⥤Q u)
  : (F ⋙Q G) ⋙Q H = F ⋙Q (G ⋙Q H) := rfl

@[simp]
theorem obj_comp (F : r ⥤Q s) (G : s ⥤Q t) : (F ⋙Q G).obj = G.obj ∘ F.obj := rfl

@[simp]
theorem map_comp (F : r ⥤Q s) (G : s ⥤Q t) (x : r a b)
  : (F ⋙Q G).map x = G.map (F.map x) := rfl

theorem toLiftFun (F : r ⥤Q s) : (Rel r ⇒ Rel s) F.obj F.obj := λ_ _ ⟨p⟩ => ⟨F.map p⟩

def mapPath (F : r ⥤Q s) : Path r a b → Path s (F.obj a) (F.obj b)
  | Path.nil a => Path.nil (F.obj a)
  | Path.cons p s => Path.cons (mapPath F p) (F.map s)

@[simp]
theorem mapPath_nil {r : α → α → Sort*} (F : r ⥤Q s) (a : α)
  : F.mapPath (Path.nil a) = Path.nil _ := rfl

@[simp]
theorem mapPath_cons {r : α → α → Sort*} (F : r ⥤Q s) (p : Path r a b) (s : r b c)
  : F.mapPath (Path.cons p s) = Path.cons (F.mapPath p) (F.map s) := rfl

@[simp]
theorem comp_mapPath {r : α → α → Sort*} (F : r ⥤Q s) (G : s ⥤Q t) (p : Path r a b)
  : (F ⋙Q G).mapPath p = G.mapPath (F.mapPath p) := by induction p <;> simp [*]

@[simp]
theorem mapPath_comp {r : α → α → Sort*} (F : r ⥤Q s) (p : Path r a b) (q : Path r b c)
  : F.mapPath (p.comp q) = (F.mapPath p).comp (F.mapPath q) := by
  induction q generalizing p <;> simp [Path.comp, Prefunctor.mapPath_cons, *]

@[simp]
theorem mapPath_single {r : α → α → Sort*} (F : r ⥤Q s) (s : r a b)
  : F.mapPath (Path.single s) = Path.single (F.map s) := rfl

end Prefunctor

section Quiver

variable [Qκ : Quiver κ] [QΘ : Quiver θ] [QΦ : Quiver Φ]

def Src (_r : α → β → Sort*) := α

def toSrc (r : α → β → Sort*) (a : α) : Src r := a

def Trg (_r : α → β → Sort*) := β

def toTrg (r : α → β → Sort*) (b : β) : Trg r := b

@[simp]
instance toQuiver {r : α → α → Sort*} : Quiver (Src r) := ⟨r⟩

namespace Path

-- TODO: this should not be necessary
set_option linter.unusedVariables false in
def toQuiver : Path r a b → Quiver.Path (toSrc r a) (toSrc r b)
  | nil _ => Quiver.Path.nil
  | cons p s => Quiver.Path.cons p.toQuiver s

@[simp]
theorem toQuiver_nil : toQuiver (@nil _ r a) = Quiver.Path.nil := rfl

@[simp]
theorem toQuiver_cons (p : Path r a b) (s : r b c)
  : toQuiver (cons p s) = Quiver.Path.cons p.toQuiver s := rfl

@[simp]
theorem toQuiver_comp (p : Path r a b) (q : Path r b c)
  : toQuiver (p.comp q) = Quiver.Path.comp p.toQuiver q.toQuiver := by
  induction q generalizing p <;> simp [*]

-- NOTE: this is here for termination checker hax...
def ofQuiver {a b : κ} : Quiver.Path a b → Path Quiver.Hom a b
  | Quiver.Path.nil => nil _
  | Quiver.Path.cons p s => cons (ofQuiver p) s

def ofSrc : Quiver.Path (toSrc r a) (toSrc r b) → Path r a b := ofQuiver

@[simp]
theorem ofQuiver_nil {a : κ} : ofQuiver (Quiver.Path.nil : Quiver.Path a a) = nil _ := rfl

@[simp]
theorem ofQuiver_cons {a b c : κ} (p : Quiver.Path a b) (s : b ⟶ c)
  : ofQuiver (Quiver.Path.cons p s) = cons (ofQuiver p) s := rfl

@[simp]
theorem ofSrc_nil : ofSrc (Quiver.Path.nil : Quiver.Path (toSrc r a) (toSrc r a)) = nil _ := rfl

@[simp]
theorem ofQuiver_comp {a b c : κ} (p : Quiver.Path a b) (q : Quiver.Path b c)
  : ofQuiver (Quiver.Path.comp p q) = (ofQuiver p).comp (ofQuiver q) := by
  induction q generalizing p <;> simp [*]

@[simp]
theorem ofSrc_comp {a b c : Src r} (p : Quiver.Path a b) (q : Quiver.Path b c)
  : ofSrc (Quiver.Path.comp p q) = (ofSrc p).comp (ofSrc q) := ofQuiver_comp p q

@[simp]
theorem toQuiver_ofQuiver_apply {a b : κ} (p : Quiver.Path a b)
    : toQuiver (ofQuiver p) = p := by induction p <;> simp [*]

@[simp]
theorem toQuiver_ofSrc_apply {a b : Src r} (p : Quiver.Path a b)
    : toQuiver (ofSrc p) = p := toQuiver_ofQuiver_apply p

end Path

namespace Prefunctor

def toQuiver (F : r ⥤Q s) : (Src r) ⥤q (Src s) where
  obj := F.obj
  map := F.map

def ofQuiver (F : κ ⥤q θ) : Qκ.Hom ⥤Q QΘ.Hom where
  obj := F.obj
  map := F.map

-- TODO: ofSrc specifically

@[simp]
theorem toQuiver_id : toQuiver (𝟭Q r) = 𝟭q (Src r) := rfl

@[simp]
theorem ofQuiver_id : ofQuiver (𝟭q κ) = 𝟭Q Qκ.Hom := rfl

@[simp]
theorem toQuiver_comp (F : r ⥤Q s) (G : s ⥤Q t)
  : toQuiver (F ⋙Q G) = toQuiver F ⋙q toQuiver G := rfl

@[simp]
theorem ofQuiver_comp (F : κ ⥤q θ) (G : θ ⥤q Φ)
  : ofQuiver (F ⋙q G) = ofQuiver F ⋙Q ofQuiver G := rfl

@[simp]
theorem toQuiver_ofQuiver_apply (F : r ⥤Q s)
  : Prefunctor.ofQuiver (Prefunctor.toQuiver F) = F := rfl

@[simp]
theorem toQuiver_ofQuiver
  : @Prefunctor.toQuiver _ r _ s ∘ Prefunctor.ofQuiver = _root_.id := rfl

@[simp]
theorem ofQuiver_toQuiver_apply (F : κ ⥤q θ)
  : Prefunctor.toQuiver (Prefunctor.ofQuiver F) = F := rfl

@[simp]
theorem ofQuiver_toQuiver
  : Prefunctor.ofQuiver ∘ @Prefunctor.toQuiver _ r _ s = _root_.id := rfl

@[simp]
theorem obj_toQuiver (F : r ⥤Q s) : (Prefunctor.toQuiver F).obj = F.obj := rfl

@[simp]
theorem map_toQuiver (F : r ⥤Q s) : (Prefunctor.toQuiver F).map p = F.map p := rfl

end Prefunctor

end Quiver

end Corr