import SpytialLean
import SpytialTests.WalkCanon

/-! # Tests for `SpytialLean.Display`

The declarations a type makes about how it is drawn — `SpytialLeaf`,
`SpytialDisplay`, `SpytialCtorTypes`, the `Hidden`/`Rel` field wrappers — and
the `spytial_view` rewrite that pairs with them, pinned through
`#spytial.datum` exactly as a user hits them. `#spytial.spec` pins the other
half: a declaration changes the datum and the selector vocabulary together, so
a name outside the view's vocabulary must not elaborate. -/

open Lean SpytialLean

/-! ## A leaf is one atom, labeled by `SpytialDisplay`

No `s` field edge, and the label is the instance's, not the type's spelling. -/

structure Wrapped where
  s : String

instance : SpytialLeaf Wrapped := ⟨⟩
instance : SpytialDisplay Wrapped := ⟨fun w => s!"<{w.s}>"⟩

/--
info: {"relations": [],
 "atoms": [{"type": "Wrapped", "label": "<hi>", "id": "atom_0"}]}
-/
#guard_msgs in
#spytial.datum (Wrapped.mk "hi")

/-! ## Constructor types, hidden fields, relation fields

`SpytialCtorTypes` makes the atom type the constructor's name, so `A` and `B`
are separate vocabulary. The `Hidden` ids and text feed the identity and
display instances without drawing anything, and the `Rel (Nat × Node)` field
is one ternary `kids` relation — the product element contributes a column,
not an atom of its own. -/

inductive Node where
  | A (id : Hidden Nat) (kids : Rel (Nat × Node))
  | B (id : Hidden Nat) (text : Hidden String)

def Node.ident : Node → Nat
  | .A i _ | .B i _ => i.val

instance : SpytialCtorTypes Node := ⟨⟩
instance : SpytialIdentity Node := ⟨.identity fun v => .ofNat v.ident, none⟩
instance : SpytialDisplay Node :=
  ⟨fun | .A .. => "a!" | .B _ t => t.val⟩

deriving instance ToExpr for Node

/--
info: {"relations":
 [{"types": ["A", "Nat", "B"],
   "tuples":
   [{"types": ["A", "Nat", "B"], "atoms": ["atom_0", "atom_1", "atom_2"]},
    {"types": ["A", "Nat", "B"], "atoms": ["atom_0", "atom_3", "atom_4"]}],
   "name": "kids",
   "id": "kids"}],
 "atoms":
 [{"type": "A", "label": "a!", "id": "atom_0"},
  {"type": "Nat", "label": "0", "id": "atom_1"},
  {"type": "B", "label": "x", "id": "atom_2"},
  {"type": "Nat", "label": "1", "id": "atom_3"},
  {"type": "B", "label": "y", "id": "atom_4"}]}
-/
#guard_msgs in
#spytial.datum (Node.A ⟨0⟩ ⟨[(0, .B ⟨1⟩ ⟨"x"⟩), (1, .B ⟨2⟩ ⟨"y"⟩)]⟩)

-- The declared identity reads a `Hidden` field: the repeated id 1 is one atom
-- two tuples point at, and the second occurrence's text never reaches a label.
/--
info: {"relations":
 [{"types": ["A", "Nat", "B"],
   "tuples":
   [{"types": ["A", "Nat", "B"], "atoms": ["atom_0", "atom_1", "atom_2"]},
    {"types": ["A", "Nat", "B"], "atoms": ["atom_0", "atom_3", "atom_2"]}],
   "name": "kids",
   "id": "kids"}],
 "atoms":
 [{"type": "A", "label": "a!", "id": "atom_0"},
  {"type": "Nat", "label": "0", "id": "atom_1"},
  {"type": "B", "label": "x", "id": "atom_2"},
  {"type": "Nat", "label": "1", "id": "atom_3"}]}
-/
#guard_msgs in
#spytial.datum (Node.A ⟨0⟩ ⟨[(0, .B ⟨1⟩ ⟨"x"⟩), (1, .B ⟨1⟩ ⟨"ignored"⟩)]⟩)

-- An empty `Rel` still declares its relation, at the field's declared element
-- type — nothing populated it, so the last column is `Node`.
/--
info: {"relations":
 [{"types": ["A", "Nat", "Node"], "tuples": [], "name": "kids", "id": "kids"}],
 "atoms": [{"type": "A", "label": "a!", "id": "atom_0"}]}
-/
#guard_msgs in
#spytial.datum (Node.A ⟨0⟩ ⟨[]⟩)

/-! ## A registered view rewrites the walked value

`Bool` is drawn as a `Node`, so neither `Bool` constructor nor the `Prod`
cell's `Bool` columns survive into the datum. Merging happens on the view
value's identity: the pair's two `false` components are one atom. -/

meta def boolView : SpytialView := fun e nonce => do
  let w ← Meta.whnf e
  unless w.isConstOf ``Bool.true || w.isConstOf ``Bool.false do return none
  let b := w.isConstOf ``Bool.true
  return some (toExpr (Node.B ⟨nonce⟩ ⟨if b then "yes" else "no"⟩))

spytial_view Bool Node boolView

/--
info: {"relations": [], "atoms": [{"type": "B", "label": "yes", "id": "atom_1"}]}
-/
#guard_msgs in
#spytial.datum true

-- The owning columns carry the walked atoms' type — the view's, not `Bool`.
/--
info: {"relations":
 [{"types": ["Prod", "B"],
   "tuples": [{"types": ["Prod", "B"], "atoms": ["atom_0", "atom_2"]}],
   "name": "fst",
   "id": "fst"},
  {"types": ["Prod", "B"],
   "tuples": [{"types": ["Prod", "B"], "atoms": ["atom_0", "atom_2"]}],
   "name": "snd",
   "id": "snd"}],
 "atoms":
 [{"type": "Prod", "label": "mk", "id": "atom_0"},
  {"type": "B", "label": "no", "id": "atom_2"}]}
-/
#guard_msgs in
#spytial.datum (false, false)

/-! ## Differential oracle: the fused walker equals the two-pass reference

`Rel` emission and view dispatch are new in both walkers, so they have to agree
there too — including a walk that dispatches the view twice. -/

def sampleLam : Expr := .lam `x (.const `Nat []) (.bvar 0) .default

#eval show MetaM Unit from do
  assertMatchesReference "diff.rel"
    (toExpr (Node.A ⟨0⟩ ⟨[(0, .B ⟨1⟩ ⟨"x"⟩), (1, .B ⟨2⟩ ⟨"y"⟩)]⟩))
  assertMatchesReference "diff.rel.empty" (toExpr (Node.A ⟨0⟩ ⟨[]⟩))
  assertMatchesReference "diff.backref"
    (toExpr (Node.A ⟨0⟩ ⟨[(0, .B ⟨1⟩ ⟨"x"⟩), (1, .B ⟨1⟩ ⟨"ignored"⟩)]⟩))
  -- a cross-constructor merge retypes the column to the representative's atom
  -- type — the reference's merge pass must follow the atom, not pass 1's cell
  assertMatchesReference "diff.crossctor"
    (toExpr (Node.A ⟨0⟩ ⟨[(0, .B ⟨0⟩ ⟨"me"⟩)]⟩))
  assertMatchesReference "diff.view" (toExpr true)
  assertMatchesReference "diff.view.pair"
    (← Meta.mkAppM ``Prod.mk #[toExpr true, toExpr false])
  -- the integrated Expr view: a `Ref` merging into its `Binder`
  assertMatchesReference "diff.exprview" (mkConst ``sampleLam)

/-! ## The selector scope is the drawn vocabulary

Constructor names resolve as atom types, and a spec over `Bool` checks
against `Node` — the view target — not against `Bool`. -/

/--
info: {"directives":
 [{"atomStyle": {"selector": "B", "fillStyle": {"color": "#ff0000"}}}]}
-/
#guard_msgs in
#spytial.spec (Node.A ⟨0⟩ ⟨[]⟩) with [atomStyle B (fillStyle "#ff0000")]

/--
info: {"directives":
 [{"atomStyle": {"selector": "B", "fillStyle": {"color": "#00ff00"}}},
  {"edgeStyle":
   {"lineStyle": {"pattern": "dashed", "color": "#123456"}, "field": "kids"}}]}
-/
#guard_msgs in
#spytial.spec true with [atomStyle B (fillStyle "#00ff00"),
                         edgeStyle kids (lineStyle "#123456" dashed)]

-- Negative control: the scope is closed, so a name it does not contain is an
-- error, not a warning.
/--
error: unknown name 'C' (did you mean 'A', 'B'?)
-/
#guard_msgs in
#spytial.spec (Node.A ⟨0⟩ ⟨[]⟩) with [atomStyle C (fillStyle "#ff0000")]
