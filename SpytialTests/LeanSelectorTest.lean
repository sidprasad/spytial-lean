module

public import Lean.Elab.Command
public import SpytialLean.Sel
-- the walk keys atoms by value only where this is visible to elaboration
public import SpytialLean.Identity
public meta import SpytialLean.Attr
public meta import SpytialLean.Command

open SpytialLean Lean Elab Command

-- off so the goldens need not restate the stamp on every op; `## The source
-- stamp` below covers it
set_option spytial.source false

/-! # Tests for raw Lean selectors

`lean (…)` selects by running an ordinary Lean function over the values the walk
produced. Goldens pin the tuples it resolves to, since those *are* the
observable behaviour. -/

public inductive LHue where
  | red | black
  deriving DecidableEq, BEq

public inductive LRB where
  | nil : LRB
  | node (color : LHue) (key : Nat) (left right : LRB) : LRB
  deriving BEq

public def LRB.isBlack : LRB → Bool
  | .node .black .. => true
  | _ => false

public def LRB.lt : LRB → LRB
  | .node _ _ l _ => l
  | .nil => .nil

public def LRB.kids : LRB → Array LRB
  | .nil => #[]
  | .node _ _ l r => #[l, r]

public def LRB.inner : LRB → Option LRB
  | .node _ _ l@(.node ..) _ => some l
  | _ => none

/-- Root black, one nil child on each side. Atoms: 0 node, 1 black, 2 key,
    3 nil (both children hold it). -/
public def lSmall : LRB := .node .black 1 .nil .nil

/-- Root red over a black node; the black one is *not* the root, so an
    `isBlack` selector must pick an interior atom. Atoms: 0 node, 1 red,
    2 key, 3 node, 4 black, 5 key, 6 nil (every leaf holds it). -/
public def lBig : LRB := .node .red 1 (.node .black 2 .nil .nil) .nil

/-- `Foo.lean:12` → `Foo.lean:N`: the stamp's line moves whenever the lines
    above it do, so the goldens pin the file, never the line. -/
private meta def maskLines (s : String) : String :=
  match s.splitOn ".lean:" with
  | [] => s
  | first :: rest =>
    first ++ String.join (rest.map fun part =>
      ".lean:N" ++ (part.dropWhile Char.isDigit).toString)

public section

/-- The `cndSpec` the widget actually receives, so deferred resolution is what
    gets tested rather than a re-render. -/
syntax (name := payloadSpecCmd) "#payload_spec " term : command

syntax (name := maskedSpecCmd) "#masked_spec " term " with "
  "[" spytial_op,*,? "]" : command

end

@[command_elab payloadSpecCmd]
public meta def elabPayloadSpec : CommandElab := fun
  | `(#payload_spec $t:term) => do
    let props ← liftTermElabM <| spytialPayloadProps t
    logInfo (maskLines s!"{props.getObjValD "cndSpec"}")
  | stx => throwError "Unexpected syntax {stx}."

@[command_elab maskedSpecCmd]
public meta def elabMaskedSpec : CommandElab := fun
  | `(#masked_spec $t:term with [$ops,*]) => do
    let props ← liftTermElabM <| spytialPayloadProps t (some (ops.getElems))
    -- unwrap the JSON string so the golden reads as the spec, not as an
    -- escaped one-liner
    logInfo (maskLines <| match props.getObjValD "cndSpec" with
      | .str spec => spec
      | j => toString j)
  | stx => throwError "Unexpected syntax {stx}."

/-! ## Arity 1: a predicate resolves to the atoms it selects, extensionally,
by atom id -/

/-- info: {"constraints": [{"hideAtom": {"selector": "`atom_3"}}]} -/
#guard_msgs in
#spytial.spec lSmall with [hideAtom lean (fun n : LRB => n matches .nil)]

-- a `Prop`-valued predicate goes through `Decidable`, not compiled `Bool`
/-- info: {"constraints": [{"hideAtom": {"selector": "`atom_1"}}]} -/
#guard_msgs in
#spytial.spec lSmall with [hideAtom lean (fun c : LHue => c = LHue.black)]

-- the argument type fixes the sig the column ranges over, so scalars are reachable
/-- info: {"constraints": [{"hideAtom": {"selector": "`atom_2"}}]} -/
#guard_msgs in
#spytial.spec lSmall with [hideAtom lean (fun k : Nat => k > 0)]

/-- info: {"constraints": [{"hideAtom": {"selector": "`atom_0"}}]} -/
#guard_msgs in
#spytial.spec lSmall with [hideAtom lean (LRB.isBlack)]

/-- info: {"constraints": [{"hideAtom": {"selector": "`atom_3 + LHue"}}]} -/
#guard_msgs in
#spytial.spec lSmall with [hideAtom lean (fun n : LRB => n matches .nil) + LHue]

-- an empty selection is `none`, not an empty union
/-- info: {"constraints": [{"hideAtom": {"selector": "none"}}]} -/
#guard_msgs in
#spytial.spec lSmall with [hideAtom lean (fun _ : LHue => false)]

/--
error: the proposition
  ∀ (m : Nat),
    (match x0 with
        | LRB.nil => true
        | x => false) =
        true ∧
      m > 0
needs a `Decidable` instance to run as a selector
-/
#guard_msgs in
#spytial.spec lSmall with
  [hideAtom lean (fun n : LRB => ∀ m : Nat, n matches .nil ∧ m > 0)]

/-! ## Arity n

A tuple lowers to a product, the tuples to a union. Atoms are keyed by value and
`==` computes the same equality, so `p.lt == c` is the accessor's relation. -/

-- `lt` of the interior node is the nil atom, and `.nil`'s own `lt` is `.nil`,
-- so the nil atom also relates to itself
/--
info: {"constraints":
 [{"orientation":
   {"selector": "`atom_0->`atom_3 + `atom_3->`atom_6 + `atom_6->`atom_6",
    "directions": ["below"]}}]}
-/
#guard_msgs in
#spytial.spec lBig with [orientation lean (fun p c : LRB => p.lt == c) below]

-- both of the interior node's children are the nil atom: one tuple
/--
info: {"directives":
 [{"inferredEdge":
   {"selector": "`atom_0->`atom_3 + `atom_0->`atom_6 + `atom_3->`atom_6",
    "name": "kids"}}]}
-/
#guard_msgs in
#spytial.spec lBig with [inferredEdge kids lean (fun p c : LRB => (p.kids).contains c)]

/--
info: {"constraints":
 [{"orientation": {"selector": "`atom_0->`atom_3", "directions": ["below"]}}]}
-/
#guard_msgs in
#spytial.spec lBig with [orientation lean (fun p c : LRB => p.inner == some c) below]

/--
error: a raw Lean selector returns `Bool` or `Prop` — the walked tuples it accepts; to select computed values, write a `Spytial.Sel`
-/
#guard_msgs in
#spytial.spec lBig with [orientation lean (LRB.lt) below]

/--
info: {"directives":
 [{"inferredEdge": {"selector": "`atom_0->`atom_4->`atom_5", "name": "tri"}}]}
-/
#guard_msgs in
#spytial.spec lBig with
  [inferredEdge tri lean (fun (n : LRB) (h : LHue) (k : Nat) =>
     n matches .node .red _ _ _ && h == .black && k > 1)]

/-- error: this position accepts a selector of arity 1, but this one has arity 2 -/
#guard_msgs in
#spytial.spec lBig with [hideAtom lean (fun p c : LRB => p.lt == c)]

/--
error: raw Lean selector selects 4900 tuples, over the limit of 4096; a diagram op over that many tuples would not render legibly
-/
#guard_msgs in
#spytial.spec (List.range 70) with [orientation lean (fun _ _ : Nat => true) below]

-- the enumeration runs even when nothing is selected, so the decided count is
-- capped separately from the selected one
/--
error: this predicate would be decided at 1030301 points (the product of its column sizes), over the limit of 1000000; write a `Spytial.Sel` that computes its tuples instead
-/
#guard_msgs in
#spytial.spec (List.range 101) with
  [inferredEdge big lean (fun _ _ _ : Nat => false)]

/-! ## The general form: `Spytial.Sel`

A predicate tests walked tuples; `Sel T α` computes them — a function of the
datum wrapping `T → Tuples α`, its returned values located by `==`. -/

public def LRB.subtrees : LRB → List LRB
  | .nil => [.nil]
  | n@(.node _ _ l r) => n :: (l.subtrees ++ r.subtrees)

/-- info: {"constraints": [{"hideAtom": {"selector": "`atom_0"}}]} -/
#guard_msgs in
#spytial.spec lBig with [hideAtom lean ((⟨fun t => [t]⟩ : Spytial.Sel LRB LRB))]

-- `Tuples` is a set: order and duplicates in the returned list change nothing
/-- info: {"constraints": [{"hideAtom": {"selector": "`atom_0"}}]} -/
#guard_msgs in
#spytial.spec lBig with [hideAtom lean ((⟨fun t => [t, t]⟩ : Spytial.Sel LRB LRB))]

public def blackSel : Spytial.Sel LRB LRB :=
  ⟨fun t => t.subtrees.filter LRB.isBlack⟩

#guard blackSel.select lBig == [.node .black 2 .nil .nil]

/-- info: {"constraints": [{"hideAtom": {"selector": "`atom_3"}}]} -/
#guard_msgs in
#spytial.spec lBig with [hideAtom lean (blackSel)]

-- on `Tuples`, `∪` is `++` read as a set
public def nilSel : Spytial.Sel LRB LRB :=
  ⟨fun t => t.subtrees.filter (fun n => n matches .nil)⟩

/--
info: {"constraints": [{"hideAtom": {"selector": "`atom_3 + `atom_6"}}]}
-/
#guard_msgs in
#spytial.spec lBig with [hideAtom lean ((blackSel ∪ nilSel))]

/--
info: {"constraints":
 [{"orientation": {"selector": "`atom_0->`atom_3", "directions": ["below"]}}]}
-/
#guard_msgs in
#spytial.spec lBig with
  [orientation lean ((⟨fun t => [(t, t.lt)]⟩ : Spytial.Sel LRB (LRB × LRB))) below]

/-- error: this position accepts a selector of arity 1, but this one has arity 2 -/
#guard_msgs in
#spytial.spec lBig with
  [hideAtom lean ((⟨fun t => [(t, t)]⟩ : Spytial.Sel LRB (LRB × LRB)))]

-- a reducible alias is normalized before the columns are read
public abbrev LEdge := LRB × LRB

/--
info: {"constraints":
 [{"orientation": {"selector": "`atom_0->`atom_3", "directions": ["below"]}}]}
-/
#guard_msgs in
#spytial.spec lBig with
  [orientation lean ((⟨fun t => [(t, t.lt)]⟩ : Spytial.Sel LRB LEdge)) below]

public abbrev LNode := LRB
public abbrev LRBSel := Spytial.Sel LRB LNode

/-- info: {"constraints": [{"hideAtom": {"selector": "`atom_0"}}]} -/
#guard_msgs in
#spytial.spec lBig with [hideAtom lean ((⟨fun t => [t]⟩ : LRBSel))]

-- the tuple cap counts the *set*, so these 9000 duplicates cost nothing
/-- info: {"constraints": [{"hideAtom": {"selector": "`atom_0"}}]} -/
#guard_msgs in
#spytial.spec lBig with
  [hideAtom lean ((⟨fun t => List.replicate 9000 t⟩ : Spytial.Sel LRB LRB))]

/-! ## Deferred resolution: an attached spec is stored structurally with no
value in sight, and the function runs at *use*, once per value -/

spytial_spec LRB [
  hideAtom lean (fun n : LRB => n matches .nil),
  atomStyle lean (LRB.isBlack) (borderStyle "black")
]

/--
info: "{\"directives\":\n [{\"atomStyle\": {\"selector\": \"`atom_0\", \"borderStyle\": {\"color\": \"black\"}}}],\n \"constraints\": [{\"hideAtom\": {\"selector\": \"`atom_3\"}}]}"
-/
#guard_msgs in
#payload_spec lSmall

-- an inherited spec: a parent's `Sel` applies to the child's parent part,
-- through the projection chain
public structure LBase where
  tag : Nat
  deriving BEq

public structure LExt extends LBase where
  extra : Nat

spytial_spec LBase [hideAtom lean ((⟨fun b => [b.tag]⟩ : Spytial.Sel LBase Nat))]

/--
info: "{\"constraints\": [{\"hideAtom\": {\"selector\": \"`atom_2\"}}]}"
-/
#guard_msgs in
#payload_spec (LExt.mk ⟨7⟩ 9)

-- same stored spec, different value: `isBlack` now picks the interior node
/--
info: "{\"directives\":\n [{\"atomStyle\": {\"selector\": \"`atom_3\", \"borderStyle\": {\"color\": \"black\"}}}],\n \"constraints\": [{\"hideAtom\": {\"selector\": \"`atom_6\"}}]}"
-/
#guard_msgs in
#payload_spec lBig

/-! ## Rejections -/

/-- error: a raw Lean selector must be a function over the walked types, but this term has type Nat -/
#guard_msgs in
#spytial.spec lSmall with [hideAtom lean (42)]

/--
warning: 'Float' is not among the types reachable from 'LRB', so this selector cannot match anything
---
info: {"constraints": [{"hideAtom": {"selector": "none"}}]}
-/
#guard_msgs in
#spytial.spec lSmall with [hideAtom lean (fun _ : Float => true)]

-- no follow-on complaint about the holes in the recovery term
/--
error: Invalid field `nosuchfield`: The environment does not contain `LRB.nosuchfield`, so it is not possible to project the field `nosuchfield` from an expression
  n
of type `LRB`
---
warning: this term carries a sorry, so the op selects nothing at render
---
info: {"constraints": [{"hideAtom": {"selector": "none"}}]}
-/
#guard_msgs in
#spytial.spec lSmall with [hideAtom lean (fun n : LRB => n.nosuchfield)]

-- Lean says nothing about a `sorry` inside a command, so the warning is the
-- whole report
/--
warning: this term carries a sorry, so the op selects nothing at render
---
info: {"constraints": [{"hideAtom": {"selector": "none"}}]}
-/
#guard_msgs in
#spytial.spec lSmall with [hideAtom lean ((sorry : Spytial.Sel LRB LRB))]

/-! ## `lean` is not a reserved word: the rule is non-reserved and needs its
parenthesis, so a relation named `lean` still reads as an identifier -/

public inductive LKw where
  | mk (lean : Nat) (rest : LKw)
  | stop

public def lKw : LKw := .mk 1 .stop

/-- info: {"directives": [{"hideField": {"field": "lean"}}]} -/
#guard_msgs in
#spytial.spec lKw with [hideField lean]

/--
info: {"constraints":
 [{"orientation": {"selector": "lean", "directions": ["below"]}}]}
-/
#guard_msgs in
#spytial.spec lKw with [orientation lean below]

/-! ## The source stamp

`lean (…)` resolves to atom ids, which say nothing to a reader of a conflict
report, so the emitted spec carries the Lean the user wrote (`spytial.source`,
on by default) and core cites that instead. -/

set_option spytial.source true in
/--
info: {"constraints":
 [{"hideAtom":
   {"source":
    {"text": "hideAtom lean (fun n : LRB => n matches .nil)",
     "location": "LeanSelectorTest.lean:N"},
    "selector": "`atom_6"}}]}
-/
#guard_msgs in
#masked_spec lBig with [hideAtom lean (fun n : LRB => n matches .nil)]

-- only the ops core cites are stamped — the manifest's `source.displayedBy` —
-- so a directive carries none …
set_option spytial.source true in
/--
info: {"directives":
 [{"atomStyle": {"selector": "`atom_3", "borderStyle": {"color": "black"}}}]}
-/
#guard_msgs in
#masked_spec lBig with [atomStyle lean (LRB.isBlack) (borderStyle "black")]

-- … and neither does `size`: the section an op lowers into is not what decides
set_option spytial.source true in
/-- info: {"constraints": [{"size": {"width": 120, "height": 40}}]} -/
#guard_msgs in
#masked_spec lBig with [size 120 40]

-- an attached spec stores its stamp, so a re-run elsewhere still cites the line
-- it was declared on
set_option spytial.source true in
spytial_spec LKw [orientation lean below]

set_option spytial.source true in
/--
info: "{\"constraints\":\n [{\"orientation\":\n   {\"source\":\n    {\"text\": \"orientation lean below\", \"location\": \"LeanSelectorTest.lean:N\"},\n    \"selector\": \"lean\",\n    \"directions\": [\"below\"]}}]}"
-/
#guard_msgs in
#payload_spec lKw
