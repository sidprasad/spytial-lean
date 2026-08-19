module

public import Lean
public meta import SpytialLean.TypeShape
public meta import SpytialLean.SelectorElab
public meta import SpytialLean.Attr
public meta import SpytialLean.Command

namespace SpytialLean

open Lean Elab Command Meta

/-! # Suggestion — a deterministic first draft of a spec

`#spytial.suggest <Type>` reads the type's declaration and proposes a
`spytial_spec` block for it, offered as a clickable `Try this:`.

The point is not to be right. It is to replace an empty `[ ]` — which asks you
to decide the layout and its selectors at once — with a concrete draft you can
edit. A draft that is almost right is easier to fix than a blank one is to fill,
and even a wrong proposal names one specific thing to change.

Everything here is static, local, and deterministic: no value, no model, no
network. The rules read `TypeShape`, which is also what the walker and the
selector checker read, so a suggested relation name cannot drift from an emitted
one. Every proposed op is then parsed and elaborated against the target's
`SelScope` before it is offered, so a `Try this:` you accept always compiles.

Where `spytial.suggest` in the Python port has to run candidate selectors
against witness values to learn whether they denote anything, the selectors here
are checked syntax: elaboration is the check.
-/

public section

/-- One proposed op: its surface `spytial_op` text, why it was proposed, and the
    field it came from (empty for whole-type rules). -/
meta structure SuggestedOp where
  op : String
  rationale : String
  sourceField : String := ""
  /-- The same op spelled with fully qualified names, tried if `op` does not
      check. Sigs and constructor literals are Lean names, so the short
      spelling is the one a person would write but only the qualified one is
      guaranteed to resolve. -/
  alt : Option String := none
  deriving Repr, Inhabited

/-- A name's two spellings: the short one a person would write, and the
    qualified one that resolves from anywhere. Both are already escaped. -/
meta structure Spelling where
  short : String
  full : String
  deriving Repr, Inhabited

meta def Spelling.pick (s : Spelling) (qualified : Bool) : String :=
  if qualified then s.full else s.short

/-! ## Spelling

Relation names come from constructor binder names and sigs from type short
names, so both are single Lean identifier components. Two still need escaping:
one that collides with a selector keyword, and one that is not a bare
identifier at all. Guillemets cover both, and over-quoting is harmless. -/

/-- Keywords of the selector grammar; a field named after one needs guillemets. -/
private meta def selKeywords : Array String :=
  #["univ", "iden", "none", "sum", "set", "one", "some", "lone", "all", "no",
    "let", "not", "and", "or", "xor", "implies", "iff", "in", "ni", "else",
    "disj", "true", "false"]

/-- Spell `s` in selector identifier position: bare when it lexes as one and is
    not a keyword, `«guillemets»` otherwise. -/
private meta def selName (s : String) : String :=
  let headOk (c : Char) := c.isAlpha || c == '_'
  let tailOk (c : Char) := c.isAlpha || c.isDigit || c == '_' || c == '\'' ||
    c == '!' || c == '?'
  let bare := match s.toList with
    | c :: cs => headOk c && cs.all tailOk
    | [] => false
  if bare && !selKeywords.contains s then s else s!"«{s}»"

/-! ## Field classification -/

/-- Scalar leaf types: a value the reader wants to *read*, not a box to follow
    an edge to. -/
private meta def scalarTypes : Array Name :=
  #[``Nat, ``Int, ``String, ``Char, ``Bool, ``Float,
    ``UInt8, ``UInt16, ``UInt32, ``UInt64, ``USize]

/-- Names that conventionally mark an edge back up a structure. Such a field is
    drawn by the forward edges already, so showing it doubles every line. -/
private meta def backPointerNames : Array String :=
  #["parent", "prev", "previous", "up", "back", "owner"]

/-- CSS colour keywords. The enum-styling rule fires only when a constructor
    names a colour, so `red`/`black` become border colours and `pending`/`done`
    are left alone rather than assigned invented ones. -/
private meta def cssColorNames : Array String :=
  #["red", "black", "white", "green", "blue", "yellow", "orange", "purple",
    "gray", "grey", "pink", "brown", "cyan", "magenta", "teal", "navy",
    "olive", "maroon", "silver", "gold", "violet", "indigo"]

meta inductive FieldKind where
  /-- Points back at the type being diagrammed: an edge to lay out. -/
  | recursive
  /-- Recursive, but named like an edge back up the structure. -/
  | backPointer
  /-- A scalar leaf; `sig` is its type's name. -/
  | scalar (sig : Spelling)
  /-- A finite enumeration; `labels` pairs each nullary constructor's short
      name (the bare word, for the colour test) with how to spell it. -/
  | enum (sig : Spelling) (labels : Array (String × Spelling))
  /-- Another data type: an edge, but with no direction to prefer. -/
  | nested (sig : Spelling)
  /-- A type parameter, function field, or `Prop`: nothing to say statically. -/
  | opaque
  deriving Repr, Inhabited

/-- How to spell `n` so it resolves from where the suggestion will be pasted.

    A sig and a constructor literal are *Lean* names in selector position, so
    they resolve against the ambient namespace and `open`s — not against the
    relationalizer's short vocabulary names. Emitting `Color` for a
    `Foo.Color` that is not open produces a block that does not compile, which
    is exactly what `checkOps` was catching. -/
private meta def displayName (n : Name) : MetaM Spelling := do
  return { short := selName (shortName n)
           full := selName (toString (← unresolveNameGlobal n)) }

/-- Whether `n` is a finite enumeration — a parameterless inductive all of whose
    constructors are nullary — and if so, its constructors, each as its short
    name paired with the spelling that resolves here. -/
private meta def enumLabels? (n : Name) : MetaM (Option (Array (String × Spelling))) := do
  let env ← getEnv
  let some (.inductInfo ii) := env.find? n | return none
  unless ii.numParams == 0 && ii.numIndices == 0 && !ii.ctors.isEmpty do return none
  let mut labels : Array (String × Spelling) := #[]
  for ctorName in ii.ctors do
    let some (.ctorInfo ci) := env.find? ctorName | return none
    unless ci.numFields == 0 do return none
    labels := labels.push (shortName ctorName, ← displayName ctorName)
  return some labels

meta def classifyField (selfName : Name) (f : FieldShape) : MetaM FieldKind := do
  -- the walker drops proof-like fields, so there is no relation to talk about
  if f.isProofLike then return .opaque
  -- a tabulating field is a table, not an edge; no geometric default fits
  if f.table.isSome then return .opaque
  let some n := f.typeHead | return .opaque
  let sig ← displayName n
  if n == selfName then
    return if backPointerNames.contains f.relName then .backPointer else .recursive
  if scalarTypes.contains n then return .scalar sig
  if let some labels ← enumLabels? n then return .enum sig labels
  return .nested sig

/-! ## Rules

Each rule reads the classified fields and proposes ops. They are deliberately
few and conservative: an op that is wrong costs a reader one edit, but an op
that is *missing* is the blank page this feature exists to remove, so the bias
is toward the handful of shapes that are near-always right. -/

private meta structure Field where
  relName : String
  kind : FieldKind
  deriving Inhabited

/-- The distinct fields of a type, first occurrence winning, paired with the
    per-constructor grouping the orientation rule needs. -/
private meta def analyze (ts : TypeShape) :
    MetaM (Array Field × Array (Array Field)) := do
  let mut seen : Array String := #[]
  let mut flat : Array Field := #[]
  let mut byCtor : Array (Array Field) := #[]
  for c in ts.ctors do
    let mut group : Array Field := #[]
    for f in c.fields do
      let kind ← classifyField ts.typeName f
      let fld : Field := { relName := f.relName, kind }
      group := group.push fld
      unless seen.contains f.relName do
        seen := seen.push f.relName
        flat := flat.push fld
    byCtor := byCtor.push group
  return (flat, byCtor)

/-- Scalars and enumerations fold into the node they hang off, rather than
    becoming a box on a line of their own. -/
private meta def attributeOps (q : Bool) (flat : Array Field) : Array SuggestedOp :=
  flat.filterMap fun f =>
    match f.kind with
    | .scalar sig => some
        { op := s!"attribute {selName f.relName}"
          rationale := s!"'{f.relName}' is a {sig.pick q} — read it on the node, \
            not as an edge"
          sourceField := f.relName }
    | .enum sig _ => some
        { op := s!"attribute {selName f.relName}"
          rationale := s!"'{f.relName}' is the enumeration {sig.pick q} — fold it \
            into the node"
          sourceField := f.relName }
    | _ => none

/-- Recursive fields become downward edges. A constructor with exactly two of
    them is the binary shape, and gets the left/right split that makes a tree
    readable; anything else fans straight down, because no horizontal order
    generalizes past two. -/
private meta def orientationOps (byCtor : Array (Array Field)) : Array SuggestedOp :=
  Id.run do
    let mut seen : Array String := #[]
    let mut out : Array SuggestedOp := #[]
    for group in byCtor do
      let recs := group.filter fun f => match f.kind with | .recursive => true | _ => false
      let binary := recs.size == 2
      for i in [:recs.size] do
        let f := recs[i]!
        if seen.contains f.relName then continue
        seen := seen.push f.relName
        let (dirs, why) :=
          if binary then
            if i == 0 then ("left below", "the left child of a binary node")
            else ("right below", "the right child of a binary node")
          else ("below", "a recursive field — children hang below the parent")
        out := out.push
          { op := s!"orientation {selName f.relName} {dirs}"
            rationale := s!"'{f.relName}' is {why}"
            sourceField := f.relName }
    return out

/-- A back pointer is the transpose of edges the diagram already draws, so
    showing it doubles every line without adding information. -/
private meta def backPointerOps (flat : Array Field) : Array SuggestedOp :=
  flat.filterMap fun f =>
    match f.kind with
    | .backPointer => some
        { op := s!"hideField {selName f.relName}"
          rationale := s!"'{f.relName}' points back up — the child edges already draw it"
          sourceField := f.relName }
    | _ => none

/-- Once a leaf value is shown as a label, its atom is a duplicate box. -/
private meta def hideAtomOp (q : Bool) (flat : Array Field) : Option SuggestedOp := Id.run do
  let mut sigs : Array String := #[]
  for f in flat do
    let sig? := match f.kind with
      | .scalar sig => some (sig.pick q)
      | .enum sig _ => some (sig.pick q)
      | _ => none
    if let some sig := sig? then
      unless sigs.contains sig do sigs := sigs.push sig
  if sigs.isEmpty then return none
  let sel := " + ".intercalate sigs.toList
  return some
    { op := s!"hideAtom {sel}"
      rationale := s!"{sel} now reads as labels, so the separate atoms are duplicates" }

/-- An enumeration whose constructors are colour words is asking to be shown as
    colour. Any other enumeration is left alone: a palette this rule invented
    would carry meaning the declaration never stated. -/
private meta def colorOps (q : Bool) (self : Spelling) (flat : Array Field) :
    Array SuggestedOp := Id.run do
  let mut out : Array SuggestedOp := #[]
  for f in flat do
    let .enum _ labels := f.kind | continue
    unless labels.all (cssColorNames.contains ·.1.toLower) do continue
    for (word, spelling) in labels do
      out := out.push
        { op := s!"atomStyle \{x : {self.pick q} | @:(x.{selName f.relName}) = \
                  {spelling.pick q}} (borderStyle \"{word.toLower}\")"
          rationale := s!"'{f.relName}' enumerates colour names — draw '{word}' as \
            the border"
          sourceField := f.relName }
  return out

/-- The full draft, ordered the way a hand-written spec reads: what each node
    says, then where things go, then what is hidden, then how it looks. -/
meta def suggestOps (ts : TypeShape) : MetaM (Array SuggestedOp) := do
  let (flat, byCtor) ← analyze ts
  let self ← displayName ts.typeName
  -- the same rules run twice, differing only in how names are spelled; the
  -- short run is what a person would write, the qualified run is the fallback
  let mkOps (q : Bool) : Array SuggestedOp :=
    attributeOps q flat
      ++ orientationOps byCtor
      ++ backPointerOps flat
      ++ (hideAtomOp q flat).toArray
      ++ colorOps q self flat
  return Array.zipWith (fun (p a : SuggestedOp) =>
    { p with alt := if p.op == a.op then none else some a.op })
    (mkOps false) (mkOps true)

/-! ## Checking

A proposal is offered only if it parses as a `spytial_op` and elaborates against
the target's scope. This is the Lean counterpart of the Python port's "run the
selector against a witness": there, a selector is a string and only a value can
say whether it denotes anything; here it is checked syntax, so the elaborator
answers statically. A rejection is a bug in the rules above, not in the user's
code, so it is reported as such. -/

/-- Whether `op` parses and elaborates against `scope`. The check must not
    leave the rules' own diagnostics in the user's log, so the message log is
    restored either way. -/
private meta def opChecks (scope : SelScope) (op : String) : TermElabM Bool := do
  let .ok stx := Parser.runParserCategory (← getEnv) `spytial_op op "<spytial.suggest>"
    | return false
  let log ← Core.getMessageLog
  let ok ← try
      let _ ← elabSpytialOps scope #[⟨stx⟩]
      pure true
    catch _ => pure false
  Core.setMessageLog log
  return ok

meta def checkOps (declName : Name) (ops : Array SuggestedOp) :
    TermElabM (Array SuggestedOp) := do
  let scope ← SelScope.ofType declName
  let mut out : Array SuggestedOp := #[]
  for o in ops do
    if ← opChecks scope o.op then
      out := out.push o
    else if let some alt := o.alt then
      -- the short spelling did not resolve here; the qualified one still reads
      if ← opChecks scope alt then
        out := out.push { o with op := alt, alt := none }
      else
        logWarning m!"#spytial.suggest produced an op that does not check \
          against '{declName}' — please report this. Op: '{o.op}'"
    else
      logWarning m!"#spytial.suggest produced an op that does not check against \
        '{declName}' — please report this. Op: '{o.op}'"
  return out

/-! ## Rendering -/

/-- The `spytial_spec` block, as source. -/
meta def renderSpec (declName : Name) (ops : Array SuggestedOp) : String :=
  let body := ",\n".intercalate (ops.toList.map fun o => s!"  {o.op}")
  s!"spytial_spec {declName} [\n{body}\n]"

/-- Why each op was proposed, shown beneath the suggestion rather than inserted
    with it — a rationale is worth reading once and not worth keeping in the
    file. -/
private meta def renderRationale (ops : Array SuggestedOp) : MessageData :=
  MessageData.joinSep (ops.toList.map fun o => m!"• {o.op} — {o.rationale}") "\n"

/-! ## #spytial.suggest command -/

/-- `#spytial.suggest <Type>` proposes a `spytial_spec` for a type, as a
    clickable `Try this:` that replaces the command with the block.

    ```
    inductive RBNode where
      | nil : RBNode
      | node (color : Color) (key : Nat) (left : RBNode) (right : RBNode) : RBNode

    #spytial.suggest RBNode
    ```

    The proposal is a draft to edit, not an answer. It reads the declaration
    only — field names, field types, and which fields recur — so it cannot know
    a layout that lives in your head or in index arithmetic. It pairs with
    `#spytial.coverage`, which names the types that have no spec at all. -/
syntax (name := spytialSuggestCmd) "#spytial.suggest " ident : command

@[command_elab spytialSuggestCmd]
meta def elabSpytialSuggestCmd : CommandElab := fun
  | stx@`(#spytial.suggest $id:ident) => do
    let declName ← resolveGlobalConstNoOverload id
    let ops ← liftTermElabM do
      let some ts ← TypeShape.ofInductive declName
        | throwErrorAt id m!"'{declName}' is not an inductive or structure, so \
            there is no declaration to read a layout from"
      checkOps declName (← suggestOps ts)
    if ops.isEmpty then
      logInfo m!"#spytial.suggest has nothing to propose for '{declName}': its \
        fields are all type parameters, function fields, or proofs, or it has \
        no fields at all. Write the spec by hand — `#spytial.datum` shows what \
        the walker emits."
    else
      liftCoreM <| Lean.Meta.Tactic.TryThis.addSuggestion stx
        { suggestion := renderSpec declName ops
          toCodeActionTitle? := some fun _ => s!"Attach suggested spec to {declName}" }
        (origSpan? := stx)
        (footer := m!"\n{renderRationale ops}\n\nA draft, not an answer — edit it.")
  | stx => throwError "Unexpected syntax {stx}."

end

end SpytialLean
