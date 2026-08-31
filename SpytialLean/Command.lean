module

public import SpytialLean.Enum
public import Lean
public import Lean.Elab.Command
public import Lean.Elab.Term
public import Lean.Elab.Tactic
public import Lean.Widget.UserWidget
public meta import SpytialLean.Types
public meta import SpytialLean.Spec
public meta import SpytialLean.SpecLang
public meta import SpytialLean.Selector
public meta import SpytialLean.SelectorElab
public meta import SpytialLean.Relationalizer
public meta import SpytialLean.LeanSelector
public meta import SpytialLean.Widget
public meta import SpytialLean.Attr

namespace SpytialLean

open Lean Elab Command Term Meta Widget

public section

/-! ## The op DSL -/

declare_syntax_cat spytial_op
declare_syntax_cat spytial_block_arg
declare_syntax_cat spytial_op_block

syntax str : spytial_block_arg
syntax num : spytial_block_arg
syntax scientific : spytial_block_arg
syntax ident : spytial_block_arg
syntax spytial_op_block : spytial_block_arg

/-- `atomic` over the whole form, so a parenthesized selector backtracks out to
    `spytial_sel`. A shorter window cannot decide it: a selector opens
    `( ident ident` too, and only the close says which was written. A form
    complete as both reads as a block; write `(some (lo))` for the selector. -/
syntax (name := spytialBlockStx)
  atomic("(" ident spytial_block_arg spytial_block_arg* ")") : spytial_op_block

syntax spytialKwArg := atomic(ident noWs ":" ) selExpr

syntax spytialOpArg := num <|> spytial_op_block <|> spytialKwArg <|> selExpr

syntax (name := spytialOpStx) ident spytialOpArg* : spytial_op
/-- `attribute` is a Lean keyword, so it gets its own rule with the keyword as the atom. -/
syntax (name := spytialAttrOp) "attribute " spytialOpArg* : spytial_op
/-- In a use-site `with [...]`, `..` splices the type's attached spec at that position. -/
syntax (name := spytialSpliceStx) ".." : spytial_op
/-- `..name` splices the list bound by `spytial_ops name`, whose root must match. -/
syntax (name := spytialSpliceNamedStx) ".." noWs ident : spytial_op

run_cmd do
  unless (SpecLang.itemOfKey? "attribute").isSome do
    throwError "spytialAttrOp spells the item id \"attribute\", which is not a live item"
  let tokens := Lean.Parser.getTokenTable (← getEnv)
  for i in SpecLang.allItems do
    let key := SpecLang.itemName i
    if key != "attribute" && (tokens.find? key).isSome then
      throwError "the op '{key}' lexes as a Lean token, so the ident-headed \
        rule cannot parse it; give it its own rule the way spytialAttrOp has one"

/-! ### Argument interpretation -/

private meta def argInner (arg : TSyntax `spytialOpArg) : Syntax := arg.raw[0]

/-- `spytialBlockStx`'s arguments, each stripped of its `spytial_block_arg` wrapper. -/
private meta def blockArgs (stx : Syntax) : Array Syntax :=
  (#[stx[2]] ++ stx[3].getArgs).map (·[0])

private meta def orVals (vs : List String) : String := "|".intercalate vs

open SpecLang in
private meta def fieldUsage (i : ItemSpec) (f : FieldSpec) : String :=
  if i.positional.contains f.id then
    match f.type with
    | .«enum» vs _ => orVals vs
    | .enumList _ _ => s!"<{fieldName f.id}>+"
    | _ => s!"<{fieldName f.id}>"
  else match f.type with
    | .block _ => s!"[({fieldName f.id} …)]"
    | .«enum» vs _ =>
      if f.alt.isSome then s!"[({fieldName f.id} {orVals vs} …)]"
      else s!"[{orVals vs}]"
    | .boolean _ =>
      match boolSugar.filter (fun (_, bf, _) => bf == f.id) with
      | [] => s!"[{fieldName f.id}: true|false]"
      | sugars => s!"[{orVals (sugars.map (·.1))}]"
    | .selector _ => s!"[{fieldName f.id}: <selector>]"
    | .str => s!"[{fieldName f.id}: \"…\"]"
    | _ => s!"[{fieldName f.id}: …]"

open SpecLang in
private meta def itemUsage (i : ItemSpec) : String :=
  let lead := i.leadingSelector.toList.map fun f => s!"[<{fieldName f}>]"
  let positional := i.positional.filterMap fun fid => (i.field? fid).map (fieldUsage i)
  let rest := i.fields.filterMap fun f =>
    if i.positional.contains f.id || i.leadingSelector == some f.id then none
    else some (fieldUsage i f)
  let hold := if i.supportsHold then [s!"[hold: {orVals holdValues}]"] else []
  " ".intercalate ([itemName i.id] ++ lead ++ positional ++ rest ++ hold)

private meta def isStringy : SpecLang.FieldType → Bool
  | .color | .iconPath | .str => true
  | _ => false

open SpecLang in
private meta def bareWordVocab (i : ItemSpec) : List String :=
  i.fields.flatMap fun f =>
    if i.positional.contains f.id then []
    else match f.type with
      | .«enum» vs _ => if f.alt.isSome then [] else vs
      | .boolean _ => (boolSugar.filter (fun (_, bf, _) => bf == f.id)).map (·.1)
      | _ => []

private meta def isNumeric : SpecLang.FieldType → Bool
  | .number .. => true
  | _ => false

private meta def jsonNumOf? (stx : Syntax) : Option JsonNumber :=
  if let some n := stx.isNatLit? then
    some (JsonNumber.fromNat n)
  else if let some (m, sign, e) := stx.isScientificLit? then
    some (OfScientific.ofScientific m sign e)
  else none

open SpecLang in
private meta def checkBounds (ref : Syntax) (what : String) (f : FieldSpec)
    (n : JsonNumber) : TermElabM Unit := do
  let .number min max := f.type | return
  let v := n.toFloat
  if let some b := min then
    if (if b.exclusive then v ≤ b.value.toFloat else v < b.value.toFloat) then
      throwErrorAt ref m!"{what} must be \
        {if b.exclusive then "greater than" else "at least"} {toString b.value}"
  if let some b := max then
    if (if b.exclusive then v ≥ b.value.toFloat else v > b.value.toFloat) then
      throwErrorAt ref m!"{what} must be \
        {if b.exclusive then "less than" else "at most"} {toString b.value}"

open SpecLang in
private meta def checkEnumList (ref : Syntax) (what : String)
    (rules : EnumListRules) (chosen : List String) : TermElabM Unit := do
  for grp in rules.atMostOneOf do
    let hits := chosen.filter grp.contains
    if 2 ≤ hits.length then
      throwErrorAt ref m!"{what} allows at most one of {orVals grp}, \
        got {", ".intercalate hits}"
  for (k, allowed) in rules.narrows do
    if chosen.contains k then
      for c in chosen do
        unless allowed.contains c do
          throwErrorAt ref m!"'{k}' restricts {what} to {orVals allowed}; \
            '{c}' cannot join it"

private meta structure ArgView where
  ref : Syntax
  word? : Option String := none
  str? : Option String := none
  num? : Option JsonNumber := none

private meta def ArgView.ofToken (stx : Syntax) : ArgView :=
  { ref := stx
    word? := if stx.isIdent then some stx.getId.toString else none
    str? := stx.isStrLit?
    num? := jsonNumOf? stx }

/-- A word also reads as a string, so a color can be written unquoted. -/
private meta def ArgView.ofSel (stx : Syntax) : ArgView :=
  let word? := if stx.isOfKind selIdentKind
    then some (stx[0].getId.toString (escape := false)) else none
  { ref := stx
    word?
    str? := if stx.isOfKind selStrKind then stx[0].isStrLit? else word?
    num? := if stx.isOfKind selNumKind then stx[0].isNatLit?.map JsonNumber.fromNat
            else jsonNumOf? stx }

private meta def usageSuffix : Option String → MessageData
  | some u => m!"; usage: {u}"
  | none => m!""

open SpecLang in
private meta def enumWord (what : String) (vs : List String) (v : ArgView)
    (usage? : Option String := none) : TermElabM String := do
  let some w := v.word?
    | throwErrorAt v.ref m!"{what} expects {orVals vs}{usageSuffix usage?}"
  unless vs.contains w do
    throwErrorAt v.ref m!"unknown {what} '{w}' (expected {", ".intercalate vs})"
  return w

open SpecLang in
private meta def elabScalar (what : String) (f : FieldSpec) (v : ArgView)
    (usage? : Option String := none) : TermElabM FieldVal := do
  match f.type with
  | .color | .iconPath | .str =>
    let some s := v.str?
      | throwErrorAt v.ref m!"{what} expects a string{usageSuffix usage?}"
    return .str s
  | .number .. =>
    let some n := v.num?
      | throwErrorAt v.ref m!"{what} expects a number{usageSuffix usage?}"
    checkBounds v.ref what f n
    return .num n
  | .«enum» vs _ => return .«enum» (← enumWord what vs v usage?)
  | .boolean _ =>
    match v.word? with
    | some "true" => return .bool true
    | some "false" => return .bool false
    | _ => throwErrorAt v.ref m!"{what} expects true|false{usageSuffix usage?}"
  | _ => throwErrorAt v.ref m!"{what} does not take a scalar value"

open SpecLang in
private meta def elabBlockScalar (b : BlockSpec) (f : FieldSpec)
    (stx : Syntax) : TermElabM FieldVal := do
  match f.type with
  | .color | .iconPath | .str | .number .. | .«enum» .. =>
    elabScalar (fieldName f.id) f (.ofToken stx)
  | _ => throwErrorAt stx m!"({blockName b.id} …) cannot nest {fieldName f.id}"

open SpecLang in
private meta def elabBlock (usage : String) (b : BlockSpec) (stx : Syntax) :
    TermElabM (List (FieldId × FieldVal)) := do
  let mut set : Array (FieldId × FieldVal) := #[]
  let dup (ref : Syntax) (f : FieldId) (set : Array (FieldId × FieldVal)) :
      TermElabM Unit := do
    if set.any (·.1 == f) then
      throwErrorAt ref m!"duplicate {fieldName f} in ({blockName b.id} …)"
  for inner in blockArgs stx do
    if let some s := inner.isStrLit? then
      let some f := b.fields.find? (isStringy ·.type)
        | throwErrorAt inner m!"({blockName b.id} …) takes no string; usage: {usage}"
      dup inner f.id set
      set := set.push (f.id, .str s)
    else if let some n := jsonNumOf? inner then
      let some f := b.fields.find? (isNumeric ·.type)
        | throwErrorAt inner m!"({blockName b.id} …) takes no number; usage: {usage}"
      dup inner f.id set
      checkBounds inner s!"{fieldName f.id} of ({blockName b.id} …)" f n
      set := set.push (f.id, .num n)
    else if inner.isIdent then
      let w := inner.getId.toString
      let hits := b.fields.filter fun f =>
        match f.type with | .«enum» vs _ => vs.contains w | _ => false
      match hits with
      | [f] =>
        dup inner f.id set
        set := set.push (f.id, .«enum» w)
      | _ =>
        let vocab := b.fields.flatMap fun f =>
          match f.type with | .«enum» vs _ => vs | _ => []
        throwErrorAt inner m!"unknown word '{w}' in ({blockName b.id} …)\
          {if vocab.isEmpty then m!"" else m!" (expected {orVals vocab})"}"
    else if inner.isOfKind ``spytialBlockStx then
      let kw := inner[1].getId.toString
      let some f := b.fields.find? (fun f => fieldName f.id == kw)
        | throwErrorAt inner m!"({blockName b.id} …) has no field '{kw}'; \
            fields: {", ".intercalate (b.fields.map (fieldName ·.id))}"
      dup inner f.id set
      let args := blockArgs inner
      unless args.size == 1 do
        throwErrorAt inner m!"({kw} …) takes one value"
      set := set.push (f.id, ← elabBlockScalar b f args[0]!)
    else
      throwErrorAt inner m!"unexpected argument in ({blockName b.id} …); usage: {usage}"
  return b.fields.filterMap fun f => (set.find? (·.1 == f.id)).map fun (_, v) => (f.id, v)

open SpecLang in
private meta def elabAltForm (usage : String) (f : FieldSpec) (alt : AltForm)
    (vs : List String) (stx : Syntax) : TermElabM FieldVal := do
  let mut dir : Option String := none
  let mut blockVals : Array (FieldId × FieldVal) := #[]
  for inner in blockArgs stx do
    if inner.isIdent then
      let w := inner.getId.toString
      unless vs.contains w do
        throwErrorAt inner m!"unknown {fieldName f.id} direction '{w}' \
          (expected {", ".intercalate vs})"
      if dir.isSome then
        throwErrorAt inner m!"duplicate direction in ({fieldName f.id} …)"
      dir := some w
    else if inner.isOfKind ``spytialBlockStx then
      let bname := inner[1].getId.toString
      let some (bf, bid) := alt.blocks.find? (fun (bf, _) => fieldName bf == bname)
        | throwErrorAt inner m!"({fieldName f.id} …) nests only \
            {", ".intercalate (alt.blocks.map fun (bf, _) => s!"({fieldName bf} …)")}"
      if blockVals.any (·.1 == bf) then
        throwErrorAt inner m!"duplicate ({bname} …) in ({fieldName f.id} …)"
      blockVals := blockVals.push (bf, .block (← elabBlock usage (BlockSpec.of bid) inner))
    else
      throwErrorAt inner m!"({fieldName f.id} …) takes a direction and style \
        blocks; usage: {usage}"
  let some d := dir
    | throwErrorAt stx m!"({fieldName f.id} …) needs a direction ({", ".intercalate vs})"
  if blockVals.isEmpty then
    return .«enum» d
  return .block ((alt.enumField, .«enum» d) :: blockVals.toList)

open SpecLang in
private meta def elabBlockArg (item : ItemSpec) (usage : String) (inner : Syntax) :
    TermElabM (FieldId × FieldVal) := do
  let kw := inner[1].getId.toString
  match item.fields.find? (fun f => fieldName f.id == kw) with
  | none =>
    let blocks := item.fields.filterMap fun f =>
      match f.type, f.alt with
      | .block _, _ => some s!"({fieldName f.id} …)"
      | .«enum» _ _, some _ => some s!"({fieldName f.id} …)"
      | _, _ => none
    throwErrorAt inner m!"unknown block '({kw} …)'\
      {if blocks.isEmpty then m!"" else m!"; expected {", ".intercalate blocks}"}; \
      usage: {usage}"
  | some f =>
    match f.type, f.alt with
    | .block bid, _ => return (f.id, .block (← elabBlock usage (BlockSpec.of bid) inner))
    | .«enum» vs _, some alt => return (f.id, ← elabAltForm usage f alt vs inner)
    | _, _ =>
      throwErrorAt inner m!"'{kw}' is written {kw}: <value>; usage: {usage}"

open SpecLang in
private meta def elabKwValue (usage : String)
    (sel : Syntax → List SelForm → TermElabM Sel)
    (rel : Syntax → FieldSpec → TermElabM String) (f : FieldSpec) (v : Syntax) :
    TermElabM FieldVal := do
  match f.type with
  | .selector forms => return .sel (← sel v forms)
  | .relation =>
    if v.isOfKind selIdentKind then
      return .rel (← rel v[0] f)
    throwErrorAt v m!"{fieldName f.id}: expects a relation name"
  | .block _ => throwErrorAt v m!"write ({fieldName f.id} …) for a style block"
  | .enumList _ _ => throwErrorAt v m!"'{fieldName f.id}' is positional; usage: {usage}"
  | _ => elabScalar (fieldName f.id) f (.ofSel v)

open SpecLang in
private meta def trailingWordField? (item : ItemSpec) (w : String) :
    Option (FieldId × FieldVal) :=
  let sugar := boolSugar.find? fun (word, bf, _) =>
    word == w && item.fields.any fun f => f.id == bf && f.type matches .boolean _
  match sugar with
  | some (_, bf, v) => some (bf, .bool v)
  | none =>
    let hits := item.fields.filter fun f =>
      !item.positional.contains f.id && f.alt.isNone &&
        match f.type with | .«enum» vs _ => vs.contains w | _ => false
    match hits with
    | [f] => some (f.id, .«enum» w)
    | _ => none

open SpecLang in
private meta def arityForms (written : List String) (forms : List SelForm) :
    List ArityForm :=
  forms.map fun f =>
    { min := f.min, max := f.max, middlesIgnored := f.middlesIgnored,
      blockedBy := f.requires.bind fun r =>
        if written.contains (fieldName r) then none else some (fieldName r) }

open SpecLang in
meta def elabSpytialOp (scope : SelScope) (op : TSyntax `spytial_op) :
    TermElabM SpytialOp := do
  let (name, head) ←
    if op.raw.isOfKind ``spytialOpStx then
      pure (op.raw[0].getId.toString, op.raw[0])
    else if op.raw.isOfKind ``spytialAttrOp then
      pure ("attribute", op.raw[0])
    else
      throwErrorAt op "unexpected op syntax"
  let argStxs : Array (TSyntax `spytialOpArg) := op.raw[1].getArgs.map (⟨·⟩)
  withRef head do
    let some itemId := itemOfKey? name
      | throwErrorAt head m!"unknown Spytial op '{name}'; known ops: \
          {", ".intercalate ((allItems.map itemName).mergeSort (· < ·))}"
    let item := ItemSpec.of itemId
    let usage := itemUsage item
    -- a width can be conditional on a sibling field written after the selector,
    -- so the keywords are read off the argument list before any of it elaborates
    let written := argStxs.toList.filterMap fun a =>
      let inner := argInner a
      if inner.isOfKind ``spytialKwArg then some inner[0].getId.toString
      else if inner.isOfKind ``spytialBlockStx then some inner[1].getId.toString
      else none
    let sel (stx : Syntax) (forms : List SelForm) : TermElabM Sel := do
      if stx.isOfKind numLitKind then
        throwErrorAt stx m!"expected a selector; usage: {usage}"
      elabSelector scope (arityForms written forms) ⟨stx⟩
    let rel (stx : Syntax) (f : FieldSpec) : TermElabM String :=
      elabFieldName scope s!"{itemName item.id}.{fieldName f.id}" ⟨stx⟩
    let setField (fields : Array (FieldId × FieldVal)) (ref : Syntax)
        (f : FieldId) (v : FieldVal) : TermElabM (Array (FieldId × FieldVal)) := do
      if fields.any (·.1 == f) then
        throwErrorAt ref m!"duplicate {fieldName f}; usage: {usage}"
      return fields.push (f, v)
    let introFid := item.introduces.map (·.field)
    let mut fields : Array (FieldId × FieldVal) := #[]
    let mut hold : Option String := none
    let mut pending := item.positional
    let mut declStx : Option Syntax := none
    -- an entered variadic enum-list: its field, the words so far, the last ref
    let mut tail : Option (FieldSpec × Array String × Syntax) := none
    for i in [0:argStxs.size] do
      let inner := argInner argStxs[i]!
      if inner.isOfKind ``spytialBlockStx then
        let (fid, v) ← elabBlockArg item usage inner
        fields ← setField fields inner fid v
      else if inner.isOfKind ``spytialKwArg then
        let kw := inner[0].getId.toString
        let vstx := inner[2]
        if kw == holdField then
          unless item.supportsHold do
            throwErrorAt inner m!"{name} does not support hold; usage: {usage}"
          if hold.isSome then
            throwErrorAt inner m!"duplicate hold"
          hold := some (← enumWord holdField holdValues (.ofSel vstx))
        else
          match item.fields.find? (fun f => fieldName f.id == kw) with
          | none => throwErrorAt inner m!"unknown keyword '{kw}:'; usage: {usage}"
          | some f =>
            if item.positional.contains f.id then
              throwErrorAt inner m!"'{kw}' is a positional argument; usage: {usage}"
            fields ← setField fields inner f.id (← elabKwValue usage sel rel f vstx)
            if introFid == some f.id then declStx := some vstx
      else if let some (f, chosen, _) := tail then
        let .enumList vs _ := f.type | unreachable!
        let w ← enumWord (fieldName f.id) vs (.ofSel inner) usage
        if chosen.contains w then
          throwErrorAt inner m!"duplicate {fieldName f.id} '{w}'"
        tail := some (f, chosen.push w, inner)
      else if i == 0 && item.leadingSelector.isSome
          && (match pending.head?.bind item.field? with
              | some f => isNumeric f.type
              | none => true)
          && !inner.isOfKind numLitKind then
        let some lf := item.leadingSelector | unreachable!
        let some f := item.field? lf | unreachable!
        let .selector forms := f.type | unreachable!
        fields ← setField fields inner lf (.sel (← sel inner forms))
      else
        match pending with
        | fid :: rest =>
          pending := rest
          let some f := item.field? fid | unreachable!
          match f.type with
          | .enumList vs _ =>
            tail := some (f, #[← enumWord (fieldName fid) vs (.ofSel inner) usage], inner)
          | .selector forms =>
            fields ← setField fields inner fid (.sel (← sel inner forms))
          | .relation =>
            unless inner.isOfKind selIdentKind do
              throwErrorAt inner m!"expected a relation name; usage: {usage}"
            fields ← setField fields inner fid (.rel (← rel inner[0] f))
          | .str | .iconPath | .color | .«enum» .. | .number .. =>
            fields ← setField fields inner fid
              (← elabScalar (fieldName fid) f (.ofSel inner) usage)
            if introFid == some fid then declStx := some inner
          | _ =>
            throwErrorAt inner m!"unexpected argument; usage: {usage}"
        | [] =>
          let vocabMsg := match bareWordVocab item with
            | [] => m!""
            | vocab => m!" (expected {orVals vocab})"
          let some w := (ArgView.ofSel inner).word?
            | throwErrorAt inner m!"unexpected extra argument{vocabMsg}; usage: {usage}"
          let some (fid, v) := trailingWordField? item w
            | throwErrorAt inner m!"unexpected argument '{w}'{vocabMsg}; usage: {usage}"
          fields ← setField fields inner fid v
    if let some (f, chosen, ref) := tail then
      if let .enumList _ rules := f.type then
        checkEnumList ref (fieldName f.id) rules chosen.toList
      fields ← setField fields ref f.id (.enums chosen.toList)
    if let some fid := pending.head? then
      throwErrorAt head m!"missing {fieldName fid}; usage: {usage}"
    unless item.effectFields.isEmpty || fields.any (item.effectFields.contains ·.1) do
      throwErrorAt head m!"{name} sets nothing; usage: {usage}"
    -- table order, so the serialized spec is stable however the source ordered them
    let ordered := item.fields.filterMap fun f =>
      (fields.find? (·.1 == f.id)).map fun (_, v) => (f.id, v)
    let mut o : SpytialOp := { item := itemId, fields := ordered, hold }
    if let some stx := declStx then
      if let some (n, i) := o.introduces? then
        addIntroducedInfo stx n i.kind i.referencedBy (isBinder := true)
        if let some range ← getDeclarationRange? stx then
          o := { o with nameDecl := some { module := ← getMainModule, range } }
    return o

/-- Read back from the file, not reprinted, so a conflict report cites the line. -/
private meta def opSource? (op : TSyntax `spytial_op) : TermElabM (Option OpSource) := do
  unless spytial.source.get (← getOptions) do return none
  let some startPos := op.raw.getPos? | return none
  let some endPos := op.raw.getTailPos? | return none
  let fileMap ← getFileMap
  let text := (Substring.Raw.mk fileMap.source startPos endPos).toString.trim
  if text.isEmpty then return none
  let path := (← getFileName)
  let base := (System.FilePath.mk path).fileName.getD path
  return some { text, location := s!"{base}:{(fileMap.toPosition startPos).line}" }

meta def elabSpytialOps (scope : SelScope) (ops : Array (TSyntax `spytial_op))
    (attached? : Option SpytialSpec := none) : TermElabM SpytialSpec := do
  let introduce (scope : SelScope) (op : SpytialOp) : SelScope :=
    match op.introduces? with
    | some (n, i) => scope.introduce n
        { kind := i.kind, arity := i.arity, referencedBy := i.referencedBy,
          decl := op.nameDecl }
    | none => scope
  let mut scope := scope
  let mut spec : Array SpytialOp := #[]
  let mut spliced := false
  let mut splicedNames : NameSet := .empty
  for op in ops do
    if op.raw.isOfKind ``spytialSpliceStx then
      let some attached := attached?
        | throwErrorAt op "`..` splices the type's attached spec; \
            only a use-site `with [...]` has one"
      if spliced then
        throwErrorAt op "duplicate `..`"
      spliced := true
      spec := spec ++ attached
      scope := attached.foldl introduce scope
    else if op.raw.isOfKind ``spytialSpliceNamedStx then
      let id : Ident := ⟨op.raw[1]⟩
      let name ← realizeGlobalConstNoOverloadWithInfo id
      let some bound := getSpytialOps? (← getEnv) name
        | throwErrorAt id m!"'{name}' is not a `spytial_ops` declaration; \
            `spytial_ops <name> : <RootType> [<ops>]` binds one"
      -- `_anonymous` is the scrutinee with no type head: no root to check against
      unless bound.root == scope.root || scope.root == `_anonymous do
        throwErrorAt id m!"'{name}' is bound against '{bound.root}', but this op \
          list is elaborated against '{scope.root}'"
      if splicedNames.contains name then
        throwErrorAt id m!"duplicate `..{name}`"
      splicedNames := splicedNames.insert name
      spec := spec ++ bound.ops
      scope := bound.ops.foldl introduce scope
    else
      let o ← elabSpytialOp scope op
      spec := spec.push { o with source := ← opSource? op }
      scope := introduce scope o
  return spec.toList

meta def scopeForExpr (e : Expr) : MetaM SelScope := do
  let ty ← inferType e
  match ← typeHead? ty with
  | some n =>
    let seeds ← ty.getAppArgs.filterMapM fun a => do
      if (← Meta.whnf (← inferType a)) matches .sort _ then typeHead? a else pure none
    SelScope.ofType n seeds
  | none => return { root := `_anonymous, lenient := true }

/-! ## Widget payload -/

private meta def lookupTypeSpec (e : Expr) : MetaM (Option SpytialSpec) := do
  let ty ← inferType e
  let tyHead := (← whnf ty).getAppFn
  match tyHead with
  | .const n _ => do
    let env ← getEnv
    if isStructure env n then
      -- parents come nearest-first; compose root-first, self last
      let parents ← getAllParentStructures n
      let allNames := parents.reverse.toList ++ [n]
      match allNames.filterMap (getSpytialSpec? env ·) with
      | [] => return none
      | specs => return some specs.flatten
    else
      return getSpytialSpec? env n
  | _ => return none

private meta def elabTermInstantiated (t : Syntax) : TermElabM Expr := do
  let e ← Term.elabTerm t none
  Term.synthesizeSyntheticMVarsNoPostponing
  instantiateMVars e

private meta def elabRelationalized (t : Syntax) (cfg : WalkConfig := {}) :
    TermElabM (Expr × JsonDataInstance × Provenance) := do
  let e ← elabTermInstantiated t
  let (di, prov) ← relationalizeWithProvenance e cfg
  return (e, di, prov)

private meta def elabUseSiteOps (e : Expr) (ops : Array (TSyntax `spytial_op)) :
    TermElabM SpytialSpec := do
  let attached? ← lookupTypeSpec e
  if attached?.isNone then
    if let some splice := ops.find? (·.raw.isOfKind ``spytialSpliceStx) then
      logWarningAt splice m!"`..` splices the attached spec, but {← inferType e} has none"
  elabSpytialOps (← scopeForExpr e) ops (some (attached?.getD []))

private meta def elabSpytialPayload (t : Syntax) (ops? : Option (Array (TSyntax `spytial_op)))
    (cfg : WalkConfig) : TermElabM (JsonDataInstance × Option String) :=
  -- Both halves derive instances — the walk needs `SpytialIdentity`, the selector
  -- scope needs `SpytialEnum` — so wrapping only the walk would leave the spec
  -- half persisting its own. Both results are plain data.
  withoutModifyingEnv do
    let (e, di, prov) ← elabRelationalized t cfg
    let spec? ← match ops? with
      | some ops => some <$> elabUseSiteOps e ops
      | none => lookupTypeSpec e
    let spec? ← spec?.mapM fun s => liftM (resolveLeanSelectors e di prov s)
    return (di, ← spec?.mapM fun s => Lean.ofExcept (SpytialSpec.render s))

private meta def spytialProps (di : JsonDataInstance) (cndSpec? : Option String) : Json :=
  Json.mkObj <|
    [("dataInstance", toJson di)] ++
    match cndSpec? with
    | some s => [("cndSpec", toJson s)]
    -- absent, not null: the widget reads a missing `cndSpec` as free layout
    | none => []

/-- Public so out-of-tree frontends render what the infoview does. -/
public meta def spytialPayloadProps (t : Syntax)
    (ops? : Option (Array (TSyntax `spytial_op)) := none) (cfg : WalkConfig := {}) :
    TermElabM Json := do
  let (di, cndSpec?) ← elabSpytialPayload t ops? cfg
  return spytialProps di cndSpec?

private meta def optionalOps (stx : Syntax) : Option (Array (TSyntax `spytial_op)) :=
  if stx.getNumArgs == 0 then none
  else some (stx[2].getSepArgs.map (⟨·⟩))

/-- `#spytial <term>` displays a spatial relational diagram in the Lean infoview.
    A `with [<ops>]` list overrides the type's attached `spytial_spec`. -/
syntax (name := spytialCmd) "#spytial " term (" with " "[" spytial_op,*,? "]")? : command

@[command_elab spytialCmd]
meta def elabSpytialCmd : CommandElab := fun
  | stx@`(#spytial $t:term) => do
    let props ← liftTermElabM <| spytialPayloadProps t
    liftCoreM <| savePanelWidgetInfo SpytialWidget.javascriptHash (return props) stx
  | stx@`(#spytial $t:term with [$ops,*]) => do
    let props ← liftTermElabM <| spytialPayloadProps t (some ops.getElems)
    liftCoreM <| savePanelWidgetInfo SpytialWidget.javascriptHash (return props) stx
  | stx => throwError "Unexpected syntax {stx}."

/-- `spytial_spec <Type> [<ops>]` attaches the spec used by default for that type. -/
syntax (name := spytialSpecCmd) "spytial_spec " ident " [" spytial_op,*,? "]" : command

@[command_elab spytialSpecCmd]
meta def elabSpytialSpecCmd : CommandElab := fun
  | `(spytial_spec $id:ident [$ops,*]) => do
    let declName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
    liftTermElabM do
      let scope ← SelScope.ofType declName
      let spec ← elabSpytialOps scope ops.getElems
      setSpytialSpec declName spec
  | stx => throwError "Unexpected syntax {stx}."

/-- `spytial_ops <name> : <Type> [<ops>]` binds a reusable op list, elaborated
    against `<Type>` as root. The name is declared as an `SpytialOps` constant,
    so it namespaces and is reached through `open` and `export` like any other. -/
syntax (name := spytialOpsCmd) "spytial_ops " ident " : " ident " [" spytial_op,*,? "]" : command

@[command_elab spytialOpsCmd]
meta def elabSpytialOpsCmd : CommandElab := fun
  | `(spytial_ops $name:ident : $ty:ident [$ops,*]) => do
    let root ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo ty
    -- a `module` file makes declarations private by default, and a list nobody
    -- downstream can splice is useless
    let (declName, _) ← mkDeclName (← getCurrNamespace) { visibility := .public } name.getId
    let spec ← liftTermElabM do
      let scope ← SelScope.ofType root
      elabSpytialOps scope ops.getElems
    let declId := mkIdentFrom name (`_root_ ++ declName)
    elabCommand (← `(public meta def $declId : SpytialOps := .mk))
    liftCoreM <| setSpytialOps declName { root, ops := spec }
  | stx => throwError "Unexpected syntax {stx}."

/-- Registers a `CustomRelationalizer` def as the relationalizer for a type. -/
syntax (name := spytialRelationalizerCmd) "spytial_relationalizer " ident ident : command

@[command_elab spytialRelationalizerCmd]
meta def elabSpytialRelationalizerCmd : CommandElab := fun
  | `(spytial_relationalizer $typeId:ident $defId:ident) => do
    let typeName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo typeId
    let defName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo defId
    -- fail mistyped registrations here, not opaquely at dispatch
    liftTermElabM do
      let declType := (← getConstInfo defName).type
      unless (← Meta.isDefEq declType (Lean.mkConst ``CustomRelationalizer)) do
        throwError s!"'{defName}' must have type `CustomRelationalizer`"
    if isPrivateName defName then
      logWarningAt defId m!"'{defName}' is not `public`, so a `#spytial` on this \
        type from an importing module fails at render with `Unknown constant` — \
        declare it `public meta def`"
    liftCoreM <| setSpytialRelationalizer typeName defName
  | stx => throwError "Unexpected syntax {stx}."

/-- `#spytial.spec <term> with [<ops>]` prints the spec string handed to core. -/
syntax (name := spytialSpecDebug) "#spytial.spec " term " with " "[" spytial_op,*,? "]" : command

@[command_elab spytialSpecDebug]
meta def elabSpytialSpecDebug : CommandElab := fun
  | `(#spytial.spec $t:term with [$ops,*]) => do
    let specStr ← liftTermElabM do
      let e ← elabTermInstantiated t
      let spec ← elabUseSiteOps e ops.getElems
      -- the walk only resolves raw Lean selectors; skipping it also skips asking
      -- each walked type for a `SpytialIdentity`
      if spec.hasLeanRel then
        let (di, prov) ← relationalizeWithProvenance e
        Lean.ofExcept (← resolveLeanSelectors e di prov spec).render
      else
        Lean.ofExcept spec.render
    logInfo m!"{specStr}"
  | stx => throwError "Unexpected syntax {stx}."

/-- `#spytial.datum <term>` prints the generated JSON data instance. -/
syntax (name := spytialDatumDebug) "#spytial.datum " term : command

@[command_elab spytialDatumDebug]
meta def elabSpytialDatumDebug : CommandElab := fun
  | `(#spytial.datum $t:term) => do
    let (_, di, _) ← liftTermElabM <| elabRelationalized t
    logInfo m!"{(toJson di).pretty}"
  | stx => throwError "Unexpected syntax {stx}."

/-- `#spytial.proof <term>` draws a proof term without filtering Prop-typed fields. -/
syntax (name := spytialProofCmd) "#spytial.proof " term (" with " "[" spytial_op,*,? "]")? : command

@[command_elab spytialProofCmd]
meta def elabSpytialProofCmd : CommandElab := fun
  | stx@`(#spytial.proof $t:term) => do
    let props ← liftTermElabM <| spytialPayloadProps t none { filterProofs := false }
    liftCoreM <| savePanelWidgetInfo SpytialWidget.javascriptHash (return props) stx
  | stx@`(#spytial.proof $t:term with [$ops,*]) => do
    let props ← liftTermElabM <|
      spytialPayloadProps t (some ops.getElems) { filterProofs := false }
    liftCoreM <| savePanelWidgetInfo SpytialWidget.javascriptHash (return props) stx
  | stx => throwError "Unexpected syntax {stx}."

/-- `#spytial.proof.datum <term>` prints the JSON data instance in proof mode. -/
syntax (name := spytialProofDatumDebug) "#spytial.proof.datum " term : command

@[command_elab spytialProofDatumDebug]
meta def elabSpytialProofDatumDebug : CommandElab := fun
  | `(#spytial.proof.datum $t:term) => do
    let (_, di, _) ← liftTermElabM <| elabRelationalized t { filterProofs := false }
    logInfo m!"{(toJson di).pretty}"
  | stx => throwError "Unexpected syntax {stx}."

open Tactic in
/-- `#spytial` in tactic mode, with hypotheses and local bindings in scope. -/
syntax (name := spytialTactic) "spytial " term (" with " "[" spytial_op,*,? "]")? : tactic

open Tactic in
@[tactic spytialTactic]
meta def elabSpytialTactic : Tactic := fun stx => do
  match stx with
  | `(tactic| spytial $t:term) => do
    let props ← spytialPayloadProps t
    savePanelWidgetInfo SpytialWidget.javascriptHash (return props) stx
  | `(tactic| spytial $t:term with [$ops,*]) => do
    let props ← spytialPayloadProps t (some ops.getElems)
    savePanelWidgetInfo SpytialWidget.javascriptHash (return props) stx
  | _ => throwError "Unexpected syntax {stx}."

/-- A dotted atom never enters the token table — the lexer reads `spytial.proof`
    as one qualified identifier — so an atom-led rule can never fire. Without
    `includeIdent` the rule is not indexed under ident and is never tried. -/
meta def spytialProofKw : Lean.Parser.Parser :=
  Lean.Parser.nonReservedSymbol "spytial.proof" (includeIdent := true)

open Tactic in
/-- `spytial.proof <term>` is `#spytial.proof` in tactic mode. -/
syntax (name := spytialProofTactic) spytialProofKw term
  (" with " "[" spytial_op,*,? "]")? : tactic

open Tactic in
@[tactic spytialProofTactic]
meta def elabSpytialProofTactic : Tactic := fun stx => do
  -- a quotation pattern would lex `spytial.proof` as one dotted ident and never match
  let props ← spytialPayloadProps stx[1] (optionalOps stx[2]) { filterProofs := false }
  savePanelWidgetInfo SpytialWidget.javascriptHash (return props) stx

end

end SpytialLean
