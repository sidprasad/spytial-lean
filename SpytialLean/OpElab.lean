module

public meta import SpytialLean.Attr
public meta import SpytialLean.SelectorElab
public meta import SpytialLean.SpecLang

namespace SpytialLean

open Lean Elab Command Term Meta

public section

/-! ## The op DSL

The head ident dispatches interpretation, so op keywords need no token-table
entries. -/

declare_syntax_cat spytial_op
declare_syntax_cat spytial_block_arg
declare_syntax_cat spytial_op_block
declare_syntax_cat spytial_field_form

syntax str : spytial_block_arg
syntax num : spytial_block_arg
syntax scientific : spytial_block_arg
syntax ident : spytial_block_arg
syntax spytial_op_block : spytial_block_arg
syntax spytial_field_form : spytial_block_arg

-- A parenthesized form is headed by a name the manifest declares, so `(some lo)`
-- never reads as one and falls through to `selExpr`; `atomic` lets any other head
-- backtrack past the `(`. A block heads an op argument, a block's field heads a
-- form nested inside it, and the two name sets are disjoint.
run_cmd do
  let declare (kind cat : Name) (heads : List String) : CommandElabM Unit := do
    let alts ← heads.eraseDups.mapM fun h => `(stx| &$(Syntax.mkStrLit h):str)
    let head ← match alts with
      | [] => throwError "the manifest declares no head for {kind}"
      | a :: rest => rest.foldlM (fun acc b => `(stx| $acc <|> $b)) a
    elabCommand (← `(syntax (name := $(mkIdent kind):ident)
      atomic("(" ($head) spytial_block_arg spytial_block_arg* ")") : $(mkIdent cat):ident))
  let altFields := SpecLang.allItems.flatMap fun i =>
    (SpecLang.ItemSpec.of i).fields.filter (·.alt.isSome)
  declare `spytialBlockStx `spytial_op_block
    (SpecLang.allBlocks.map SpecLang.blockName ++ altFields.map (SpecLang.fieldName ·.id))
  declare `spytialFieldStx `spytial_field_form
    (SpecLang.allBlocks.flatMap fun b =>
      (SpecLang.BlockSpec.of b).fields.map (SpecLang.fieldName ·.id))

syntax spytialKwArg := atomic(ident noWs ":" ) selExpr

syntax spytialOpArg := num <|> scientific <|> spytial_op_block <|> spytialKwArg <|> selExpr

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

/-- A block or field form's arguments, each stripped of its `spytial_block_arg` wrapper. -/
private meta def blockArgs (stx : Syntax) : Array Syntax :=
  (#[stx[2]] ++ stx[3].getArgs).map (·[0])

/-- `&"name"` wraps the token it matched in a `token.name` node. -/
private meta def blockHead (stx : Syntax) : String := stx[1][0].getAtomVal

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
/-- The op's usage line, synthesized from its table entry: the name, the
    positionals in table order, then every other field in its surface form. -/
private meta def itemUsage (i : ItemSpec) : String :=
  let lead := i.leadingSelector.toList.map fun f => s!"[<{fieldName f}>]"
  let positional := i.positional.filterMap fun fid => (i.field? fid).map (fieldUsage i)
  let rest := i.fields.filterMap fun f =>
    if i.positional.contains f.id || i.leadingSelector == some f.id then none
    else some (fieldUsage i f)
  let hold := if i.supportsHold then [s!"[hold: {orVals holdValues}]"] else []
  " ".intercalate ([itemName i.id] ++ lead ++ positional ++ rest ++ hold)

open SpecLang in
private meta def bareWordVocab (i : ItemSpec) : List String :=
  i.fields.flatMap fun f =>
    if i.positional.contains f.id then []
    else match f.type with
      | .«enum» vs _ => if f.alt.isSome then [] else vs
      | .boolean _ => (boolSugar.filter (fun (_, bf, _) => bf == f.id)).map (·.1)
      | _ => []

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
  -- exact: a `Float` rounds `1.0000000000000000000000001` onto the bound
  if let some b := min then
    if (if b.exclusive then !(b.value.lt n) else n.lt b.value) then
      throwErrorAt ref m!"{what} must be \
        {if b.exclusive then "greater than" else "at least"} {toString b.value}"
  if let some b := max then
    if (if b.exclusive then !(n.lt b.value) else b.value.lt n) then
      throwErrorAt ref m!"{what} must be \
        {if b.exclusive then "less than" else "at most"} {toString b.value}"

open SpecLang in
/-- The manifest's list rules: `atMostOneOf` forbids two values from one set;
    choosing a key of `narrows` restricts the whole list to its values. -/
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

/-! ### Scalar values

One reader serves the three places a scalar can sit — a nested block keyword,
a `name: value`, a positional argument — which differ only in how the syntax
carries the word/string/number, abstracted by `ArgView`. -/

private meta structure ArgView where
  ref : Syntax
  word? : Option String := none
  str? : Option String := none
  num? : Option JsonNumber := none

/-- A bare token, as blocks carry them. Only a string literal is a string. -/
private meta def ArgView.ofToken (stx : Syntax) : ArgView :=
  { ref := stx
    word? := if stx.isIdent then some stx.getId.toString else none
    str? := stx.isStrLit?
    num? := jsonNumOf? stx }

/-- A selector-expression leaf, as keyword values and positionals carry them.
    A word also reads as a string, so a color can be written unquoted. -/
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
/-- One scalar against a field's table entry. Callers dispatch the non-scalar
    types (selector, relation, block, enum-list) themselves: what those mean
    differs by position. -/
private meta def elabScalar (what : String) (f : FieldSpec) (v : ArgView)
    (usage? : Option String := none) : TermElabM FieldVal := do
  match f.type with
  | .color | .iconPath | .str =>
    let some s := v.str?
      | throwErrorAt v.ref m!"{what} expects a string{usageSuffix usage?}"
    if f.type matches .color then Editor.colorLiteral v.ref s
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

/-! ### Style blocks -/

open SpecLang in
/-- The single scalar of a nested `(fieldName value)` keyword in a block. -/
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
    if inner.isOfKind strLitKind then
      let some f := b.fields.find? (·.type.isStringy)
        | throwErrorAt inner m!"({blockName b.id} …) takes no string; usage: {usage}"
      dup inner f.id set
      set := set.push (f.id, ← elabScalar (fieldName f.id) f (.ofToken inner))
    else if let some n := jsonNumOf? inner then
      let some f := b.fields.find? (·.type.isNumeric)
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
    else if inner.isOfKind ``spytialFieldStx then
      let kw := blockHead inner
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
      let bname := blockHead inner
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
  let kw := blockHead inner
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
/-- `name: value` for everything a keyword can carry. -/
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
/-- A bare word past the positionals: bool sugar, else the unique optional
    enum field that lists the word. -/
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
/-- A field's accepted widths in one op: a form whose `requires` names a field
    the op does not write is unavailable there. -/
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
    Editor.highlight head .keyword
    let usage := itemUsage item
    -- A form can make a width conditional on a sibling field, which may be
    -- written after the selector, so the keywords are read off the argument
    -- list before any of it elaborates.
    let written := argStxs.toList.filterMap fun a =>
      let inner := argInner a
      if inner.isOfKind ``spytialKwArg then some inner[0].getId.toString
      else if inner.isOfKind ``spytialBlockStx then some (blockHead inner)
      else none
    let isNumber (stx : Syntax) : Bool :=
      stx.isOfKind numLitKind || stx.isOfKind scientificLitKind
    let sel (stx : Syntax) (forms : List SelForm) : TermElabM Sel := do
      if isNumber stx then
        throwErrorAt stx m!"expected a selector; usage: {usage}"
      elabSelector scope (arityForms written forms) ⟨stx⟩
    -- a bare sugar word is never a selector, even where a selector may lead
    let isTrailingWord (stx : Syntax) : Bool :=
      (ArgView.ofSel stx).word?.any fun w => (trailingWordField? item w).isSome
    let rel (stx : Syntax) (f : FieldSpec) : TermElabM String :=
      elabFieldName scope s!"{itemName item.id}.{fieldName f.id}" ⟨stx⟩
    let setField (fields : Array (FieldId × FieldVal)) (ref : Syntax)
        (f : FieldId) (v : FieldVal) : TermElabM (Array (FieldId × FieldVal)) := do
      if fields.any (·.1 == f) then
        throwErrorAt ref m!"duplicate {fieldName f}; usage: {usage}"
      return fields.push (f, v)
    let mut fields : Array (FieldId × FieldVal) := #[]
    let mut hold : Option String := none
    let mut pending := item.positional
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
      else if let some (f, chosen, _) := tail then
        let .enumList vs _ := f.type | unreachable!
        let w ← enumWord (fieldName f.id) vs (.ofSel inner) usage
        if chosen.contains w then
          throwErrorAt inner m!"duplicate {fieldName f.id} '{w}'"
        tail := some (f, chosen.push w, inner)
      else if i == 0 && item.leadingSelector.isSome
          && (match pending.head?.bind item.field? with
              | some f => f.type.isNumeric
              | none => true)
          && !isNumber inner && !isTrailingWord inner then
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
    return { item := itemId, fields := ordered, hold }

/-- The op as the user wrote it, with where they wrote it. Read back from the
    file rather than reprinted from syntax, so what core cites in a conflict
    report is the text on the line. -/
private meta def opSource? (op : TSyntax `spytial_op) : TermElabM (Option OpSource) := do
  unless spytial.source.get (← getOptions) do return none
  let some startPos := op.raw.getPos? | return none
  let some endPos := op.raw.getTailPos? | return none
  let fileMap ← getFileMap
  let text := (Substring.Raw.mk fileMap.source startPos endPos).toString.trimAscii.copy
  if text.isEmpty then return none
  let path := (← getFileName)
  let base := (System.FilePath.mk path).fileName.getD path
  return some { text, location := s!"{base}:{(fileMap.toPosition startPos).line}" }

/-- Elaborate an op list, bringing each op's introduced names (groups, inferred
    edges) into scope for the ops after it. A `..` element splices `attached?`
    at that position; `none` means the context has no attached spec to splice.
    A `..name` element splices the op list bound by `spytial_ops name`, which
    must share this list's root type. -/
meta def elabSpytialOps (scope : SelScope) (ops : Array (TSyntax `spytial_op))
    (attached? : Option SpytialSpec := none) : TermElabM SpytialSpec := do
  let introduce (scope : SelScope) (op : SpytialOp) : SelScope :=
    match op.introduces? with
    | some (n, i) => scope.introduce n { arity := i.arity, referencedBy := i.referencedBy }
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

end

end SpytialLean
