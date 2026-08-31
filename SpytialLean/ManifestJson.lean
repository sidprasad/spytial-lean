module

public import Lean
public meta import Lake.Util.JsonObject

namespace SpytialLean.ManifestJson

open Lean Lake Elab Command

export Lake (JsonObject)

public section

/-! # Reading a language manifest

`deriving FromJson` composes error paths already, so nothing here threads one by
hand. What it does not cover is the tagged-union convention and which element of
an array failed. -/

-- v4.32.2 doesn't include FromJson Char
meta instance : FromJson Char where
  fromJson? j := do
    let s ← j.getStr?
    let [c] := s.toList | throw s!"expected a single character, got {s.quote}"
    return c

meta instance : Repr JsonObject := ⟨fun o _ => Std.Format.text (Json.obj o).compress⟩

meta def eachKeyedBy (α) [FromJson α] (key : String) (js : Array Json) :
    Except String (Array α) :=
  js.mapM fun j => (fromJson? j).mapError fun e =>
    match j.getObjValAs? String key with
    | .ok name => s!"{name}: {e}"
    | .error _ => e

/-- An absent member decodes as `null`, which is what makes an `Option` field
    optional and every other field name itself. -/
meta def member (α) [FromJson α] (j : Json) (key : String) : Except String α := do
  match (← (fromJson? j : Except String JsonObject)).getJson? key with
  | some v => (fromJson? v).mapError fun e => s!"{key}: {e}"
  | none => (fromJson? Json.null).mapError fun _ => s!"property not found: {key}"

meta def spelling (j : Json) : Except String String := j.getStr?

/-- Refuses a member outside `known`, so an object that grows one upstream
    fails the build rather than having it read past. -/
meta def onlyMembers (known : List String) (o : JsonObject) : Except String Unit :=
  match o.toArray.toList.find? fun (k, _) => !known.contains k with
  | some (k, _) => .error s!"no representation for {k.quote}"
  | none => .ok ()

/-! ## Declaring the derived surface -/

meta def manifest! (what : String) (parsed : Except String α) : CommandElabM α :=
  match parsed with
  | .ok m => return m
  | .error e => throwError "{what}: {e}"

meta def enumCtor (ns enum : Name) (id : String) : Ident :=
  mkIdent (ns ++ enum ++ Name.mkSimple id)

meta def declareEnum (enum : Name) (ids : List String) : CommandElabM Unit := do
  let ctors ← ids.mapM fun s =>
    `(Lean.Parser.Command.ctor| | $(mkIdent (Name.mkSimple s)):ident)
  elabCommand (← `(public meta inductive $(mkIdent enum):ident where
      $(ctors.toArray)*
      deriving Repr, DecidableEq, Inhabited, Hashable))

meta def declareAll (all enum : Name) (ids : List String) : CommandElabM Unit := do
  let ns ← getCurrNamespace
  let refs := (ids.map (enumCtor ns enum)).toArray
  elabCommand (← `(public meta def $(mkIdent all):ident :
      List $(mkIdent enum):ident := [$refs,*]))

meta def declareNames (fn enum : Name) (ids : List String) : CommandElabM Unit := do
  let ns ← getCurrNamespace
  let alts : Array (TSyntax ``Lean.Parser.Term.matchAlt) ← ids.toArray.mapM fun s =>
    `(Lean.Parser.Term.matchAltExpr| | $(enumCtor ns enum s):term => $(quote s):term)
  elabCommand (← `(public meta def $(mkIdent fn):ident (id : $(mkIdent enum):ident) :
      String := match id with $alts:matchAlt*))

meta def declareDef (name : Name) (ty val : Term) : CommandElabM Unit := do
  elabCommand (← `(public meta def $(mkIdent name):ident : $ty := $val))

/-! ## Declaring a tagged union

    json_union ArityRule on "rule" where
      | slot (index : Nat)
      | fixed (width : Nat)
      | sum

declares the inductive and its decoder from one list: a constructor's fields
name the sibling members that carry them, and the constructor name is the JSON
spelling unless written out (`| "n-ary" => nary`). Without `on`, the value is
the tag itself. -/

syntax jsonField := "(" ident " : " term ")"
syntax jsonAlt := ppLine "| " (str " => ")? ident jsonField*
syntax (name := jsonUnion)
  (docComment)? "json_union " ident (" on " str)? " where" jsonAlt* : command

elab_rules : command
  | `($[$doc:docComment]? json_union $name:ident $[on $tag:str]? where $alts:jsonAlt*) => do
    -- Names shared across quotations go through `mkIdent`; a literal would be
    -- hygiene-mangled and the arms would not see the binding.
    let subject := mkIdent `j
    let mut ctors := #[]
    let mut arms := #[]
    for alt in alts do
      let `(jsonAlt| | $[$spelling?:str => ]? $ctor:ident $fields:jsonField*) := alt
        | throwErrorAt alt "expected `| ctor (field : Type)*`, with `\"spelling\" =>` \
            ahead of a ctor spelled differently in JSON"
      let spelling := spelling?.getD (Syntax.mkStrLit (ctor.getId.toString (escape := false)))
      if tag.isNone && !fields.isEmpty then
        throwErrorAt alt "an untagged union reads the value itself, so its \
          alternatives take no fields; give the union an `on \"member\"`"
      let mut binders := #[]
      let mut args := #[]
      for field in fields do
        let `(jsonField| ($fname:ident : $ftype:term)) := field
          | throwErrorAt field "expected `(name : Type)`"
        binders := binders.push (← `(Lean.Parser.Term.bracketedBinderF| ($fname : $ftype)))
        args := args.push
          (← `(← member _ $subject:ident $(quote (fname.getId.toString (escape := false)))))
      ctors := ctors.push (← `(Lean.Parser.Command.ctor| | $ctor:ident $binders*))
      let built ← `(do return $(mkIdent (name.getId ++ ctor.getId)):ident $args*)
      arms := arms.push (← `(Lean.Parser.Term.matchAltExpr| | $spelling:str => $built))
    -- No `DecidableEq`: it has no handler for a union that nests itself.
    -- The linter reads the spliced field binders as unused term bindings.
    let ind ← `($[$doc:docComment]? public meta inductive $name:ident where
      $ctors*
      deriving Repr, Inhabited)
    elabCommand (← `(set_option linter.unusedVariables false in $ind:command))
    let unknown := match tag with
      | some t => s!"no representation for {t.getString} "
      | none => "no representation for "
    let fallback ← `(Lean.Parser.Term.matchAltExpr|
      | t => .error ($(quote unknown) ++ t.quote))
    let tagOf ← match tag with
      | some t => `(member String $subject:ident $t)
      | none => `(spelling $subject:ident)
    let decide ← `(fun t => match t with $arms:matchAlt* $fallback:matchAlt)
    -- `partial` plus the self-instance is what lets an alternative nest the
    -- union, as a template's `optional` holds template items.
    let decoder := mkIdent (name.getId ++ `ofJson)
    elabCommand (← `(public meta partial def $decoder:ident
        ($subject:ident : Json) : Except String $name:ident :=
      let _self : FromJson $name:ident := ⟨$decoder:ident⟩
      $tagOf >>= $decide))
    elabCommand (← `(public meta instance : FromJson $name:ident := ⟨$decoder:ident⟩))
    let members := ((tag.map (·.getString)).toList
        ++ alts.toList.flatMap (fun (alt : TSyntax ``jsonAlt) =>
      match alt with
      | `(jsonAlt| | $[$_ => ]? $_ $fields:jsonField*) =>
        fields.toList.filterMap fun (field : TSyntax ``jsonField) =>
          match field with
          | `(jsonField| ($fname:ident : $_)) => some (fname.getId.toString (escape := false))
          | _ => none
      | _ => [])).eraseDups
    elabCommand (← `(public meta def $(mkIdent (name.getId ++ `memberNames)):ident :
        List String := $(quote members)))

/-! ## Declaring a closed record reader

    json_record JOp
    json_record JField ignoring JFieldType.memberNames "description"

reads the named structure's fields back off the environment and declares its
decoder: one `member` per field, refusing any member outside the field list and
the `ignoring` entries. A string entry names a member left unread on purpose; an
identifier splices another reader's `memberNames` when two readers share one
object. -/

syntax (name := jsonRecord) "json_record " ident ("ignoring" (str <|> ident)+)? : command

@[command_elab jsonRecord] meta def elabJsonRecord : CommandElab := fun stx => do
  let name : Ident := ⟨stx[1]⟩
  let structName ← resolveGlobalConstNoOverload name
  let fields := getStructureFields (← getEnv) structName
  let keys := fields.toList.map (·.toString (escape := false))
  elabCommand (← `(public meta def $(mkIdent (name.getId ++ `memberNames)):ident :
      List String := $(quote keys)))
  let mut allowed : Term ← `(($(quote keys) : List String))
  for entry in (if stx[2].getNumArgs == 0 then #[] else stx[2][1].getArgs) do
    allowed ← match entry.isStrLit? with
      | some s => `($allowed ++ [$(Syntax.mkStrLit s)])
      | none => `($allowed ++ ($(⟨entry⟩) : List String))
  let subject := mkIdent `j
  let args ← fields.mapM fun f =>
    `(← member _ $subject:ident $(quote (f.toString (escape := false))))
  let decoder := mkIdent (name.getId ++ `ofJson)
  elabCommand (← `(public meta def $decoder:ident ($subject:ident : Json) :
      Except String $name:ident := do
    onlyMembers $allowed (← fromJson? $subject:ident)
    return $(Syntax.mkCApp (structName ++ `mk) args)))
  elabCommand (← `(public meta instance : FromJson $name:ident := ⟨$decoder:ident⟩))

end

end SpytialLean.ManifestJson
