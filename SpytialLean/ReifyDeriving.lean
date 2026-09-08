module

public import SpytialLean.ReifyCore
public meta import SpytialLean.TypeShape
public meta import Lean.Elab.Deriving.Basic
public meta import Lean.Elab.Deriving.Util

namespace SpytialLean.SpytialReify.Deriving

open Lean Meta Elab Command Term
open Lean.Elab.Deriving
open Lean.Parser.Term

private meta structure FieldPlan where
  type : Term
  relation : String
  recursive : Bool
  deriving Inhabited

private meta structure CtorPlan where
  name : Name
  label : String
  numParams : Nat
  fields : Array FieldPlan

private meta structure Plan where
  declName : Name
  indVal : InductiveVal
  argNames : Array Name
  ctors : Array CtorPlan

private meta structure DecoderNames where
  reifyAt : Name

private meta def unsupported (declName : Name) (message : MessageData) : TermElabM α :=
  throwError "cannot derive `SpytialReify` for `{.ofConstName declName}`: {message}"

/-- Render a first-order field type in generated decoder code. Only datatype parameters may occur
free; dependencies on earlier constructor fields are Tier 2. -/
private meta partial def renderFieldType (declName : Name)
    (params : Array (FVarId × Ident)) : Expr → TermElabM Term
  | .fvar id =>
    match params.findSome? (fun (param, name) => if param == id then some name else none) with
    | some name => pure name
    | none => unsupported declName m!"a constructor field depends on an earlier field"
  | .const name _ => `(@$(mkCIdent name):ident)
  | .lit (.natVal value) => pure (quote value)
  | .lit (.strVal value) => pure (quote value)
  | expression@(.app ..) => do
    let arguments ← expression.getAppArgs.mapM (renderFieldType declName params)
    match expression.getAppFn with
    | .const name _ => `(@$(mkCIdent name):ident $arguments:term*)
    | .fvar id =>
      let function ← renderFieldType declName params (.fvar id)
      `($function $arguments:term*)
    | function => unsupported declName m!"unsupported field type head{indentExpr function}"
  | .mdata _ expression => renderFieldType declName params expression
  | expression => unsupported declName m!"unsupported field type{indentExpr expression}"

private meta def mkPlan (declName : Name) : TermElabM Plan := do
  let indVal ← getConstInfoInduct declName
  unless indVal.all.length == 1 do
    unsupported declName m!"mutually recursive inductives are outside Tier 1"
  unless indVal.numIndices == 0 do
    unsupported declName m!"indexed inductive families are Tier 2"
  if indVal.isNested then
    unsupported declName m!"nested recursion is not yet supported"
  let argNames ← mkInductArgNames indVal
  let mut ctors := #[]
  for constructor in indVal.ctors do
    let info ← getConstInfoCtor constructor
    let binderNames := ctorDataBinderNames info
    let fields ← forallTelescopeReducing info.type fun variables _ => do
      let constructorParams := variables.extract 0 info.numParams
      let params := constructorParams.mapIdx fun index parameter =>
        (parameter.fvarId!, mkIdent argNames[index]!)
      let mut fields := #[]
      for index in [:info.numFields] do
        let field := variables[info.numParams + index]!
        let declaration ← field.fvarId!.getDecl
        let type ← whnf declaration.type
        if ← isProp type then
          unsupported declName m!"proof fields are outside Tier 1"
        if type.isSort then
          unsupported declName m!"`Sort`-valued fields are outside Tier 1"
        if type.isForall then
          unsupported declName m!"function fields are outside Tier 1"
        let recursive := type.isAppOf declName
        if type.getUsedConstants.contains declName && !recursive then
          unsupported declName m!"nested recursion is not yet supported"
        if recursive then
          let arguments := type.getAppArgs
          unless arguments.size == constructorParams.size do
            unsupported declName m!"non-regular recursive occurrence"
          for argument in arguments, parameter in constructorParams do
            unless ← isDefEq argument parameter do
              unsupported declName
                m!"recursive occurrences must use the datatype's parameters unchanged"
        fields := fields.push {
          type := ← renderFieldType declName params type
          relation := fieldRelName (shortName constructor) binderNames index
          recursive
        }
      return fields
    ctors := ctors.push {
      name := constructor
      label := shortName constructor
      numParams := info.numParams
      fields
    }
  return { declName, indVal, argNames, ctors }

private meta def mkNames (plan : Plan) : TermElabM DecoderNames := do
  let instanceName ← mkInstName ``SpytialReify plan.declName
  return { reifyAt := instanceName ++ `reifyAt }

open TSyntax.Compat in
private meta def mkBinders (plan : Plan) :
    TermElabM (Array (TSyntax ``bracketedBinder)) := do
  let mut binders := #[]
  for binder in ← mkImplicitBinders plan.argNames do
    binders := binders.push binder
  for binder in ← mkInstImplicitBinders ``SpytialReify plan.indVal plan.argNames do
    binders := binders.push binder
  return binders

private meta def mkCtorBody (names : DecoderNames) (constructor : CtorPlan)
    (datum root fuel : Ident) : TermElabM Term := do
  let mut fields : Array Ident := #[]
  let mut children : Array Ident := #[]
  for _ in constructor.fields do
    fields := fields.push (mkIdent (← mkFreshUserName `field))
    children := children.push (mkIdent (← mkFreshUserName `child))
  let value ← `($(mkCIdent constructor.name) $fields:term*)
  let mut body ← `(Except.ok $value)
  for index in (List.range constructor.fields.size).reverse do
    let field := fields[index]!
    let child := children[index]!
    let lookupError := mkIdent (← mkFreshUserName `error)
    let decodeError := mkIdent (← mkFreshUserName `error)
    let fieldPlan := constructor.fields[index]!
    let decode ← if fieldPlan.recursive then
      `($(mkIdent names.reifyAt) $datum:ident $child:ident $fuel:ident)
    else
      `(SpytialLean.SpytialReify.decodeAt (α := $(fieldPlan.type))
        $datum:ident $child:ident $fuel:ident)
    body ← `(match SpytialLean.ReifyDatum.child
        $datum:ident $root:ident $(quote fieldPlan.relation) with
      | Except.error $lookupError:ident => Except.error $lookupError:ident
      | Except.ok $child:ident =>
        match $decode:term with
        | Except.error $decodeError:ident => Except.error $decodeError:ident
        | Except.ok $field:ident => $body:term)
  return body

open TSyntax.Compat in
private meta def mkDecoder (plan : Plan) (names : DecoderNames) :
    TermElabM (TSyntax `command) := do
  let indApp ← mkInductiveApp plan.indVal plan.argNames
  let binders ← mkBinders plan
  let datum := mkIdent (← mkFreshUserName `datum)
  let root := mkIdent (← mkFreshUserName `root)
  let fuel := mkIdent (← mkFreshUserName `fuel)
  let nextFuel := mkIdent (← mkFreshUserName `fuel)
  let atom := mkIdent (← mkFreshUserName `atom)
  let error := mkIdent (← mkFreshUserName `error)

  let mut labelAlts : Array (TSyntax ``matchAlt) := #[]
  for constructor in plan.ctors do
    let body ← mkCtorBody names constructor datum root nextFuel
    labelAlts := labelAlts.push
      (← `(matchAltExpr| | $(quote constructor.label) => $body:term))
  labelAlts := labelAlts.push
    (← `(matchAltExpr| | _ => SpytialLean.reifyError "reify: unknown constructor"))
  let labelMatch ← `(match ($atom:ident).label with $labelAlts:matchAlt*)
  let atomMatch ← `(match SpytialLean.ReifyDatum.expectAtom
      $datum:ident $root:ident $(quote (shortName plan.declName)) with
    | Except.error $error:ident => Except.error $error:ident
    | Except.ok $atom:ident => $labelMatch:term)
  let body ← `(match $fuel:ident with
    | 0 => SpytialLean.reifyError "reify: decoder fuel exhausted"
    | $nextFuel:ident + 1 => $atomMatch:term)
  if plan.indVal.isRec then
    `(def $(mkIdent names.reifyAt):ident $binders:bracketedBinder*
        ($datum:ident : SpytialLean.ReifyDatum) ($root:ident : String) ($fuel:ident : Nat) :
        Except SpytialLean.ReifyError $indApp := $body:term
      termination_by $fuel:ident)
  else
    `(def $(mkIdent names.reifyAt):ident $binders:bracketedBinder*
        ($datum:ident : SpytialLean.ReifyDatum) ($root:ident : String) ($fuel:ident : Nat) :
        Except SpytialLean.ReifyError $indApp := $body:term)

open TSyntax.Compat in
private meta def mkInstance (plan : Plan) (names : DecoderNames) :
    TermElabM (TSyntax `command) := do
  let indApp ← mkInductiveApp plan.indVal plan.argNames
  let binders ← mkBinders plan
  let instanceName ← mkInstName ``SpytialReify plan.declName
  `(instance $(mkIdent instanceName):ident $binders:bracketedBinder* :
      SpytialLean.SpytialReify $indApp where
    reifyAt := $(mkIdent names.reifyAt))

/-- Derive a graph decoder for a Tier 1 algebraic datatype: one regular, first-order, non-indexed
inductive declaration, including a structure.

The generated decoder uses exactly the constructor labels and field-relation names emitted by the
existing relationalizer's default constructor walk. Type parameters are supported when they have
`SpytialReify` instances, and direct regular recursion is bounded by the datum's atom count.

Dependent/indexed families, mutual and nested recursion, and proof-, type-, or function-valued
fields are rejected with a diagnostic. A type with a custom relationalizer must provide a matching
manual `SpytialReify` instance instead of deriving this one. -/
public meta def mkSpytialReifyHandler (declNames : Array Name) : CommandElabM Bool := do
  unless declNames.size > 0 do return false
  let env ← getEnv
  unless declNames.all fun name => (env.find? name) matches some (.inductInfo _) do return false
  for declName in declNames do
    withoutExposeFromCtors declName do
      let plan ← liftTermElabM <| mkPlan declName
      let names ← liftTermElabM <| mkNames plan
      elabCommand (← liftTermElabM <| mkDecoder plan names)
      elabCommand (← liftTermElabM <| mkInstance plan names)
  return true

meta initialize
  registerDerivingHandler ``SpytialReify mkSpytialReifyHandler

end SpytialLean.SpytialReify.Deriving
