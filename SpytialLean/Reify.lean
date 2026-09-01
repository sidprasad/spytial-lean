module

public meta import SpytialLean.Relationalizer

namespace SpytialLean

open Lean Meta

/-!
# Reifying relational data

`reify expectedType datum` reconstructs a closed Lean expression from a rooted
relational datum. The expected type is essential: atom labels contain short
constructor names for display, not globally unique declaration names.

This first implementation deliberately accepts a small, checkable fragment:

* the root type and every reconstructed field type are closed;
* values reduce to `Nat`/`String` literals or applications of inductive
  constructors;
* constructor fields are data, not functions or types; omitted proof fields
  must be closed and decidable, so the reifier can rebuild a proof;
* no custom relationalizer or `Raw`/`Viewed` wrapper is active; and
* every atom and binary field edge in the datum is consumed.

The ordinary visualization walk may deliberately merge structurally unequal
values according to `SpytialIdentity`. `relationalizeForReify` instead walks in
hereditary `asWritten` mode so that the fidelity path preserves occurrences.

The reifier does not receive the original value. `certifyReifyRoundTrip`
relationalizes a concrete expression through the fidelity path, reifies the
result, and asks Lean's kernel to accept `rfl` at the resulting equality. This
is a certificate for that fully instantiated value, not a universal theorem
about `MetaM`.
-/

/-- Relational data together with the atom from which reconstruction starts.
    Atom-array order is not semantically significant. -/
public meta structure ReifyDatum where
  root : String
  data : JsonDataInstance

/-- Relationalize a closed value without consulting identity declarations, so
    distinct constructor-field occurrences remain available to the reifier. -/
public meta def relationalizeForReify (original : Expr) : MetaM ReifyDatum := do
  unless isClosedValue original do
    throwError "relationalize for reify: the original expression is not fully instantiated"
  withoutModifyingEnv do
    let (root, state) ← (walkExpr {} original { mode := .asWritten }).run {}
    return { root, data := state.toDataInstance }

private meta structure ReifyIndex where
  atoms : Std.HashMap String JsonAtom
  edges : Std.HashMap (String × String) String
  root : String

private meta structure ReifyState where
  active : Std.HashSet String := {}
  usedAtoms : Std.HashSet String := {}
  usedEdges : Std.HashSet (String × String) := {}
  expectedTypes : Std.HashMap String Expr := {}
  values : Std.HashMap String Expr := {}

private meta abbrev ReifyM := StateT ReifyState MetaM

private meta def kernelDefEq (left right : Expr) : MetaM Bool := do
  match Kernel.isDefEq (← getEnv) (← getLCtx) left right with
  | .ok answer => return answer
  | .error _ => return false

private meta def indexData (datum : ReifyDatum) : MetaM ReifyIndex := do
  let data := datum.data
  let mut atoms : Std.HashMap String JsonAtom := {}
  for atom in data.atoms do
    if atoms.contains atom.id then
      throwError "reify: duplicate atom id '{atom.id}'"
    atoms := atoms.insert atom.id atom

  let mut relationNames : Std.HashSet String := {}
  let mut edges : Std.HashMap (String × String) String := {}
  for relation in data.relations do
    if relationNames.contains relation.name then
      throwError "reify: duplicate relation name '{relation.name}'"
    relationNames := relationNames.insert relation.name
    if relation.tuples.isEmpty then
      throwError "reify: empty relation '{relation.name}' is outside the reifiable fragment"
    unless relation.types.size == 2 do
      throwError "reify: relation '{relation.name}' has arity {relation.types.size}; expected 2"
    for tuple in relation.tuples do
      unless tuple.atoms.size == 2 do
        throwError "reify: a tuple in '{relation.name}' has arity {tuple.atoms.size}; expected 2"
      unless tuple.types.size == 2 do
        throwError "reify: tuple types in '{relation.name}' do not describe a binary edge"
      let parentId := tuple.atoms[0]!
      let childId := tuple.atoms[1]!
      let some parent := atoms[parentId]?
        | throwError "reify: relation '{relation.name}' refers to unknown atom '{parentId}'"
      let some child := atoms[childId]?
        | throwError "reify: relation '{relation.name}' refers to unknown atom '{childId}'"
      unless tuple.types[0]! == parent.type && tuple.types[1]! == child.type do
        throwError "reify: tuple types in '{relation.name}' disagree with their atoms"
      let key := (parentId, relation.name)
      if edges.contains key then
        throwError "reify: '{relation.name}' gives atom '{parentId}' more than one child"
      edges := edges.insert key childId
  unless atoms.contains datum.root do
    throwError "reify: the root atom '{datum.root}' is not present in the datum"
  return { atoms, edges, root := datum.root }

private meta def childFor (index : ReifyIndex) (parentId relation : String) : ReifyM String := do
  let key := (parentId, relation)
  let some childId := index.edges[key]?
    | throwError "reify: atom '{parentId}' has no '{relation}' field edge"
  modify fun state => { state with usedEdges := state.usedEdges.insert key }
  return childId

private meta def rememberExpectedType (atomId : String) (expectedType : Expr) : ReifyM Unit := do
  let state ← get
  if let some previous := state.expectedTypes[atomId]? then
    unless ← kernelDefEq previous expectedType do
      throwError "reify: shared atom '{atomId}' is used at incompatible Lean types"
  else
    modify fun state =>
      { state with expectedTypes := state.expectedTypes.insert atomId expectedType }

private meta def quotedString? (label : String) : Option String :=
  if label.startsWith "\"" && label.endsWith "\"" then
    some ((label.drop 1).dropEnd 1).toString
  else
    none

private meta partial def reifyAt (index : ReifyIndex) (expectedType : Expr)
    (atomId : String) : ReifyM Expr := do
  let expectedType ← instantiateMVars expectedType
  unless isClosedValue expectedType do
    throwError "reify: expected type for atom '{atomId}' is not fully instantiated"
  rememberExpectedType atomId expectedType

  let state ← get
  if state.active.contains atomId then
    throwError "reify: cycle through atom '{atomId}'"
  if let some value := state.values[atomId]? then
    return value

  let some atom := index.atoms[atomId]?
    | throwError "reify: unknown atom '{atomId}'"
  let expectedSignature ← sigOfType expectedType
  unless atom.type == expectedSignature do
    throwError "reify: atom '{atomId}' has type label '{atom.type}', expected '{expectedSignature}'"
  modify fun state => { state with
    active := state.active.insert atomId
    usedAtoms := state.usedAtoms.insert atomId }

  let typeHead ← typeHead? expectedType
  let value ← match typeHead with
    | some ``Nat =>
      match atom.label.toNat? with
      | some value => pure (mkRawNatLit value)
      | none => reifyConstructor index expectedType atom
    | some ``String =>
      match quotedString? atom.label with
      | some value => pure (mkStrLit value)
      | none => reifyConstructor index expectedType atom
    | _ => reifyConstructor index expectedType atom

  let value ← instantiateMVars value
  unless isClosedValue value do
    throwError "reify: reconstructed atom '{atomId}' still contains metavariables"
  let actualType ← instantiateMVars (← inferType value)
  unless ← kernelDefEq actualType expectedType do
    throwError "reify: reconstructed atom '{atomId}' has the wrong Lean type"
  modify fun state => { state with
    active := state.active.erase atomId
    values := state.values.insert atomId value }
  return value
where
  reifyConstructor (index : ReifyIndex) (expectedType : Expr) (atom : JsonAtom) :
      ReifyM Expr := do
    let expectedType ← whnf expectedType
    let some typeName := expectedType.getAppFn.constName?
      | throwError "reify: expected type for atom '{atom.id}' is not an inductive application"
    let env ← getEnv
    if (getSpytialRelationalizerName? env typeName).isSome then
      throwError "reify: type '{typeName}' has a custom relationalizer"
    let some (.inductInfo inductiveInfo) := env.find? typeName
      | throwError "reify: expected type '{typeName}' is not inductive"
    let constructors := inductiveInfo.ctors.filter fun ctorName => shortName ctorName == atom.label
    let some ctorName := constructors[0]?
      | throwError "reify: '{atom.label}' is not a constructor of '{typeName}'"
    unless constructors.length == 1 do
      throwError "reify: constructor label '{atom.label}' is ambiguous in '{typeName}'"

    let ctorInfo ← getConstInfoCtor ctorName
    let ctor ← mkConstWithFreshMVarLevels ctorName
    let (arguments, _, resultType) ← forallMetaTelescopeReducing (← inferType ctor)
    unless arguments.size == ctorInfo.numParams + ctorInfo.numFields do
      throwError "reify: unexpected telescope for constructor '{ctorName}'"
    let expectedArguments := expectedType.getAppArgs
    unless expectedArguments.size >= ctorInfo.numParams do
      throwError "reify: expected type '{expectedType}' omits constructor parameters"
    for index in [:ctorInfo.numParams] do
      unless ← isDefEq arguments[index]! expectedArguments[index]! do
        throwError "reify: parameter {index} of '{ctorName}' does not match the expected type"

    let binderNames := ctorDataBinderNames ctorInfo
    let mut fieldNames : Std.HashSet String := {}
    for fieldIndex in [:ctorInfo.numFields] do
      let argumentIndex := ctorInfo.numParams + fieldIndex
      let argument := arguments[argumentIndex]!
      let fieldType ← instantiateMVars (← inferType argument)
      if ← isProp fieldType then
        let proof ← try
            mkDecideProof fieldType
          catch _ =>
            throwError "reify: omitted proof field {fieldIndex} of '{ctorName}' is not decidable"
        unless ← kernelDefEq (← inferType proof) fieldType do
          throwError "reify: omitted proof field {fieldIndex} of '{ctorName}' is false"
        unless ← isDefEq argument proof do
          throwError "reify: could not assign proof field {fieldIndex} of '{ctorName}'"
        continue
      if (← whnf fieldType).isSort then
        throwError "reify: type field {fieldIndex} of '{ctorName}' is not represented"
      if (← whnf fieldType).isForall then
        throwError "reify: function field {fieldIndex} of '{ctorName}' is not reifiable"
      let relation := fieldRelName (shortName ctorName) binderNames fieldIndex
      if fieldNames.contains relation then
        throwError "reify: constructor '{ctorName}' has duplicate field name '{relation}'"
      fieldNames := fieldNames.insert relation
      let childId ← childFor index atom.id relation
      let child ← reifyAt index fieldType childId
      unless ← isDefEq argument child do
        throwError "reify: field '{relation}' of '{ctorName}' has the wrong Lean type"

    unless ← isDefEq resultType expectedType do
      throwError "reify: constructor '{ctorName}' does not build the expected type"
    return mkAppN ctor arguments

/-- Reconstruct a closed constructor value from a rooted relational datum at a supplied type. -/
public meta def reify (expectedType : Expr) (datum : ReifyDatum) : MetaM Expr :=
  withoutModifyingState <| withNewMCtxDepth do
    unless isClosedValue expectedType do
      throwError "reify: the expected type is not fully instantiated"
    let index ← indexData datum
    let (value, state) ← (reifyAt index expectedType index.root).run {}
    unless state.usedAtoms.size == index.atoms.size do
      throwError "reify: the datum contains atoms unreachable from its root"
    unless state.usedEdges.size == index.edges.size do
      throwError "reify: the datum contains field edges not used by the reconstructed value"
    return value

/-- Evidence produced for one closed value by the actual relationalizer/reifier pipeline. -/
public meta structure ReifyCertificate where
  datum : ReifyDatum
  reconstructed : Expr
  equalityType : Expr
  equalityProof : Expr

/--
Run the real walker and reifier on `original`, then construct an `rfl` proof of
`original = reconstructed`.  The kernel accepts the proof exactly when the two
closed constructor values are definitionally (hence structurally) equal.
-/
public meta def certifyReifyRoundTrip (original : Expr) : MetaM ReifyCertificate := do
  unless isClosedValue original do
    throwError "reify round trip: the original expression is not fully instantiated"
  let expectedType ← instantiateMVars (← inferType original)
  unless isClosedValue expectedType do
    throwError "reify round trip: the original type is not fully instantiated"
  let datum ← relationalizeForReify original
  let reconstructed ← reify expectedType datum
  unless ← kernelDefEq original reconstructed do
    throwError "reify round trip: reconstructed value is not structurally equal to the original"
  let equalityType ← mkAppM ``Eq #[original, reconstructed]
  let equalityProof ← mkEqRefl original
  let checkedType ← match Kernel.check (← getEnv) (← getLCtx) equalityProof with
    | .ok checkedType => pure checkedType
    | .error error =>
      throwError m!"reify round trip: the kernel rejected the equality certificate: \
        {error.toMessageData (← getOptions)}"
  unless ← kernelDefEq checkedType equalityType do
    throwError "reify round trip: the kernel checked the certificate at the wrong type"
  return { datum, reconstructed, equalityType, equalityProof }

end SpytialLean
