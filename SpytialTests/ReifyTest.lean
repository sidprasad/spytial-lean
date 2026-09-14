module

public import Lean.ToExpr
public import SpytialLean.Identity
public import SpytialLean.ReifyCore
public import SpytialLean.ReifyInstances
public meta import SpytialLean.Reify

open Lean Meta
open SpytialLean

deriving instance ToExpr for Sum

/-!
These are integration checks over the actual Spytial relationalizer. They intentionally run in
`MetaM`: a thrown error fails elaboration and therefore fails the build, unlike printing an
`Except.error` from `#eval`.
-/

private inductive Tree where
  | leaf (value : Nat)
  | node (left right : Tree)
  deriving Repr, DecidableEq, ToExpr, SpytialIdentity, SpytialReify

private inductive OccurrenceTree where
  | leaf (value : Nat)
  | node (left right : OccurrenceTree)
  deriving Repr, DecidableEq, ToExpr, SpytialReify

private instance : SpytialIdentity OccurrenceTree := .asWritten

private structure Person where
  name : String
  age : Nat
  deriving Repr, DecidableEq, ToExpr, SpytialIdentity, SpytialReify

namespace ReifyObservation
private def age (person : Person) : Nat := person.age + 1
end ReifyObservation

private structure Mixed where
  number : Option Nat
  text : Option String
  pair : Nat × String
  deriving Repr, DecidableEq, ToExpr, SpytialIdentity, SpytialReify

private inductive TrafficLight where
  | red
  | amber
  | green
  deriving Repr, DecidableEq, ToExpr, SpytialIdentity, SpytialReify

private inductive BinTree (α : Type u) where
  | leaf (value : α)
  | branch (left right : BinTree α)
  deriving Repr, DecidableEq, ToExpr, SpytialIdentity, SpytialReify

private structure CoarseLeaf where
  value : Nat
  deriving Repr, DecidableEq, ToExpr, SpytialReify

private instance : SpytialIdentity CoarseLeaf where
  via := .identity fun _ => .ofNat 0

private structure CoarsePair where
  left : CoarseLeaf
  right : CoarseLeaf
  deriving Repr, DecidableEq, ToExpr, SpytialIdentity, SpytialReify

/- The deriving boundary is enforced, rather than silently emitting a decoder for data the
existing constructor walk cannot invert. -/
/--
error: cannot derive `SpytialReify` for `ReifyIndexedFixture`: indexed inductive families require dependent reconstruction
-/
#guard_msgs in
inductive ReifyIndexedFixture : Nat → Type where
  | zero : ReifyIndexedFixture 0
  deriving SpytialReify

/--
error: cannot derive `SpytialReify` for `ReifyNestedFixture`: nested recursion is not yet supported
-/
#guard_msgs in
inductive ReifyNestedFixture where
  | node : List ReifyNestedFixture → ReifyNestedFixture
  deriving SpytialReify

/--
error: cannot derive `SpytialReify` for `ReifyFunctionFixture`: function fields are not supported
-/
#guard_msgs in
structure ReifyFunctionFixture where
  run : Nat → Nat
  deriving SpytialReify

/--
error: cannot derive `SpytialReify` for `ReifyDuplicateFieldFixture`: constructor `mk` maps more than one field to relation `value`
-/
#guard_msgs in
inductive ReifyDuplicateFieldFixture where
  | mk (value : Nat) (value : Nat)
  deriving SpytialReify

/--
error: cannot derive `SpytialReify` for `ReifyFallbackCollisionFixture`: constructor `mk` maps more than one field to relation `mk_1`
-/
#guard_msgs in
inductive ReifyFallbackCollisionFixture where
  | mk (mk_1 : Nat) (_ : Nat)
  deriving SpytialReify

/-- error: `relationalize%` requires a closed, fully instantiated value without `sorry` -/
#guard_msgs in
example (value : Nat) : RootedJsonDataInstance := relationalize% value

/- These declarations are the kernel-checked part of the test. `relationalize%` runs the existing
relationalizer once, during elaboration, and embeds its root ID and `JsonDataInstance`. The
representation certificate is computed independently of `reify`; the universal theorem then gives
structural equality with the original closed value. -/

private def closedString : String := "a\"b\nλ"
private def closedStringData : RootedJsonDataInstance := relationalize% closedString

private theorem closedStringRepresents : StructurallyRepresents closedStringData closedString := by
  decide_cbv

private theorem closedStringRoundTrip :
    reify closedStringData = Except.ok closedString :=
  reify_of_structurallyRepresents closedStringRepresents

private def closedOption : Option Nat := some 1000
private def closedOptionData : RootedJsonDataInstance := relationalize% closedOption

private theorem closedOptionRepresents : StructurallyRepresents closedOptionData closedOption := by
  decide_cbv

private theorem closedOptionRoundTrip :
    reify closedOptionData = Except.ok closedOption :=
  reify_of_structurallyRepresents closedOptionRepresents

private def closedTree : Tree := .node (.leaf 1) (.node (.leaf 1) (.leaf 2))
private def closedTreeData : RootedJsonDataInstance := relationalize% closedTree

private theorem closedTreeRepresents : StructurallyRepresents closedTreeData closedTree := by
  decide_cbv

private theorem closedTreeRoundTrip : reify closedTreeData = Except.ok closedTree :=
  reify_of_structurallyRepresents closedTreeRepresents

private def closedOccurrenceTree : OccurrenceTree := .node (.leaf 1) (.leaf 1)
private def closedOccurrenceTreeData : RootedJsonDataInstance :=
  relationalize% closedOccurrenceTree

private theorem closedOccurrenceTreeRepresents :
    StructurallyRepresents closedOccurrenceTreeData closedOccurrenceTree := by
  decide_cbv

private theorem closedOccurrenceTreeRoundTrip :
    reify closedOccurrenceTreeData = Except.ok closedOccurrenceTree :=
  reify_of_structurallyRepresents closedOccurrenceTreeRepresents

private def closedPerson : Person := ⟨"Ada", 37⟩
private def closedPersonData : RootedJsonDataInstance := relationalize% closedPerson

private theorem closedPersonRepresents : StructurallyRepresents closedPersonData closedPerson := by
  decide_cbv

private theorem closedPersonRoundTrip : reify closedPersonData = Except.ok closedPerson :=
  reify_of_structurallyRepresents closedPersonRepresents

private theorem closedPersonRepr :
    reifyRepr (α := Person) closedPersonData = Except.ok (reprStr closedPerson) :=
  reifyRepr_of_structurallyRepresents closedPersonRepresents

private def closedBinTree : BinTree String := .branch (.leaf "left") (.leaf "right")
private def closedBinTreeData : RootedJsonDataInstance := relationalize% closedBinTree

private theorem closedBinTreeRepresents : StructurallyRepresents closedBinTreeData closedBinTree := by
  decide_cbv

private theorem closedBinTreeRoundTrip : reify closedBinTreeData = Except.ok closedBinTree :=
  reify_of_structurallyRepresents closedBinTreeRepresents

private def closedMixed : Mixed := ⟨some 42, none, (7, "seven")⟩
private def closedMixedData : RootedJsonDataInstance := relationalize% closedMixed

private theorem closedMixedRepresents : StructurallyRepresents closedMixedData closedMixed := by
  decide_cbv

private theorem closedMixedRoundTrip : reify closedMixedData = Except.ok closedMixed :=
  reify_of_structurallyRepresents closedMixedRepresents

private def closedTrafficLight : TrafficLight := .amber
private def closedTrafficLightData : RootedJsonDataInstance := relationalize% closedTrafficLight

private theorem closedTrafficLightRepresents :
    StructurallyRepresents closedTrafficLightData closedTrafficLight := by
  decide_cbv

private theorem closedTrafficLightRoundTrip :
    reify closedTrafficLightData = Except.ok closedTrafficLight :=
  reify_of_structurallyRepresents closedTrafficLightRepresents

private def closedCoarsePair : CoarsePair := ⟨⟨1⟩, ⟨2⟩⟩
private def closedCoarsePairData : RootedJsonDataInstance := relationalize% closedCoarsePair

private theorem closedCoarsePairIsLossy :
    ¬ StructurallyRepresents closedCoarsePairData closedCoarsePair := by
  decide_cbv

private meta def throughJson (datum : RootedJsonDataInstance) :
    MetaM RootedJsonDataInstance := do
  let json ← match Json.parse (toJson datum).compress with
    | .ok json => pure json
    | .error error => throwError "reify test: JSON parse failed: {error}"
  match fromJson? json with
  | .ok decoded => pure decoded
  | .error error => throwError "reify test: JSON decode failed: {error}"

private meta def child (data : JsonDataInstance) (owner field : String) : MetaM String :=
  match data.child owner field with
  | .ok child => pure child
  | .error error => throwError "{error}"

private meta def assertRoundTrip {α : Type}
    [ToExpr α] [Repr α] [DecidableEq α] [SpytialReify α] [StructuralReification α]
    (label : String) (original : α)
    (config : WalkConfig := {}) : MetaM RootedJsonDataInstance := do
  let data ← throughJson (← SpytialLean.Reify.relationalizeValue original config)
  unless structurallyRepresents data original do
    throwError "{label}: the relational datum does not structurally represent the original"
  let reconstructed ← match reify data with
    | .ok value => pure value
    | .error error => throwError "{label}: decoder rejected the datum: {error}"
  unless reconstructed = original do
    throwError "{label}: reconstructed value is not structurally equal to the original"
  let originalRepr := reprStr original
  let reconstructedRepr := reprStr reconstructed
  unless originalRepr == reconstructedRepr do
    throwError "{label}: repr changed from {originalRepr} to {reconstructedRepr}"
  return data

private def treesUpTo : Nat → Array Tree
  | 0 => #[.leaf 0, .leaf 1]
  | depth + 1 => Id.run do
    let previous := treesUpTo depth
    let mut trees := previous
    for left in previous do
      for right in previous do
        trees := trees.push (.node left right)
    return trees

private def boolListsUpTo : Nat → Array (List Bool)
  | 0 => #[[]]
  | length + 1 => Id.run do
    let previous := boolListsUpTo length
    return previous ++ previous.map (false :: ·) ++ previous.map (true :: ·)

#eval show MetaM Unit from do
  for value in (Array.range 33).push 1000 do
    discard <| assertRoundTrip "Nat" value
  for value in #[("" : String), "plain", "a\"b", "line\nbreak", "λ"] do
    discard <| assertRoundTrip "String" value
  for value in #[false, true] do
    discard <| assertRoundTrip "Bool" value
  discard <| assertRoundTrip "PUnit" PUnit.unit
  for value in #[-8, -1, 0, 1, 8] do
    discard <| assertRoundTrip "Int" (value : Int)
  for value in #[none, some 0, some 1000] do
    discard <| assertRoundTrip "Option Nat" (value : Option Nat)
  for value in #[Sum.inl 0, Sum.inr "right"] do
    discard <| assertRoundTrip "Sum Nat String" (value : Sum Nat String)
  for value in #[(0, ""), (37, "Ada")] do
    discard <| assertRoundTrip "Nat × String" (value : Nat × String)
  for value in boolListsUpTo 4 do
    discard <| assertRoundTrip "List Bool" value
  for value in treesUpTo 2 do
    discard <| assertRoundTrip "Tree" value
  for value in (#[(.leaf "root"), (.branch (.leaf "left") (.leaf "right"))] :
      Array (BinTree String)) do
    discard <| assertRoundTrip "BinTree String" value
  for value in (#[(⟨"Ada", 37⟩), (⟨"Grace", 85⟩)] : Array Person) do
    discard <| assertRoundTrip "Person" value
  for value in (#[(⟨none, some "text", (0, "")⟩),
      (⟨some 42, none, (7, "seven")⟩)] : Array Mixed) do
    discard <| assertRoundTrip "mixed polymorphic fields" value
  for value in #[TrafficLight.red, .amber, .green] do
    discard <| assertRoundTrip "nullary constructors" value

/- Structural identity merges equal subvalues. The decoder follows both field relations to the
same atom and reconstructs both constructor fields. -/
#eval show MetaM Unit from do
  let value := Tree.node (.leaf 1) (.leaf 1)
  let datum ← assertRoundTrip "merged identity" value
  let left ← child datum.data datum.root "left"
  let right ← child datum.data datum.root "right"
  unless left == right do
    throwError "merged identity: the existing relationalizer did not share equal leaves"

/- `SpytialIdentity.asWritten` keeps the two leaf occurrences distinct. The same decoder handles
this graph without a second encoding format. -/
#eval show MetaM Unit from do
  let value := OccurrenceTree.node (.leaf 1) (.leaf 1)
  let datum ← assertRoundTrip "as written identity" value
  let left ← child datum.data datum.root "left"
  let right ← child datum.data datum.root "right"
  unless left != right do
    throwError "as written identity: equal leaf occurrences unexpectedly merged"

/- The explicit root survives JSON transport and makes every atom-array permutation equivalent. -/
#eval show MetaM Unit from do
  let value := Tree.node (.leaf 1) (.leaf 2)
  let datum ← throughJson (← SpytialLean.Reify.relationalizeValue value)
  let reordered := { datum with data := { datum.data with atoms := datum.data.atoms.reverse } }
  let reconstructed ← match reify reordered with
    | .ok value => pure value
    | .error error => throwError "relation traversal: decoder rejected reordered datum: {error}"
  unless reconstructed = value do
    throwError "relation traversal: reordering atoms changed the reconstructed value"
  let missingRoot := { reordered with root := "not-an-atom" }
  if (reify missingRoot : Except ReifyError Tree).isOk then
    throwError "relation traversal: decoder ignored an unknown explicit root"

/- Repeated records of one structural ID are extensional, including after JSON transport. -/
#eval show MetaM Unit from do
  let value := Tree.node (.leaf 1) (.leaf 2)
  let datum ← throughJson (← SpytialLean.Reify.relationalizeValue value)
  let split := { datum with data := { datum.data with
    relations := datum.data.relations.flatMap fun relation =>
      relation.tuples.map fun tuple =>
        { relation with tuples := #[tuple] } } }
  let received ← throughJson split
  let reconstructed ← match (reify received : Except ReifyError Tree) with
    | .ok value => pure value
    | .error error => throwError "relation identity: decoder rejected split records: {error}"
  unless reconstructed = value do
    throwError "relation identity: splitting same-named records changed reification"

/- The production expression walker retains a field and an observed function with the same name;
the independent kernel-checked representation certificate still implies exact reconstruction. -/
#eval show MetaM Unit from do
  let value := (⟨"Ada", 37⟩ : Person)
  let expression := toExpr value
  let datum ← relationalizeRooted expression {} #[mkApp (mkConst ``ReifyObservation.age) expression]
  let relations := datum.data.relations.filter (·.name == "age")
  unless relations.size == 2 && relations[0]!.id != relations[1]!.id do
    throwError "relation identity: field and observation were merged"
  let received ← throughJson datum
  discard <| Reify.certifyReification expression received
  let reconstructed ← match (reify received : Except ReifyError Person) with
    | .ok value => pure value
    | .error error => throwError "relation identity: observed datum did not reify: {error}"
  unless reconstructed = value do throwError "relation identity: round trip changed Person"

/- A same-named observation about the same owner must not replace or corrupt its field. -/
#eval show MetaM Unit from do
  let value := (⟨"Ada", 37⟩ : Person)
  let datum ← SpytialLean.Reify.relationalizeValue value
  let observation : JsonRelation := {
    id := "lean:head:unrelated-age", name := "age", types := #["Person", "Person"]
    tuples := #[{ atoms := #[datum.root, datum.root], types := #["Person", "Person"] }] }
  let enriched := { datum with data := { datum.data with
    relations := #[observation] ++ datum.data.relations } }
  let received ← throughJson enriched
  discard <| Reify.certifyReification (toExpr value) received
  let reconstructed ← match (reify received : Except ReifyError Person) with
    | .ok value => pure value
    | .error error => throwError "relation identity: observation corrupted field decoding: {error}"
  unless reconstructed = value do
    throwError "relation identity: observation changed the reconstructed value"
  let missingField := { enriched with data := { enriched.data with
    relations := enriched.data.relations.filter
      (fun relation => relation.id != fieldRelationId "Person" "age") } }
  if (reify missingField : Except ReifyError Person).isOk then
    throwError "relation identity: an observation supplied a missing structural field"
  -- Display names are for selectors, so changing one does not change reconstruction.
  let renamed := { datum with data := { datum.data with
    relations := datum.data.relations.map fun relation => { relation with name := "display" } } }
  let renamedValue ← match (reify renamed : Except ReifyError Person) with
    | .ok value => pure value
    | .error error => throwError "relation identity: decoder depended on display names: {error}"
  unless renamedValue = value do throwError "relation identity: display names changed the value"

/- Relations carry the data fields: deleting one makes decoding fail. -/
#eval show MetaM Unit from do
  let value := (⟨"Ada", 37⟩ : Person)
  let datum ← SpytialLean.Reify.relationalizeValue value
  let broken := { datum with data := { datum.data with
    relations := datum.data.relations.filter (fun relation => relation.name != "age") } }
  if (reify broken : Except ReifyError Person).isOk then
    throwError "relation traversal: decoder accepted a structure with a missing age field"

/- The expected Lean type participates in decoding, and malformed graph claims are rejected. -/
#eval show MetaM Unit from do
  let datum ← SpytialLean.Reify.relationalizeValue (some 7 : Option Nat)
  if (reify datum : Except ReifyError (Option String)).isOk then
    throwError "typed decoding: Option Nat data was accepted as Option String"
  let some root := datum.data.atoms.find? (·.id == datum.root)
    | throwError "typed decoding: the explicit root atom is missing"
  let duplicateRoot := { datum with data := { datum.data with
    atoms := datum.data.atoms.push root } }
  if (reify duplicateRoot : Except ReifyError (Option Nat)).isOk then
    throwError "typed decoding: a duplicate atom id was accepted"

#eval show MetaM Unit from do
  let datum ← SpytialLean.Reify.relationalizeValue (⟨"Ada", 37⟩ : Person)
  let wrongTupleTypes := { datum with data := { datum.data with
    relations := datum.data.relations.map fun relation =>
      if relation.name == "age" then
        { relation with tuples := relation.tuples.map fun tuple =>
          { tuple with types := #["Person", "String"] } }
      else relation } }
  if (reify wrongTupleTypes : Except ReifyError Person).isOk then
    throwError "typed decoding: tuple types that disagree with their atoms were accepted"

/- A deliberately coarse identity merges unequal leaves and therefore really loses information.
This boundary case also proves that reification reads the graph instead of consulting hidden
evidence containing the original value. -/
#eval show MetaM Unit from do
  let original : CoarsePair := ⟨⟨1⟩, ⟨2⟩⟩
  let data ← SpytialLean.Reify.relationalizeValue original
  unless structurallyRepresents data original == false do
    throwError "coarse identity: the structural reconstruction predicate accepted a lossy datum"
  let reconstructed ← match reify data with
    | .ok value => pure value
    | .error error => throwError "coarse identity: decoder rejected the datum: {error}"
  if reconstructed = original then
    throwError "coarse identity: unequal merged leaves unexpectedly round-tripped"
  unless reconstructed = (⟨⟨1⟩, ⟨1⟩⟩ : CoarsePair) do
    throwError "coarse identity: decoder did not reconstruct the graph's shared representative"
