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
error: cannot derive `SpytialReify` for `ReifyIndexedFixture`: indexed inductive families are Tier 2
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
error: cannot derive `SpytialReify` for `ReifyFunctionFixture`: function fields are outside Tier 1
-/
#guard_msgs in
structure ReifyFunctionFixture where
  run : Nat → Nat
  deriving SpytialReify

/--
error: cannot derive `SpytialReify` for `ReifyImplicitFieldFixture`: constructor `mk` has a non-explicit data field; Tier 1 requires explicit constructor fields
-/
#guard_msgs in
inductive ReifyImplicitFieldFixture where
  | mk {hidden : Nat} (visible : String)
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
example (value : Nat) : JsonDataInstance := relationalize% value

/- These declarations are the kernel-checked part of the test. `relationalize%` runs the existing
relationalizer once, during elaboration, and embeds only its `JsonDataInstance`. The representation
certificate is computed independently of `reify`; the universal theorem then gives structural
equality with the original closed value. -/

private def closedString : String := "a\"b\nλ"
private def closedStringData : JsonDataInstance := relationalize% closedString

private theorem closedStringRepresents : Tier1Represents closedStringData closedString := by
  decide_cbv

private theorem closedStringRoundTrip :
    reify closedStringData = Except.ok closedString :=
  reify_of_tier1Represents closedStringRepresents

private def closedOption : Option Nat := some 1000
private def closedOptionData : JsonDataInstance := relationalize% closedOption

private theorem closedOptionRepresents : Tier1Represents closedOptionData closedOption := by
  decide_cbv

private theorem closedOptionRoundTrip :
    reify closedOptionData = Except.ok closedOption :=
  reify_of_tier1Represents closedOptionRepresents

private def closedTree : Tree := .node (.leaf 1) (.node (.leaf 1) (.leaf 2))
private def closedTreeData : JsonDataInstance := relationalize% closedTree

private theorem closedTreeRepresents : Tier1Represents closedTreeData closedTree := by
  decide_cbv

private theorem closedTreeRoundTrip : reify closedTreeData = Except.ok closedTree :=
  reify_of_tier1Represents closedTreeRepresents

private def closedOccurrenceTree : OccurrenceTree := .node (.leaf 1) (.leaf 1)
private def closedOccurrenceTreeData : JsonDataInstance := relationalize% closedOccurrenceTree

private theorem closedOccurrenceTreeRepresents :
    Tier1Represents closedOccurrenceTreeData closedOccurrenceTree := by
  decide_cbv

private theorem closedOccurrenceTreeRoundTrip :
    reify closedOccurrenceTreeData = Except.ok closedOccurrenceTree :=
  reify_of_tier1Represents closedOccurrenceTreeRepresents

private def closedPerson : Person := ⟨"Ada", 37⟩
private def closedPersonData : JsonDataInstance := relationalize% closedPerson

private theorem closedPersonRepresents : Tier1Represents closedPersonData closedPerson := by
  decide_cbv

private theorem closedPersonRoundTrip : reify closedPersonData = Except.ok closedPerson :=
  reify_of_tier1Represents closedPersonRepresents

private theorem closedPersonRepr :
    reifyRepr (α := Person) closedPersonData = Except.ok (reprStr closedPerson) :=
  reifyRepr_of_tier1Represents closedPersonRepresents

private def closedBinTree : BinTree String := .branch (.leaf "left") (.leaf "right")
private def closedBinTreeData : JsonDataInstance := relationalize% closedBinTree

private theorem closedBinTreeRepresents : Tier1Represents closedBinTreeData closedBinTree := by
  decide_cbv

private theorem closedBinTreeRoundTrip : reify closedBinTreeData = Except.ok closedBinTree :=
  reify_of_tier1Represents closedBinTreeRepresents

private def closedMixed : Mixed := ⟨some 42, none, (7, "seven")⟩
private def closedMixedData : JsonDataInstance := relationalize% closedMixed

private theorem closedMixedRepresents : Tier1Represents closedMixedData closedMixed := by
  decide_cbv

private theorem closedMixedRoundTrip : reify closedMixedData = Except.ok closedMixed :=
  reify_of_tier1Represents closedMixedRepresents

private def closedTrafficLight : TrafficLight := .amber
private def closedTrafficLightData : JsonDataInstance := relationalize% closedTrafficLight

private theorem closedTrafficLightRepresents :
    Tier1Represents closedTrafficLightData closedTrafficLight := by
  decide_cbv

private theorem closedTrafficLightRoundTrip :
    reify closedTrafficLightData = Except.ok closedTrafficLight :=
  reify_of_tier1Represents closedTrafficLightRepresents

private def closedCoarsePair : CoarsePair := ⟨⟨1⟩, ⟨2⟩⟩
private def closedCoarsePairData : JsonDataInstance := relationalize% closedCoarsePair

private theorem closedCoarsePairIsLossy :
    ¬ Tier1Represents closedCoarsePairData closedCoarsePair := by
  decide_cbv

private meta def throughJson (data : JsonDataInstance) : MetaM JsonDataInstance := do
  let json ← match Json.parse (toJson data).compress with
    | .ok json => pure json
    | .error error => throwError "reify test: JSON parse failed: {error}"
  match fromJson? json with
  | .ok decoded => pure decoded
  | .error error => throwError "reify test: JSON decode failed: {error}"

private meta def child (datum : ReifyDatum) (owner field : String) : MetaM String :=
  match datum.child owner field with
  | .ok child => pure child
  | .error error => throwError "{error}"

private meta def assertRoundTrip {α : Type}
    [ToExpr α] [Repr α] [DecidableEq α] [SpytialReify α] [Tier1Reification α]
    (label : String) (original : α)
    (config : WalkConfig := {}) : MetaM JsonDataInstance := do
  let data ← throughJson (← SpytialLean.Reify.relationalizeValue original config)
  unless tier1Represents data original do
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
  let data ← assertRoundTrip "merged identity" value
  let datum ← match ReifyDatum.ofData data with
    | .ok datum => pure datum
    | .error error => throwError "merged identity: {error}"
  let left ← child datum datum.root "left"
  let right ← child datum datum.root "right"
  unless left == right do
    throwError "merged identity: the existing relationalizer did not share equal leaves"

/- `SpytialIdentity.asWritten` keeps the two leaf occurrences distinct. The same decoder handles
this graph without a second encoding format. -/
#eval show MetaM Unit from do
  let value := OccurrenceTree.node (.leaf 1) (.leaf 1)
  let data ← assertRoundTrip "as written identity" value
  let datum ← match ReifyDatum.ofData data with
    | .ok datum => pure datum
    | .error error => throwError "as written identity: {error}"
  let left ← child datum datum.root "left"
  let right ← child datum datum.root "right"
  unless left != right do
    throwError "as written identity: equal leaf occurrences unexpectedly merged"

/- Atom-array order is not used for reconstruction when the root is explicit. -/
#eval show MetaM Unit from do
  let value := Tree.node (.leaf 1) (.leaf 2)
  let data ← SpytialLean.Reify.relationalizeValue value
  let datum ← match ReifyDatum.ofData data with
    | .ok datum => pure datum
    | .error error => throwError "relation traversal: {error}"
  let reordered := { datum with data.atoms := datum.data.atoms.reverse }
  let reconstructed ← match reifyRooted reordered with
    | .ok value => pure value
    | .error error => throwError "relation traversal: decoder rejected reordered datum: {error}"
  unless reconstructed = value do
    throwError "relation traversal: reordering atoms changed the reconstructed value"

/- Relations carry the data fields: deleting one makes decoding fail. -/
#eval show MetaM Unit from do
  let value := (⟨"Ada", 37⟩ : Person)
  let data ← SpytialLean.Reify.relationalizeValue value
  let broken := { data with
    relations := data.relations.filter (fun relation => relation.name != "age") }
  if (reify broken : Except ReifyError Person).isOk then
    throwError "relation traversal: decoder accepted a structure with a missing age field"

/- The expected Lean type participates in decoding, and malformed graph claims are rejected. -/
#eval show MetaM Unit from do
  let data ← SpytialLean.Reify.relationalizeValue (some 7 : Option Nat)
  if (reify data : Except ReifyError (Option String)).isOk then
    throwError "typed decoding: Option Nat data was accepted as Option String"
  let root := data.atoms[0]!
  let duplicateRoot := { data with atoms := data.atoms.push root }
  if (reify duplicateRoot : Except ReifyError (Option Nat)).isOk then
    throwError "typed decoding: a duplicate atom id was accepted"

#eval show MetaM Unit from do
  let data ← SpytialLean.Reify.relationalizeValue (⟨"Ada", 37⟩ : Person)
  let wrongTupleTypes := { data with relations := data.relations.map fun relation =>
    if relation.name == "age" then
      { relation with tuples := relation.tuples.map fun tuple =>
        { tuple with types := #["Person", "String"] } }
    else relation }
  if (reify wrongTupleTypes : Except ReifyError Person).isOk then
    throwError "typed decoding: tuple types that disagree with their atoms were accepted"

/- A deliberately coarse identity merges unequal leaves and therefore really loses information.
This boundary case also proves that reification reads the graph instead of consulting hidden
evidence containing the original value. -/
#eval show MetaM Unit from do
  let original : CoarsePair := ⟨⟨1⟩, ⟨2⟩⟩
  let data ← SpytialLean.Reify.relationalizeValue original
  unless tier1Represents data original == false do
    throwError "coarse identity: the Tier 1 predicate accepted a lossy datum"
  let reconstructed ← match reify data with
    | .ok value => pure value
    | .error error => throwError "coarse identity: decoder rejected the datum: {error}"
  if reconstructed = original then
    throwError "coarse identity: unequal merged leaves unexpectedly round-tripped"
  unless reconstructed = (⟨⟨1⟩, ⟨1⟩⟩ : CoarsePair) do
    throwError "coarse identity: decoder did not reconstruct the graph's shared representative"
