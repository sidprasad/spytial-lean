module

public import SpytialTests.ClosedValueTest
public meta import SpytialTests.ClosedValueTest

open Lean Meta Elab Term SpytialLean ClosedValueTest

namespace ClosedValueCapabilityTest

/-!
The scoped capability is evaluated at the actual `#spytial` payload boundary:

  closed value → payload JSON → parsed datum + explicit root → reify → reprStr

The comparison path is `closed value → reprStr`. The decoder receives only the parsed relational
data, its root ID, and the expected type's instance: no source expression, provenance, or saved
printout. Every fixture must select the typed route, and the exact parsed output also receives a
kernel-checked reconstruction certificate. These examples exercise the integration; the universal
theorems below and in `LosslessIdentity` establish the value-level result for all values of a type.
-/

-- PUnit has a supplied decoder/exposure, but no primitive identity classifier.
deriving instance SpytialIdentity for PUnit
-- Sum likewise needs an explicit policy; occurrence preservation is lossless.
public instance : SpytialIdentity (Sum Nat String) := .asWritten

public instance : LosslessIdentity Nat := by spytial_lossless
public instance : LosslessIdentity String := by spytial_lossless
public instance : LosslessIdentity Bool := by spytial_lossless
public instance : LosslessIdentity Int := by spytial_lossless
public instance : LosslessIdentity PUnit := by spytial_lossless
public instance : LosslessIdentity (Option String) := by spytial_lossless
public instance : LosslessIdentity (Sum Nat String) := by spytial_lossless
public instance : LosslessIdentity (Nat × String) := by spytial_lossless
public instance : LosslessIdentity (List (List Nat)) := by spytial_lossless

deriving instance Repr for Tree, Written

public inductive Color where
  | red | green | blue
  deriving Repr, SpytialIdentity, SpytialReify, LosslessIdentity

public structure Entry where
  name : String
  count : Nat
  deriving Repr, SpytialIdentity, SpytialReify, LosslessIdentity

-- A quantified theorem, not a finite collection of successful examples.
public theorem list_inspection (inspect : List Nat → String) (xs : List Nat) :
    (reify (Structural.relationalizeCandidate xs)).map inspect = Except.ok (inspect xs) :=
  Structural.inspect_reify_relationalize_of_lossless inspect xs

public theorem list_repr (xs : List Nat) :
    reifyRepr (α := List Nat) (Structural.relationalizeCandidate xs) = Except.ok (reprStr xs) :=
  Structural.reifyRepr_relationalize_of_lossless xs

-- The elaboration bridge exposes that same program, so no concrete decoder computation is needed.
example : reifyRepr (α := List Nat) (relationalize% ([1, 2, 1] : List Nat)) =
    Except.ok (reprStr ([1, 2, 1] : List Nat)) :=
  Structural.reifyRepr_relationalize_of_lossless _

private meta def checkPayload {α : Type} [SpytialReify α] [Repr α]
    (input : TSyntax `term) (expected : α) : TermElabM RootedJsonDataInstance := do
  let expression ← elabTerm input none
  synthesizeSyntheticMVarsNoPostponing
  let expression ← instantiateMVars expression
  let some typed ← ClosedValue.relationalize? expression
    | throwError "capability fixture did not select the proved route: {input}"
  -- Retain the explicit root from the production API; never infer it from atom-array order.
  let (rooted, _, _) ← Reify.relationalizeWithEvidence expression
  unless (toJson rooted).compress == (toJson typed.datum).compress do
    throwError "the command boundary did not retain the typed result"
  let props ← spytialPayloadProps input
  let .ok payload := Json.parse props.compress | throwError "payload JSON did not parse"
  let .ok data := fromJson? (α := JsonDataInstance) (payload.getObjValD "dataInstance")
    | throwError "payload did not contain a relational datum"
  unless (toJson data).compress == (toJson rooted.data).compress do
    throwError "the widget payload changed the production datum"
  let transported : RootedJsonDataInstance := ⟨rooted.root, data⟩
  let .ok reconstructed := reifyRepr (α := α) transported
    | throwError "could not reconstruct inspection output from the payload"
  unless reconstructed == reprStr expected do
    throwError "inspection differed: reconstructed {reconstructed}, expected {reprStr expected}"
  -- Stronger than string equality: check reconstruction of this exact JSON-derived value.
  discard <| Reify.certifyReification expression transported
  return transported

run_cmd Lean.Elab.Command.liftTermElabM do
  -- Literal foundations, including empty and escaped strings and an arbitrary-precision natural.
  discard <| checkPayload (← `((0 : Nat))) (0 : Nat)
  discard <| checkPayload (← `((100000000000000000000 : Nat))) (100000000000000000000 : Nat)
  discard <| checkPayload (← `(("" : String))) ""
  discard <| checkPayload (← `(("a\"b\nλ\\" : String))) "a\"b\nλ\\"
  -- Supplied inductive instances and both constructor alternatives where applicable.
  discard <| checkPayload (← `(false)) false
  discard <| checkPayload (← `(true)) true
  discard <| checkPayload (← `((0 : Int))) (0 : Int)
  discard <| checkPayload (← `((-7 : Int))) (-7 : Int)
  discard <| checkPayload (← `((PUnit.unit : PUnit.{1}))) PUnit.unit
  discard <| checkPayload (← `((none : Option String))) (none : Option String)
  discard <| checkPayload (← `((some "λ" : Option String))) (some "λ" : Option String)
  discard <| checkPayload (← `((Sum.inl 7 : Sum Nat String))) (Sum.inl 7 : Sum Nat String)
  discard <| checkPayload (← `((Sum.inr "x" : Sum Nat String))) (Sum.inr "x" : Sum Nat String)
  discard <| checkPayload (← `(((7, "x") : Nat × String))) ((7, "x") : Nat × String)
  discard <| checkPayload (← `(([] : List Nat))) ([] : List Nat)
  discard <| checkPayload (← `(([1, 2, 1] : List Nat))) ([1, 2, 1] : List Nat)
  discard <| checkPayload (← `(([[], [1, 2], [1, 2]] : List (List Nat))))
    ([[], [1, 2], [1, 2]] : List (List Nat))
  -- User-defined sums/products, direct recursion, structural sharing, and asWritten identity.
  discard <| checkPayload (← `(Color.red)) Color.red
  discard <| checkPayload (← `(Color.blue)) Color.blue
  discard <| checkPayload (← `(Entry.mk "Ada" 37)) (Entry.mk "Ada" 37)
  discard <| checkPayload (← `(sample)) sample
  discard <| checkPayload (← `(Written.branch (.leaf 7) (.leaf 7)))
    (Written.branch (.leaf 7) (.leaf 7))
  -- The decoder really depends on the transmitted data: changing its literal changes the output.
  let literal ← checkPayload (← `((7 : Nat))) (7 : Nat)
  let altered := { literal with data.atoms := literal.data.atoms.map fun atom =>
    if atom.id == literal.root then { atom with label := "8" } else atom }
  let .ok alteredInspection := reifyRepr (α := Nat) altered
    | throwError "altered literal did not reconstruct"
  unless alteredInspection == reprStr (8 : Nat) do
    throwError "inspection did not use the transmitted literal"

#eval show MetaM Unit from do
  for name in #[``list_inspection, ``list_repr,
      ``Structural.inspect_reify_relationalize_of_lossless,
      ``Structural.reifyRepr_relationalize_of_lossless] do
    let axioms ← collectAxioms name
    unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains ·) do
      throwError "unexpected axiom in the inspection-preservation theorem: {name}: {axioms}"

end ClosedValueCapabilityTest
