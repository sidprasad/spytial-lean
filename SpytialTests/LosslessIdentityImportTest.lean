module

public import SpytialTests.LosslessIdentityTest
public meta import SpytialLean.LosslessIdentityDeriving
public meta import Lean.Util.CollectAxioms

open SpytialLean LosslessIdentityTest

-- A downstream module uses the generated certificate without importing private definitions.
example (value : Tree) : reify (Structural.relationalizeCandidate value) = Except.ok value :=
  Structural.reify_relationalize_of_lossless value

-- Derivation also composes with an imported recursive field type.
public structure Imported where
  tree : Tree
  values : List Tree
  deriving SpytialReify, LosslessIdentity

public theorem imported_roundTrip (value : Imported) :
    reify (Structural.relationalizeCandidate value) = Except.ok value :=
  Structural.reify_relationalize_of_lossless value

#eval show Lean.MetaM Unit from do
  let axioms ← Lean.collectAxioms ``imported_roundTrip
  unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains ·) do
    throwError "unexpected axiom in imported round trip: {axioms}"
