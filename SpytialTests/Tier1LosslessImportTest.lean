module

public import SpytialTests.Tier1LosslessTest
public meta import SpytialLean.Tier1LosslessDeriving
public meta import Lean.Util.CollectAxioms

open SpytialLean Tier1LosslessTest

-- A downstream module uses the generated certificate without importing private definitions.
example (value : Tree) : reify (Tier1.relationalizeCandidate value) = Except.ok value :=
  Tier1.reify_relationalize_of_lossless value

-- Derivation also composes with an imported recursive field type.
public structure Imported where
  tree : Tree
  values : List Tree
  deriving SpytialReify, Tier1Lossless

public theorem imported_roundTrip (value : Imported) :
    reify (Tier1.relationalizeCandidate value) = Except.ok value :=
  Tier1.reify_relationalize_of_lossless value

#eval show Lean.MetaM Unit from do
  let axioms ← Lean.collectAxioms ``imported_roundTrip
  unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains ·) do
    throwError "unexpected axiom in imported round trip: {axioms}"
