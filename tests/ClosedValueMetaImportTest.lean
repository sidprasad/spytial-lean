module

public import ClosedValueTest
public meta import ClosedValueTest

open Lean Meta SpytialLean ClosedValueTest

-- No private implementation imports or per-value structural-checker proof is needed. Meta import
-- supplies the executable definitions for the typed exposure and selected identity classifiers.
example : reify (relationalize% sample) = Except.ok sample :=
  Tier1.reify_relationalize_of_lossless sample

#eval show MetaM Unit from do
  let some result ← ClosedValue.relationalize? (mkConst ``sample)
    | throwError "imported certificate did not enable the proved production route"
  checkWithKernel result.roundTrip
  unless result.datum.data.atoms.size == 3 && result.provenance.size == 3 do
    throwError "imported production route lost sharing or provenance"
