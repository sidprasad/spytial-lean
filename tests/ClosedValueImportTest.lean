module

public import ClosedValueTest

open Lean Meta SpytialLean ClosedValueTest

-- An ordinary import need not provide executable host code to the metaprogram. Inspection still
-- works through the old expression adapter; it must not turn this into an error or change data.
#eval show MetaM Unit from do
  let value := mkConst ``sample
  unless (← ClosedValue.relationalize? value).isNone do
    throwError "ordinary import unexpectedly provided meta code"
  let (expected, _, _) ← relationalizeRootedWithEvidence value
  let (actual, _, _) ← Reify.relationalizeWithEvidence value
  unless (toJson actual).compress == (toJson expected).compress do
    throwError "ordinary-import fallback changed inspection"
