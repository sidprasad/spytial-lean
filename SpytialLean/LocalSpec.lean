module

public meta import SpytialLean.LeanSelector
meta import Lean.Meta.Tactic.Assert

namespace SpytialLean

open Lean Meta

/-- A layout belongs to a particular proof branch. Its presence in a goal is recorded by a
    hidden local marker. The marker is independent of the layout's captures so it cannot block
    `clear` or introduce extra premises when the user reverts a variable. The elaborated terms
    live only in the elaborator's environment, keyed by the marker's free-variable identity. -/
private meta initialize proofLayouts : EnvExtension (Std.HashMap FVarId (Expr × SpytialSpec)) ←
  registerEnvExtension (pure {}) (asyncMode := .local)

public meta def attachProofLayout (goal : MVarId) (type : Expr) (spec : SpytialSpec) : MetaM MVarId := do
  let (markers, next) ← goal.assertHypotheses #[{
    userName := ← mkFreshUserName `spytial_spec, type := mkConst ``Unit,
    value := mkConst ``Unit.unit, kind := .implDetail }]
  modifyEnv fun env => proofLayouts.modifyState env (·.insert markers[0]! (type, spec))
  return next

public meta def getProofLayout? (type : Expr) : MetaM (Option SpytialSpec) := do
  let layouts := proofLayouts.getState (← getEnv)
  if layouts.isEmpty then return none
  let type ← instantiateMVars type
  if type.hasMVar then return none
  let lctx ← getLCtx
  lctx.findDeclRevM? fun decl => do
    let some (target, spec) := layouts[decl.fvarId]? | return none
    if target.hasFVar && (target.find? fun e => e.isFVar && !lctx.contains e.fvarId!).isSome then
      return none
    unless ← withoutModifyingState <| withNewMCtxDepth <| isDefEq target type do return none
    if spec.hasMissingLocals lctx then return none
    return some spec

end SpytialLean
