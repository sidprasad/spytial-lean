module

public import SpytialLean.ReifyCore
public import SpytialLean.ReifyInstances
public meta import SpytialLean.Relationalizer
public meta import Lean.ToExpr

namespace SpytialLean.Reify

open Lean Meta

/-!
# Adapter for the existing relationalizer

The pure `SpytialReify` class is a decoder only. This module connects it to the actual
expression-level relationalizer used by `#spytial` and the `spytial` tactic. It returns the same
ordinary `JsonDataInstance` already consumed by Spytial; no parallel encoder or evidence registry
is involved.

`MetaM` belongs only at this adapter boundary: quoting a host value, reducing an elaborated
expression, and discovering its instances require Lean's environment. The result is the ordinary
`JsonDataInstance` consumed by Spytial; decoding it with `reify` is pure and typed.
-/

/-- Relationalize a closed expression with Spytial's existing walker.

The walker emits the root atom first, which is the convention used by `SpytialLean.reify`. -/
public meta def relationalize (value : Expr) (config : WalkConfig := {}) :
    MetaM JsonDataInstance := do
  unless isClosedValue value do
    throwError "spytial reify: expected a closed value"
  withoutModifyingEnv do
    let (_, state) ← (walkExpr config value).run {}
    return state.toDataInstance

/-- Quote a fully instantiated host value and pass it to Spytial's existing relationalizer.

The `ToExpr` instance performs only the host-to-expression boundary. In particular, the returned
datum contains no copy of `value` for the decoder to retrieve. -/
public meta def relationalizeValue {α : Type u} [ToExpr α]
    (value : α) (config : WalkConfig := {}) : MetaM JsonDataInstance :=
  relationalize (toExpr value) config

end SpytialLean.Reify
