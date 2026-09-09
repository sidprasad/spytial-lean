module

public import SpytialLean.Tier1Relationalizer
meta import SpytialLean.Tier1Relationalizer
public import SpytialLean.ReifyInstances
public import Lean.ToExpr
meta import SpytialLean.Relationalizer

open SpytialLean
open SpytialLean.Tier1
open Lean

namespace Tier1RelationalizerTest

example (value : Nat) : reify (relationalize value) = Except.ok value := by
  exact reify_relationalize value

example (value : String) : reify (relationalize value) = Except.ok value := by
  exact reify_relationalize value

example (value : Nat) : Tier1Represents (relationalize value) value := by
  exact relationalize_represents value

private meta def assertMatchesMeta (expression : Lean.Expr)
    (typed : RootedJsonDataInstance) : Lean.MetaM Unit := do
  let elaborated ← SpytialLean.relationalizeRooted expression
  unless (toJson elaborated).compress == (toJson typed).compress do
    throwError "typed and expression frontends emitted different data"

#eval show Lean.MetaM Unit from do
  assertMatchesMeta (Lean.toExpr (42 : Nat)) (relationalize 42)
  assertMatchesMeta (Lean.toExpr "a\"b\nλ") (relationalize "a\"b\nλ")

private inductive TrafficLight where
  | red
  | amber
  | green
  deriving DecidableEq, SpytialReify

private instance trafficLightIdentity : Tier1Identity TrafficLight where
  key? _ := none

private def trafficLightTypeKey : IdentityKey :=
  IdentityKey.ofString "Tier1RelationalizerTest.TrafficLight"

private def describeTrafficLight : TrafficLight → Tier1Node
  | .red => { typeName := "TrafficLight", label := "red" }
  | .amber => { typeName := "TrafficLight", label := "amber" }
  | .green => { typeName := "TrafficLight", label := "green" }

private instance : Tier1Relationalizer TrafficLight where
  typeKey := trafficLightTypeKey
  describe := describeTrafficLight
  represents value := by
    cases identity : Tier1Identity.key? value
    all_goals
      cases value <;>
      unfold Tier1Represents tier1Represents <;>
      change instSpytialReifyTrafficLight_representsAt _ _ _ _ = true <;>
      simp [describeTrafficLight, Tier1Node.withIdentity, tier1Identity,
        identity, instSpytialReifyTrafficLight_representsAt,
        RelationalizerCore.relationalize, RelationalizerCore.Engine.addNode,
        RelationalizerCore.Engine.addFields, RelationalizerCore.Engine.intern,
        RelationalizerCore.Engine.find?, RelationalizerCore.Engine.empty,
        RelationalizerCore.Graph.freshId, RelationalizerCore.Graph.addAtom,
        RelationalizerCore.Graph.toDataInstance, JsonDataInstance.constructorRepresents,
        JsonDataInstance.expectAtom, JsonDataInstance.atom, Bind.bind, Pure.pure,
        Except.bind, Except.pure]

example (value : TrafficLight) : reify (relationalize value) = Except.ok value := by
  exact reify_relationalize value

private structure WrittenNat where
  value : Nat

private instance writtenNatIdentity : SpytialIdentity WrittenNat := .asWritten

private def isAsWritten : RelationalizerCore.Identity IdentityKey IdentityKey → Bool
  | .asWritten => true
  | .keyed _ _ => false

/-- The typed frontend observes an explicit `SpytialIdentity.asWritten` policy. -/
example :
    isAsWritten (tier1Identity (IdentityKey.ofString "WrittenNat") (⟨1⟩ : WrittenNat)) =
      true := by
  simp [isAsWritten, tier1Identity, Tier1Identity.key?]

end Tier1RelationalizerTest
