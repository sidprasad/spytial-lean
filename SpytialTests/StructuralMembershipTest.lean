module

public import SpytialLean.ReifyInstances
public import SpytialLean.LosslessIdentity
public meta import SpytialLean.LosslessIdentityDeriving
public meta import SpytialLean.Reify
public meta import Lean.Util.CollectAxioms

open Lean Meta SpytialLean

namespace StructuralMembershipTest

public class Tag where
  code : Nat
  deriving Repr, DecidableEq, ToExpr, SpytialIdentity, SpytialReify, LosslessIdentity

-- Reconstruction must retain the stored instance even in the presence of this default.
public instance : Tag := ⟨0⟩

public instance : SpytialIdentity String where
  via := .identity ToIdentityKey.toKey

public inductive Packet (alpha : Type) where
  | mk {hidden : Nat} ⦃strict : Nat⦄ [tag : Tag] (payload : alpha)
  deriving Repr, DecidableEq, ToExpr, SpytialIdentity, SpytialReify

public instance : LosslessIdentity (Packet String) := by spytial_lossless

public theorem packet_roundTrip (value : Packet String) :
    reify (Structural.relationalizeCandidate value) = Except.ok value :=
  Structural.reify_relationalize_of_lossless value

public inductive Chain where
  | last {value : Nat}
  | next ⦃child : Chain⦄ (annotation : String)
  deriving Repr, DecidableEq, ToExpr, SpytialIdentity, SpytialReify, LosslessIdentity

public theorem chain_roundTrip (value : Chain) :
    reify (Structural.relationalizeCandidate value) = Except.ok value :=
  Structural.reify_relationalize_of_lossless value

public structure Envelope where
  packet : Packet String
  chain : Chain
  deriving Repr, DecidableEq, ToExpr, SpytialIdentity, SpytialReify, LosslessIdentity

public theorem envelope_roundTrip (value : Envelope) :
    reify (Structural.relationalizeCandidate value) = Except.ok value :=
  Structural.reify_relationalize_of_lossless value

-- The expression adapter, JSON transport, and emitted-datum certificate must agree with the
-- universal typed theorem, including hidden recursive children and a nondefault stored instance.
#eval show MetaM Unit from do
  let value : Envelope := {
    packet := @Packet.mk String 7 8 ⟨9⟩ "payload"
    chain := .next (child := .next (child := .last (value := 11)) "inner") "outer" }
  let datum ← Reify.relationalizeValue value
  let received ← match (fromJson? (toJson datum) : Except String RootedJsonDataInstance) with
    | .ok received => pure received
    | .error error => throwError "hidden fields: JSON transport failed: {error}"
  discard <| Reify.certifyReification (toExpr value) received
  match (reify received : Except ReifyError Envelope) with
  | .error error => throwError "hidden fields: reconstruction failed: {error}"
  | .ok decoded =>
      unless decoded = value do
        throwError "hidden fields: reconstruction changed a stored constructor argument"
  let missing := { received with data.relations :=
    received.data.relations.filter (·.id != fieldRelationId "Packet" "hidden") }
  if (reify missing : Except ReifyError Envelope).isOk then
    throwError "hidden fields: decoder inferred an absent hidden argument"
  for name in #[``packet_roundTrip, ``chain_roundTrip, ``envelope_roundTrip] do
    let axioms ← Lean.collectAxioms name
    unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains ·) do
      throwError "unexpected axiom in expanded structural reconstruction: {name}: {axioms}"

end StructuralMembershipTest
