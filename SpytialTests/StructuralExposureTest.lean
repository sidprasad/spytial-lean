module

public import SpytialLean.StructuralExposure
public meta import SpytialLean.ReifyDeriving
public import SpytialLean.ReifyInstances
public import Lean.ToExpr
meta import SpytialLean.Relationalizer

open SpytialLean
open SpytialLean.Structural
open Lean

namespace StructuralExposureTest

example (value : Nat) : reify (relationalize value) = Except.ok value := by
  exact reify_relationalize value

example (value : String) : reify (relationalize value) = Except.ok value := by
  exact reify_relationalize value

example (value : Nat) : StructurallyRepresents (relationalize value) value := by
  exact relationalize_represents value

example (value : Nat) : reify (relationalizeAsWritten value) = Except.ok value :=
  reify_relationalizeAsWritten value

example (value : Bool) : reify (relationalize value) = Except.ok value := by
  exact reify_relationalize value

example (value : Option Nat) : reify (relationalize value) = Except.ok value := by
  exact reify_relationalize value

private meta def assertMatchesMeta (expression : Lean.Expr)
    (typed : RootedJsonDataInstance) : Lean.MetaM Unit := do
  let elaborated ← SpytialLean.relationalizeRooted expression
  unless (toJson elaborated).compress == (toJson typed).compress do
    throwError "typed and expression frontends emitted different data"

#eval show Lean.MetaM Unit from do
  assertMatchesMeta (Lean.toExpr (42 : Nat)) (relationalize 42)
  assertMatchesMeta (Lean.toExpr "a\"b\nλ") (relationalize "a\"b\nλ")

public inductive TrafficLight where
  | red
  | amber
  | green
  deriving DecidableEq, SpytialIdentity, SpytialReify

example (value : TrafficLight) : reify (relationalize value) = Except.ok value := by
  exact reify_relationalize value

public structure Person where
  name : String
  age : Nat
  deriving DecidableEq, ToExpr, SpytialIdentity, SpytialReify

example (value : Person) : reify (relationalize value) = Except.ok value := by
  exact reify_relationalize value

#eval show Lean.MetaM Unit from do
  let value : Person := ⟨"Ada", 37⟩
  assertMatchesMeta (Lean.toExpr value) (relationalize value)

public structure NoDeclaredIdentity where
  value : Nat
  deriving DecidableEq, SpytialReify

example (value : NoDeclaredIdentity) : reify (relationalize value) = Except.ok value := by
  exact reify_relationalize value

public inductive Empty where
  deriving SpytialReify

public inductive Tree (alpha : Type u) where
  | leaf (value : alpha)
  | branch (left right : Tree alpha)
  deriving DecidableEq, SpytialIdentity, SpytialReify

example {alpha : Type u} [SpytialReify alpha] [StructuralReification alpha]
    [ValueIdentity alpha] [StructuralExposure alpha] (value : Tree alpha) :
    reify (relationalize value) = Except.ok value := by
  exact reify_relationalize value

example {alpha : Type u} [SpytialReify alpha] [StructuralReification alpha]
    [ValueIdentity alpha] [StructuralExposure alpha] (value : Tree alpha) :
    reify (relationalizeAsWritten value) = Except.ok value :=
  reify_relationalizeAsWritten value

public structure CoarseLeaf where
  value : Nat
  deriving DecidableEq, SpytialReify

public instance coarseLeafIdentity : SpytialIdentity CoarseLeaf where
  via := .identity fun _ => .ofNat 0

public structure CoarsePair where
  left : CoarseLeaf
  right : CoarseLeaf
  deriving DecidableEq, SpytialIdentity, SpytialReify

private def unequalCoarsePair : CoarsePair := ⟨⟨1⟩, ⟨2⟩⟩
private def equalCoarsePair : CoarsePair := ⟨⟨1⟩, ⟨1⟩⟩

/-- A lossy identity makes the normal candidate fail its independent structural check. -/
example : structurallyRepresents (relationalizeCandidate unequalCoarsePair) unequalCoarsePair = false := by
  native_decide

/-- The typed entry point detects that loss and reruns the same engine occurrence-by-occurrence. -/
example : (relationalize unequalCoarsePair).data.atoms.size = 5 := by
  native_decide

example : reify (relationalize unequalCoarsePair) = Except.ok unequalCoarsePair := by
  exact reify_relationalize unequalCoarsePair

/-- A safe merge is retained: equal children share an atom instead of triggering the fallback. -/
example : structurallyRepresents (relationalizeCandidate equalCoarsePair) equalCoarsePair = true := by
  native_decide

example : (relationalize equalCoarsePair).data.atoms.size = 3 := by
  native_decide

private structure WrittenNat where
  value : Nat

private instance writtenNatIdentity : SpytialIdentity WrittenNat := .asWritten

private def isAsWritten : RelationalizerCore.Identity IdentityKey IdentityKey → Bool
  | .asWritten => true
  | .keyed _ _ => false

/-- Typed exposure passes an explicit `SpytialIdentity.asWritten` policy to the walker. -/
example :
    isAsWritten (valueIdentity (IdentityKey.ofString "WrittenNat") (⟨1⟩ : WrittenNat)) =
      true := by
  simp [isAsWritten, valueIdentity, ValueIdentity.key?]

end StructuralExposureTest
