module

public import Lean
public import SpytialLeanMetatheory.SemanticInstance

public section

/-!
# Meaning of Lean expressions

The production relationalizer records real `Lean.Expr` values. This file gives
those expressions a place in the semantic model without attempting to prove
Lean's kernel correct inside Lean.

`LeanExprMeaning` is the small trusted boundary. An implementation supplies
the typing and definitional-equality results already checked by Lean, together
with their mathematical meanings. The formalization uses those results
explicitly.
-/

namespace SpytialLean.Metatheory

open Lean

universe u v w

/-- The information needed to interpret checked Lean expressions in possible
    worlds. `defEq` represents Lean's definitional equality on expressions;
    its restriction to type expressions identifies semantic types.
    `proofChecks claim proof` represents the successful kernel
    check that `proof` has type `claim` in the captured local context. -/
public structure LeanExprMeaning (World : Type u)
    (context : Iykyk.Metatheory.Context World) where
  defEq : Setoid Expr
  Carrier : Quotient defEq → Type v
  isType : Expr → Prop
  hasType : Expr → Expr → Prop
  hasType_isType : ∀ {term type}, hasType term type → isType type
  denote : ∀ (term type : Expr), hasType term type →
    ∀ world, context world → Carrier (Quotient.mk defEq type)
  denote_defEq : ∀ {left right leftType rightType : Expr}
    (leftChecked : hasType left leftType) (rightChecked : hasType right rightType)
    (typesEqual : defEq.r leftType rightType), defEq.r left right →
      ∀ world (compatible : context world),
        cast (congrArg Carrier (Quotient.sound typesEqual))
            (denote left leftType leftChecked world compatible) =
          denote right rightType rightChecked world compatible
  proposition : Expr → Iykyk.Metatheory.Fact World
  proofChecks : Expr → Expr → Prop
  proofChecks_sound : ∀ {claim proof}, proofChecks claim proof →
    Iykyk.Metatheory.Entails context (proposition claim)
  /-- Semantic meaning of Lean's actual equality expression. This is part of
      the trusted Lean-expression interpretation, not a premise supplied by
      an individual inspection theorem. -/
  equality_sound : ∀ {claim type left right : Expr},
    claim.eq? = some (type, left, right) →
    (leftChecked : hasType left type) → (rightChecked : hasType right type) →
    ∀ world (compatible : context world), proposition claim world →
      denote left type leftChecked world compatible =
        denote right type rightChecked world compatible
  /-- Interpretation of Lean-backed relation symbols. This is independent of
      any finite production trace: emitted tuples must be proved true in this
      relation structure. -/
  relationHolds : ∀ (world : World) (name : String) (head : Quotient defEq)
    (parameters : List (Quotient defEq)) (columns : List (Quotient defEq)),
      TypedTuple Carrier columns → Prop

namespace LeanExprMeaning

/-- An actual Lean expression considered up to definitional equality. -/
public abbrev ExprCode {World : Type u}
    {context : Iykyk.Metatheory.Context World}
    (meaning : LeanExprMeaning World context) :=
  Quotient meaning.defEq

/-- A semantic type is an actual Lean type expression, with definitionally
    equal expressions identified. -/
public abbrev TypeCode {World : Type u}
    {context : Iykyk.Metatheory.Context World}
    (meaning : LeanExprMeaning World context) :=
  meaning.ExprCode

/-- Definitionally equal Lean type expressions name the same semantic type. -/
public theorem typeCode_eq_of_defEq {World : Type u}
    {context : Iykyk.Metatheory.Context World}
    (meaning : LeanExprMeaning World context) {left right : Expr}
    (equal : meaning.defEq.r left right) :
    (Quotient.mk meaning.defEq left : meaning.TypeCode) =
      Quotient.mk meaning.defEq right :=
  Quotient.sound equal

/-- An actual Lean term paired with the actual Lean type accepted for it. -/
public structure CheckedTerm {World : Type u}
    {context : Iykyk.Metatheory.Context World}
    (meaning : LeanExprMeaning World context) where
  expression : Expr
  type : Expr
  checked : meaning.hasType expression type

namespace CheckedTerm

/-- The semantic type represented by a checked term's Lean type. -/
public abbrev typeCode {World : Type u}
    {context : Iykyk.Metatheory.Context World}
    {meaning : LeanExprMeaning World context} (term : CheckedTerm meaning) :
    meaning.TypeCode :=
  Quotient.mk meaning.defEq term.type

/-- Interpret a checked term in a world compatible with the proof context. -/
public abbrev denote {World : Type u}
    {context : Iykyk.Metatheory.Context World}
    {meaning : LeanExprMeaning World context} (term : CheckedTerm meaning)
    (world : World) (compatible : context world) :
    meaning.Carrier term.typeCode :=
  meaning.denote term.expression term.type term.checked world compatible

end CheckedTerm

/-- A semantic atom that retains both its production identifier and the
    checked Lean expression it denotes. The equality permits a type alias in
    the trace and its reduced Lean type to share one semantic type. -/
public structure ExprAtom {World : Type u}
    {context : Iykyk.Metatheory.Context World}
    (meaning : LeanExprMeaning World context) (type : meaning.TypeCode) where
  id : String
  term : CheckedTerm meaning
  type_eq : term.typeCode = type

namespace ExprAtom

/-- Interpret an expression-backed atom at its indexed semantic type. -/
@[expose] public def denote {World : Type u}
    {context : Iykyk.Metatheory.Context World}
    {meaning : LeanExprMeaning World context} {type : meaning.TypeCode}
    (atom : ExprAtom meaning type) (world : World) (compatible : context world) :
    meaning.Carrier type :=
  cast (congrArg meaning.Carrier atom.type_eq) (atom.term.denote world compatible)

end ExprAtom

/-- A relation decoded from an actual Lean head expression. `name` is only
    its display name; `head` distinguishes predicates with the same short
    name. -/
public structure ExprRelation {World : Type u}
    {context : Iykyk.Metatheory.Context World}
    (meaning : LeanExprMeaning World context) where
  name : String
  head : meaning.ExprCode
  parameters : List meaning.ExprCode
  columns : List meaning.TypeCode

/-- The signature whose symbols retain actual Lean relation heads. -/
@[expose] public def signature {World : Type u}
    {context : Iykyk.Metatheory.Context World}
    (meaning : LeanExprMeaning World context) :
    RelationalSignature meaning.TypeCode where
  Relation := ExprRelation meaning
  columns := ExprRelation.columns

/-- The relational ground generated by a Lean-expression interpretation. -/
@[expose] public def ground {World : Type u}
    {context : Iykyk.Metatheory.Context World}
    (meaning : LeanExprMeaning World context) :
    World → GroundInstance meaning.signature meaning.Carrier :=
  fun world => {
    holds := fun relation entries =>
      meaning.relationHolds world relation.name relation.head relation.parameters
        relation.columns entries }

end LeanExprMeaning

end SpytialLean.Metatheory
