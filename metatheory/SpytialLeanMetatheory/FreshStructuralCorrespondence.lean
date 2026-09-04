module

public import SpytialLeanMetatheory.ProductionTraceInstance
public meta import SpytialLean.StructuralCorrespondence

public section

/-!
# Semantic meaning of fresh structural correspondence

The production checker aligns two independently generated structural traces.
This file interprets that checked alignment: corresponding relation heads,
column types, and column terms are definitionally equal, while atom IDs are
related by a two-sided finite mapping.
-/

namespace SpytialLean.Metatheory

open Lean SpytialLean

universe u v

/-- The semantic information carried by one production tuple column. -/
public structure StructuralColumnMeaning {World : Type u}
    {context : Iykyk.Metatheory.Context World}
    (meaning : LeanExprMeaning World context) where
  term : meaning.ExprCode
  type : meaning.TypeCode
  atom : Option String

/-- The structural rule distinguished by a production relation. -/
public inductive StructuralRuleMeaning (ExprCode : Type u) where
  | constructorField (constructor : Name) (index : Nat)
  | projection (field : Name) (application : ExprCode)

/-- Interpret one checked structural kind modulo Lean definitional equality. -/
@[expose] public def structuralRuleMeaning {World : Type u}
    {context : Iykyk.Metatheory.Context World}
    (meaning : LeanExprMeaning World context) :
    CheckedStructuralKind → StructuralRuleMeaning meaning.ExprCode
  | .constructorField constructor index => .constructorField constructor index
  | .projection field application =>
      .projection field (Quotient.mk meaning.defEq application)

/-- Interpret checked columns while applying a chosen atom-ID map. -/
@[expose] public def structuralColumnMeanings {World : Type u}
    {context : Iykyk.Metatheory.Context World}
    (meaning : LeanExprMeaning World context) (atom : String → Option String) :
    {terms : List Expr} → {atoms : List String} →
      CheckedColumns terms atoms → List (StructuralColumnMeaning meaning)
  | _, _, .nil => []
  | _, _, .cons (term := term) (atom := atomId) head tail =>
      { term := Quotient.mk meaning.defEq term
        type := Quotient.mk meaning.defEq head.type
        atom := atom atomId } :: structuralColumnMeanings meaning atom tail

/-- The semantic and graph information carried by one structural origin. -/
public structure StructuralOriginMeaning {World : Type u}
    {context : Iykyk.Metatheory.Context World}
    (meaning : LeanExprMeaning World context) where
  relation : String
  rule : StructuralRuleMeaning meaning.ExprCode
  head : meaning.ExprCode
  source : meaning.ExprCode
  child : meaning.ExprCode
  columns : List (StructuralColumnMeaning meaning)

/-- Interpret one checked structural origin under an atom-ID map. -/
@[expose] public def structuralOriginMeaning {World : Type u}
    {context : Iykyk.Metatheory.Context World}
    (meaning : LeanExprMeaning World context) (atom : String → Option String)
    (origin : CheckedStructuralOrigin) : StructuralOriginMeaning meaning where
  relation := origin.relation
  rule := structuralRuleMeaning meaning origin.kind
  head := Quotient.mk meaning.defEq origin.head
  source := Quotient.mk meaning.defEq origin.source
  child := Quotient.mk meaning.defEq origin.child
  columns := structuralColumnMeanings meaning atom origin.columns

/-- Interpret all checked origins of one structural trace. -/
@[expose] public def structuralTraceMeaning {World : Type u}
    {context : Iykyk.Metatheory.Context World}
    (meaning : LeanExprMeaning World context) (atom : String → Option String)
    {trace : TracedDataInstance} (checked : CheckedStructuralTrace trace) :
    List (StructuralOriginMeaning meaning) :=
  checked.origins.toList.map fun origin => structuralOriginMeaning meaning atom origin

/-- Two checked traces have the same relational structure when a two-sided
    atom mapping makes their semantic origin lists equal in both directions. -/
public def SameProductionStructure {World : Type u}
    {context : Iykyk.Metatheory.Context World}
    (meaning : LeanExprMeaning World context)
    {leftTrace rightTrace : TracedDataInstance}
    (left : CheckedStructuralTrace leftTrace)
    (right : CheckedStructuralTrace rightTrace) : Prop :=
  ∃ mapping : AtomRenaming,
    structuralTraceMeaning meaning mapping.forward? left =
        structuralTraceMeaning meaning some right ∧
      structuralTraceMeaning meaning mapping.backward? right =
        structuralTraceMeaning meaning some left

/-- The completed inspection retains its root structural phase as its first
    semantic structural rows, up to the atom names reconstructed by its two
    production checks. -/
public def RootStructureRetained {World : Type u}
    {context : Iykyk.Metatheory.Context World}
    (meaning : LeanExprMeaning World context)
    {rootTrace fullTrace : TracedDataInstance}
    (root : CheckedStructuralTrace rootTrace)
    (full : CheckedStructuralTrace fullTrace) : Prop :=
  let fullPrefix := full.origins.toList.take root.origins.size
  ∃ mapping : AtomRenaming,
    structuralTraceMeaning meaning mapping.forward? root =
        fullPrefix.map (structuralOriginMeaning meaning some) ∧
      fullPrefix.map (structuralOriginMeaning meaning mapping.backward?) =
        structuralTraceMeaning meaning some root

namespace CheckedStructuralKindAgreement

/-- Checked kind agreement has one meaning modulo definitional equality. -/
public theorem meaning_eq {World : Type u}
    {context : Iykyk.Metatheory.Context World}
    {meaning : LeanExprMeaning World context}
    (evidence : ProductionEvidenceMeaning meaning)
    {left right : CheckedStructuralKind}
    (agreement : CheckedStructuralKindAgreement left right) :
    structuralRuleMeaning meaning left = structuralRuleMeaning meaning right := by
  cases agreement with
  | constructorField => rfl
  | projection field application =>
      simp only [structuralRuleMeaning]
      rw [Quotient.sound (evidence.def_eq application)]

end CheckedStructuralKindAgreement

namespace CheckedColumnsAgreement

/-- Forward atom mapping preserves the semantic term and type of every column. -/
public theorem forward_meaning_eq {World : Type u}
    {context : Iykyk.Metatheory.Context World}
    {meaning : LeanExprMeaning World context}
    (evidence : ProductionEvidenceMeaning meaning) {mapping : AtomRenaming}
    {leftTerms rightTerms : List Expr} {leftAtoms rightAtoms : List String}
    {left : CheckedColumns leftTerms leftAtoms}
    {right : CheckedColumns rightTerms rightAtoms}
    (agreement : CheckedColumnsAgreement mapping left right) :
    structuralColumnMeanings meaning mapping.forward? left =
      structuralColumnMeanings meaning some right := by
  induction agreement with
  | nil => rfl
  | @cons leftTerm rightTerm leftAtom rightAtom leftTerms rightTerms leftAtoms rightAtoms
      leftHead rightHead leftTail rightTail term type forward backward tail ih =>
      simp only [structuralColumnMeanings]
      rw [Quotient.sound (evidence.def_eq term),
        Quotient.sound (evidence.def_eq type), forward, ih]

/-- Backward atom mapping preserves the semantic term and type of every column. -/
public theorem backward_meaning_eq {World : Type u}
    {context : Iykyk.Metatheory.Context World}
    {meaning : LeanExprMeaning World context}
    (evidence : ProductionEvidenceMeaning meaning) {mapping : AtomRenaming}
    {leftTerms rightTerms : List Expr} {leftAtoms rightAtoms : List String}
    {left : CheckedColumns leftTerms leftAtoms}
    {right : CheckedColumns rightTerms rightAtoms}
    (agreement : CheckedColumnsAgreement mapping left right) :
    structuralColumnMeanings meaning mapping.backward? right =
      structuralColumnMeanings meaning some left := by
  induction agreement with
  | nil => rfl
  | @cons leftTerm rightTerm leftAtom rightAtom leftTerms rightTerms leftAtoms rightAtoms
      leftHead rightHead leftTail rightTail term type forward backward tail ih =>
      simp only [structuralColumnMeanings]
      rw [Quotient.sound (meaning.defEq.symm (evidence.def_eq term)),
        Quotient.sound (meaning.defEq.symm (evidence.def_eq type)), backward, ih]

end CheckedColumnsAgreement

namespace CheckedStructuralOriginAgreement

/-- One checked origin pair has equal semantic meaning under the forward map. -/
public theorem forward_meaning_eq {World : Type u}
    {context : Iykyk.Metatheory.Context World}
    {meaning : LeanExprMeaning World context}
    (evidence : ProductionEvidenceMeaning meaning) {mapping : AtomRenaming}
    {left right : CheckedStructuralOrigin}
    (agreement : CheckedStructuralOriginAgreement mapping left right) :
    structuralOriginMeaning meaning mapping.forward? left =
      structuralOriginMeaning meaning some right := by
  cases agreement with
  | mk relation kind source child head columns =>
      simp only [structuralOriginMeaning]
      rw [relation, CheckedStructuralKindAgreement.meaning_eq evidence kind,
        Quotient.sound (evidence.def_eq head), Quotient.sound (evidence.def_eq source),
        Quotient.sound (evidence.def_eq child),
        CheckedColumnsAgreement.forward_meaning_eq evidence columns]

/-- One checked origin pair has equal semantic meaning under the backward map. -/
public theorem backward_meaning_eq {World : Type u}
    {context : Iykyk.Metatheory.Context World}
    {meaning : LeanExprMeaning World context}
    (evidence : ProductionEvidenceMeaning meaning) {mapping : AtomRenaming}
    {left right : CheckedStructuralOrigin}
    (agreement : CheckedStructuralOriginAgreement mapping left right) :
    structuralOriginMeaning meaning mapping.backward? right =
      structuralOriginMeaning meaning some left := by
  cases agreement with
  | mk relation kind source child head columns =>
      simp only [structuralOriginMeaning]
      rw [relation, CheckedStructuralKindAgreement.meaning_eq evidence kind,
        Quotient.sound (evidence.def_eq head),
        Quotient.sound (meaning.defEq.symm (evidence.def_eq source)),
        Quotient.sound (meaning.defEq.symm (evidence.def_eq child)),
        CheckedColumnsAgreement.backward_meaning_eq evidence columns]

end CheckedStructuralOriginAgreement

namespace CheckedStructuralOriginsAgreement

/-- An aligned origin list has the same forward semantic meaning. -/
public theorem forward_meaning_eq {World : Type u}
    {context : Iykyk.Metatheory.Context World}
    {meaning : LeanExprMeaning World context}
    (evidence : ProductionEvidenceMeaning meaning) {mapping : AtomRenaming}
    {left right : List CheckedStructuralOrigin}
    (agreement : CheckedStructuralOriginsAgreement mapping left right) :
    left.map (structuralOriginMeaning meaning mapping.forward?) =
      right.map (structuralOriginMeaning meaning some) := by
  induction agreement with
  | nil => rfl
  | cons head tail ih =>
      simp only [List.map_cons]
      rw [CheckedStructuralOriginAgreement.forward_meaning_eq evidence head, ih]

/-- An aligned origin list has the same backward semantic meaning. -/
public theorem backward_meaning_eq {World : Type u}
    {context : Iykyk.Metatheory.Context World}
    {meaning : LeanExprMeaning World context}
    (evidence : ProductionEvidenceMeaning meaning) {mapping : AtomRenaming}
    {left right : List CheckedStructuralOrigin}
    (agreement : CheckedStructuralOriginsAgreement mapping left right) :
    right.map (structuralOriginMeaning meaning mapping.backward?) =
      left.map (structuralOriginMeaning meaning some) := by
  induction agreement with
  | nil => rfl
  | cons head tail ih =>
      simp only [List.map_cons]
      rw [CheckedStructuralOriginAgreement.backward_meaning_eq evidence head, ih]

end CheckedStructuralOriginsAgreement

namespace CheckedStructuralIso

/-- A production-checked structural isomorphism implies equality of relation
    heads, rules, typed terms, and graph connectivity in both directions. -/
public theorem same_production_structure {World : Type u}
    {context : Iykyk.Metatheory.Context World}
    {meaning : LeanExprMeaning World context}
    (evidence : ProductionEvidenceMeaning meaning)
    {leftTrace rightTrace : TracedDataInstance}
    {left : CheckedStructuralTrace leftTrace}
    {right : CheckedStructuralTrace rightTrace}
    (isomorphism : CheckedStructuralIso left right) :
    SameProductionStructure meaning left right :=
  ⟨isomorphism.mapping,
    CheckedStructuralOriginsAgreement.forward_meaning_eq evidence isomorphism.origins,
    CheckedStructuralOriginsAgreement.backward_meaning_eq evidence isomorphism.origins⟩

end CheckedStructuralIso

namespace CheckedRootPrefix

/-- A checked root prefix has the same semantic structural rows in both
    directions. -/
public theorem root_structure_retained {World : Type u}
    {context : Iykyk.Metatheory.Context World}
    {meaning : LeanExprMeaning World context}
    (evidence : ProductionEvidenceMeaning meaning)
    {rootTrace fullTrace : TracedDataInstance}
    {root : CheckedStructuralTrace rootTrace}
    {full : CheckedStructuralTrace fullTrace}
    (retained : CheckedRootPrefix root full) : RootStructureRetained meaning root full :=
  ⟨retained.mapping,
    CheckedStructuralOriginsAgreement.forward_meaning_eq evidence retained.agreement,
    CheckedStructuralOriginsAgreement.backward_meaning_eq evidence retained.agreement⟩

end CheckedRootPrefix

/-- Every checked fresh production run has the same semantic structural rows
    as the root phase retained by proof-guided inspection. The two traces are
    distinct inputs to the checked correspondence; only generated atom names
    may differ. -/
public theorem fresh_relationalization_agrees_with_inspection_root
    {World : Type u} {context : Iykyk.Metatheory.Context World}
    {meaning : LeanExprMeaning World context} {knowledge : Iykyk.Afaik}
    (production : CheckedFreshRelationalization knowledge)
    (evidence : ProductionEvidenceMeaning meaning) :
    SameProductionStructure meaning production.inspection.run.computedChecked
      production.checked :=
  CheckedStructuralIso.same_production_structure evidence production.correspondence

/-- Every completed proof-guided inspection retains the checked structural
    rows from its root walk before any structure introduced by contextual
    facts. -/
public theorem inspection_retains_root_structure
    {World : Type u} {context : Iykyk.Metatheory.Context World}
    {meaning : LeanExprMeaning World context} {knowledge : Iykyk.Afaik}
    (production : CheckedFreshRelationalization knowledge)
    (evidence : ProductionEvidenceMeaning meaning) :
    RootStructureRetained meaning production.inspection.run.computedChecked
      production.inspection.run.structuralChecked :=
  CheckedRootPrefix.root_structure_retained evidence production.rootPrefix

end SpytialLean.Metatheory
