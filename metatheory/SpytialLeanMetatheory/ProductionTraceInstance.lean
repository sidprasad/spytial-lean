module

public import SpytialLeanMetatheory.Inspection

public section

/-!
# Semantic instances constructed from checked production traces

The production checker returns `CheckedColumn` values only after Lean has
inferred the type of each term. This file interprets those values once and
then constructs the typed atoms, tuples, and inspection result directly from
checked structural and proof origins.

Custom, observed, tabulated, symbolic, and synthetic origins are not assigned
a rule here. They remain available in production output, but are outside this
core soundness claim.
-/

namespace SpytialLean.Metatheory

open Lean SpytialLean

universe u v

/-- Agreement between the semantic model and the two checks performed by the
    production core. These are global laws for checked evidence, not premises
    repeated for individual tuples or traces. -/
public structure ProductionEvidenceMeaning {World : Type u}
    {context : Iykyk.Metatheory.Context World}
    (meaning : LeanExprMeaning World context) where
  column_has_type : ∀ {term atom} (column : CheckedColumn term atom),
    meaning.hasType term column.type
  proved_origin_checks : ∀ origin : CheckedProvedOrigin,
    meaning.proofChecks origin.proposition origin.proof

/-- Interpret one production-checked column as an expression-backed atom. -/
public def checkedColumnAtom {World : Type u}
    {context : Iykyk.Metatheory.Context World}
    {meaning : LeanExprMeaning World context}
    (evidence : ProductionEvidenceMeaning meaning)
    {term : Expr} {atom : String} (column : CheckedColumn term atom) :
    LeanExprMeaning.ExprAtom meaning (Quotient.mk meaning.defEq column.type) where
  id := atom
  term := {
    expression := term
    type := column.type
    checked := evidence.column_has_type column }
  type_eq := rfl

/-- Interpret an aligned checked column list as one intrinsically typed tuple. -/
@[expose] public def checkedColumnEntries {World : Type u}
    {context : Iykyk.Metatheory.Context World}
    {meaning : LeanExprMeaning World context}
    (evidence : ProductionEvidenceMeaning meaning) :
    {terms : List Expr} → {atoms : List String} →
      (columns : CheckedColumns terms atoms) →
        TypedTuple (LeanExprMeaning.ExprAtom meaning)
          (columns.types.map fun type => Quotient.mk meaning.defEq type)
  | _, _, .nil => .nil
  | _, _, .cons head tail =>
      .cons (checkedColumnAtom evidence head) (checkedColumnEntries evidence tail)

/-- Converting checked columns preserves their production atom IDs. -/
public theorem checkedColumnEntries_atomIds {World : Type u}
    {context : Iykyk.Metatheory.Context World}
    {meaning : LeanExprMeaning World context}
    (evidence : ProductionEvidenceMeaning meaning)
    {terms : List Expr} {atoms : List String}
    (columns : CheckedColumns terms atoms) :
    (checkedColumnEntries evidence columns).atoms.map (fun atom => atom.value.id) = atoms := by
  induction columns with
  | nil => rfl
  | @cons term atom terms atoms head tail ih =>
      simpa only [checkedColumnEntries, TypedTuple.atoms, List.map_cons,
        checkedColumnAtom] using congrArg (List.cons atom) ih

/-- Converting checked columns preserves their checked Lean terms. -/
public theorem checkedColumnEntries_terms {World : Type u}
    {context : Iykyk.Metatheory.Context World}
    {meaning : LeanExprMeaning World context}
    (evidence : ProductionEvidenceMeaning meaning)
    {terms : List Expr} {atoms : List String}
    (columns : CheckedColumns terms atoms) :
    (checkedColumnEntries evidence columns).atoms.map
      (fun atom => atom.value.term.expression) = terms := by
  induction columns with
  | nil => rfl
  | @cons term atom terms atoms head tail ih =>
      simpa only [checkedColumnEntries, TypedTuple.atoms, List.map_cons,
        checkedColumnAtom] using congrArg (List.cons term) ih

/-- The typed relation symbol reconstructed from one checked proof origin. -/
@[expose] public def provedOriginRelation {World : Type u}
    {context : Iykyk.Metatheory.Context World}
    {meaning : LeanExprMeaning World context} (origin : CheckedProvedOrigin) :
    LeanExprMeaning.ExprRelation meaning where
  name := origin.relation
  head := Quotient.mk meaning.defEq origin.head
  parameters := origin.parameters.toList.map fun parameter =>
    Quotient.mk meaning.defEq parameter
  columns := origin.columns.types.map fun type => Quotient.mk meaning.defEq type

/-- The typed semantic tuple reconstructed from one checked proof origin. -/
@[expose] public def provedOriginTuple {World : Type u}
    {context : Iykyk.Metatheory.Context World}
    {meaning : LeanExprMeaning World context}
    (evidence : ProductionEvidenceMeaning meaning) (origin : CheckedProvedOrigin) :
    RelationalTuple meaning.signature (LeanExprMeaning.ExprAtom meaning) where
  relation := provedOriginRelation origin
  entries := checkedColumnEntries evidence origin.columns

/-- Tuple construction discharges every local proof-origin realization field. -/
public theorem provedOriginTuple_realizes {World : Type u}
    {context : Iykyk.Metatheory.Context World}
    {meaning : LeanExprMeaning World context}
    (evidence : ProductionEvidenceMeaning meaning) (origin : CheckedProvedOrigin) :
    ProvedTupleRealization meaning origin (provedOriginTuple evidence origin) where
  relation_name := rfl
  relation_head := rfl
  relation_parameters := rfl
  column_types := rfl
  atom_ids := by
    change (checkedColumnEntries evidence origin.columns).atoms.map
      (fun atom => atom.value.id) = origin.emission.tuple.atoms.toList
    exact checkedColumnEntries_atomIds evidence origin.columns
  atom_terms := by
    change (checkedColumnEntries evidence origin.columns).atoms.map
      (fun atom => atom.value.term.expression) = origin.terms.toList
    exact checkedColumnEntries_terms evidence origin.columns
  proof_checked := evidence.proved_origin_checks origin

/-- The constructor or projection constant represented by a structural origin. -/
@[expose] public def structuralOriginHead (origin : CheckedStructuralOrigin) : Expr :=
  match origin.kind with
  | .constructorField _ _ => origin.source.getAppFn
  | .projection _ application => application.getAppFn

/-- The typed relation symbol reconstructed from one checked structural
    origin. Constructor and projection constants distinguish relations that
    happen to have the same short display name. -/
@[expose] public def structuralOriginRelation {World : Type u}
    {context : Iykyk.Metatheory.Context World}
    {meaning : LeanExprMeaning World context} (origin : CheckedStructuralOrigin) :
    LeanExprMeaning.ExprRelation meaning where
  name := origin.relation
  head := Quotient.mk meaning.defEq (structuralOriginHead origin)
  parameters := []
  columns := origin.columns.types.map fun type => Quotient.mk meaning.defEq type

/-- The typed semantic tuple reconstructed from one checked structural origin. -/
@[expose] public def structuralOriginTuple {World : Type u}
    {context : Iykyk.Metatheory.Context World}
    {meaning : LeanExprMeaning World context}
    (evidence : ProductionEvidenceMeaning meaning) (origin : CheckedStructuralOrigin) :
    RelationalTuple meaning.signature (LeanExprMeaning.ExprAtom meaning) where
  relation := structuralOriginRelation origin
  entries := checkedColumnEntries evidence origin.columns

/-- Tuple construction discharges every local structural realization field. -/
public theorem structuralOriginTuple_realizes {World : Type u}
    {context : Iykyk.Metatheory.Context World}
    {meaning : LeanExprMeaning World context}
    (evidence : ProductionEvidenceMeaning meaning) (origin : CheckedStructuralOrigin) :
    StructuralTupleRealization meaning origin (structuralOriginTuple evidence origin) where
  relation_name := rfl
  column_types := rfl
  atom_ids := by
    change (checkedColumnEntries evidence origin.columns).atoms.map
      (fun atom => atom.value.id) = origin.emission.tuple.atoms.toList
    exact checkedColumnEntries_atomIds evidence origin.columns
  atom_terms := by
    change (checkedColumnEntries evidence origin.columns).atoms.map
      (fun atom => atom.value.term.expression) = origin.terms.toList
    exact checkedColumnEntries_terms evidence origin.columns

/-- All typed tuples reconstructed from the checked proof origins of a trace. -/
@[expose] public def proofTraceTuples {World : Type u}
    {context : Iykyk.Metatheory.Context World}
    {meaning : LeanExprMeaning World context}
    {trace : TracedDataInstance} (checked : CheckedProofTrace trace)
    (evidence : ProductionEvidenceMeaning meaning) :
    List (RelationalTuple meaning.signature (LeanExprMeaning.ExprAtom meaning)) :=
  checked.origins.toList.map fun origin => provedOriginTuple evidence origin

/-- The checked proof origins construct a sound semantic instance with no
    per-trace proof-decoding obligation. -/
public theorem proofTraceTuples_sound {World : Type u}
    {context : Iykyk.Metatheory.Context World}
    {meaning : LeanExprMeaning World context}
    {trace : TracedDataInstance} (checked : CheckedProofTrace trace)
    (evidence : ProductionEvidenceMeaning meaning) :
    Completes context (meaning.instanceOfTuples (proofTraceTuples checked evidence))
      (ProductionTupleHolds.ground meaning) := by
  intro world compatible tuple present
  obtain ⟨origin, _, rfl⟩ := List.mem_map.mp present
  exact ProductionTupleHolds.checkedProvedTupleHolds
    (provedOriginTuple_realizes evidence origin) world compatible

/-- All typed tuples reconstructed from the checked structural origins of a trace. -/
@[expose] public def structuralTraceTuples {World : Type u}
    {context : Iykyk.Metatheory.Context World}
    {meaning : LeanExprMeaning World context}
    {trace : TracedDataInstance} (checked : CheckedStructuralTrace trace)
    (evidence : ProductionEvidenceMeaning meaning) :
    List (RelationalTuple meaning.signature (LeanExprMeaning.ExprAtom meaning)) :=
  checked.origins.toList.map fun origin => structuralOriginTuple evidence origin

/-- The checked structural origins construct a sound semantic instance with
    no per-origin soundness obligation. -/
public theorem structuralTraceTuples_sound {World : Type u}
    {context : Iykyk.Metatheory.Context World}
    {meaning : LeanExprMeaning World context}
    {trace : TracedDataInstance} (checked : CheckedStructuralTrace trace)
    (evidence : ProductionEvidenceMeaning meaning) :
    Completes context (meaning.instanceOfTuples (structuralTraceTuples checked evidence))
      (ProductionTupleHolds.ground meaning) := by
  intro world compatible tuple present
  obtain ⟨origin, _, rfl⟩ := List.mem_map.mp present
  exact ProductionTupleHolds.structuralTupleHolds
    (structuralOriginTuple_realizes evidence origin) world compatible

/-- The two checked built-in origin classes for one production trace. -/
public structure CheckedCoreTrace (trace : TracedDataInstance) where
  structural : CheckedStructuralTrace trace
  proofs : CheckedProofTrace trace

namespace CheckedCoreTrace

/-- Run both production checkers and retain exactly the checked built-in
    structural and proof origins. Other origin classes remain in the runtime
    trace but do not enter this semantic instance. -/
public meta def check (cfg : WalkConfig) (trace : TracedDataInstance)
    (provenance : Provenance) (selectorEvidence : SelectorEvidence) :
    MetaM (CheckedCoreTrace trace) := do
  return {
    structural := ← checkStructuralTrace cfg trace provenance selectorEvidence
    proofs := ← checkProofTrace trace selectorEvidence }

/-- The unified semantic inspection constructed from a checked core trace. -/
@[expose] public def inspection {World : Type u}
    {context : Iykyk.Metatheory.Context World}
    {meaning : LeanExprMeaning World context}
    {trace : TracedDataInstance} (checked : CheckedCoreTrace trace)
    (evidence : ProductionEvidenceMeaning meaning) : Inspection meaning where
  structuralTuples := structuralTraceTuples checked.structural evidence
  provedTuples := proofTraceTuples checked.proofs evidence

/-- Main production-instantiation theorem: every tuple reconstructed from the
    checked built-in relationalizers is true in the shared production ground. -/
public theorem inspection_sound {World : Type u}
    {context : Iykyk.Metatheory.Context World}
    {meaning : LeanExprMeaning World context}
    {trace : TracedDataInstance} (checked : CheckedCoreTrace trace)
    (evidence : ProductionEvidenceMeaning meaning) :
    Completes context (checked.inspection evidence).data
      (ProductionTupleHolds.ground meaning) :=
  (checked.inspection evidence).sound (ProductionTupleHolds.ground meaning)
    (structuralTraceTuples_sound checked.structural evidence)
    (proofTraceTuples_sound checked.proofs evidence)

end CheckedCoreTrace

end SpytialLean.Metatheory
