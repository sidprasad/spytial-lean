module

public import SpytialLeanMetatheory.SemanticInstance
public import SpytialLeanMetatheory.RelationalInstance
public meta import SpytialLean.Relationalizer

public section

/-!
# Relational structure obtained by computation

This file states the semantic obligations for the direct structural part of a
real computed-value trace. The executable checker recognizes constructor
fields and projections and checks field coverage. A separate interpretation
must connect those checked expressions to typed semantic tuples and show that
the tuples are true. Given that interpretation, this file proves soundness and
semantic field coverage.
-/

namespace SpytialLean.Metatheory

open SpytialLean

universe u v w x

/-- A production origin belongs to the direct constructor/projection fragment. -/
public inductive IsStructuralOrigin : TupleOrigin → Prop where
  | intro (terms : Array Lean.Expr) : IsStructuralOrigin (.structural terms)

/-- A value returned by the production structural checker really does retain
    a structural trace origin. -/
public theorem checkedStructuralOrigin_is_structural (origin : CheckedStructuralOrigin) :
    IsStructuralOrigin origin.emission.origin := by
  rw [origin.origin_eq]
  exact .intro origin.terms

/-- A relation between the actual production trace and a typed semantic
    instance. `represents emission tuple` includes the atom-ID, type, and
    relation-symbol correspondence chosen by the Lean-expression bridge. -/
public structure TraceRealization {World : Type u} {SemanticType : Type v}
    {context : Iykyk.Metatheory.Context World}
    {signature : RelationalSignature SemanticType} {Carrier : SemanticType → Type w}
    (trace : TracedDataInstance)
    (data : SemanticInstance.{u, v, w, x} context signature Carrier) where
  represents : TupleEmission → RelationalTuple signature data.Atom → Prop
  output_represented : ∀ tuple, tuple ∈ data.tuples →
    ∃ emission ∈ trace.emissions, represents emission tuple
  represented_is_output : ∀ emission ∈ trace.emissions, ∀ tuple,
    represents emission tuple → tuple ∈ data.tuples

/-- The structural facts expected from a computed value. For an algebraic
    value these are its non-proof constructor fields and structure
    projections, expressed as semantic tuples. -/
public abbrev StructuralRequirement {SemanticType : Type v}
    {signature : RelationalSignature SemanticType}
    {Entry : SemanticType → Type x} :=
  RelationalTuple signature Entry → Prop

/-- Every required structural fact occurs in the finite semantic instance. -/
@[expose] public def StructurallyComplete {World : Type u} {SemanticType : Type v}
    {context : Iykyk.Metatheory.Context World}
    {signature : RelationalSignature SemanticType} {Carrier : SemanticType → Type w}
    (data : SemanticInstance.{u, v, w, x} context signature Carrier)
    (required : StructuralRequirement (signature := signature) (Entry := data.Atom)) : Prop :=
  ∀ tuple, required tuple → tuple ∈ data.tuples

/-- The semantic interpretation paired with a successful executable
    structural check. Its obligations are local:

    * each output tuple has a structural production origin;
    * each such origin has the correct semantic meaning; and
    * every expected field has a corresponding structural origin.

    The executable checker supplies the checked origins and syntactic field
    coverage. The `LeanExprMeaning` boundary supplies their typing and
    denotation. -/
public structure ComputedStructuralCertificate {World : Type u}
    {SemanticType : Type v} {context : Iykyk.Metatheory.Context World}
    {signature : RelationalSignature SemanticType} {Carrier : SemanticType → Type w}
    (trace : TracedDataInstance)
    (data : SemanticInstance.{u, v, w, x} context signature Carrier)
    (ground : World → GroundInstance signature Carrier)
    (required : StructuralRequirement (signature := signature) (Entry := data.Atom))
    (checked : CheckedStructuralTrace trace) where
  realization : TraceRealization trace data
  output_has_checked_origin : ∀ tuple, tuple ∈ data.tuples →
    ∃ origin ∈ checked.origins.toList, origin.emission ∈ trace.emissions ∧
      realization.represents origin.emission tuple
  checked_origin_sound : ∀ origin ∈ checked.origins.toList,
    origin.emission ∈ trace.emissions → ∀ tuple,
      realization.represents origin.emission tuple →
      ∀ world (compatible : context world),
        data.TupleHolds ground tuple world compatible
  required_has_checked_origin : ∀ tuple, required tuple →
    ∃ origin ∈ checked.origins.toList, origin.emission ∈ trace.emissions ∧
      realization.represents origin.emission tuple

namespace ComputedStructuralCertificate

/-- A completed semantic certificate implies soundness of the computed
    structural slice. -/
public theorem adequate {World : Type u} {SemanticType : Type v}
    {context : Iykyk.Metatheory.Context World}
    {signature : RelationalSignature SemanticType} {Carrier : SemanticType → Type w}
    {trace : TracedDataInstance}
    {data : SemanticInstance.{u, v, w, x} context signature Carrier}
    {ground : World → GroundInstance signature Carrier}
    {required : StructuralRequirement (signature := signature) (Entry := data.Atom)}
    {checked : CheckedStructuralTrace trace}
    (certificate : ComputedStructuralCertificate trace data ground required checked) :
    Completes context data ground := by
  intro world compatible tuple present
  obtain ⟨origin, originMem, emissionMem, represented⟩ :=
    certificate.output_has_checked_origin tuple present
  exact certificate.checked_origin_sound origin originMem emissionMem tuple represented
    world compatible

/-- Origin coverage for every expected field implies structural completeness
    of the semantic instance. -/
public theorem structurallyComplete {World : Type u} {SemanticType : Type v}
    {context : Iykyk.Metatheory.Context World}
    {signature : RelationalSignature SemanticType} {Carrier : SemanticType → Type w}
    {trace : TracedDataInstance}
    {data : SemanticInstance.{u, v, w, x} context signature Carrier}
    {ground : World → GroundInstance signature Carrier}
    {required : StructuralRequirement (signature := signature) (Entry := data.Atom)}
    {checked : CheckedStructuralTrace trace}
    (certificate : ComputedStructuralCertificate trace data ground required checked) :
    StructurallyComplete data required := by
  intro tuple expected
  obtain ⟨origin, _, emissionMem, represented⟩ :=
    certificate.required_has_checked_origin tuple expected
  exact certificate.realization.represented_is_output origin.emission emissionMem tuple represented

/-- The computed theorem supplies both directions normally hidden by the word
    "faithful": no emitted structural tuple is wrong, and no required
    structural field is missing. -/
public theorem adequate_and_structurallyComplete {World : Type u}
    {SemanticType : Type v} {context : Iykyk.Metatheory.Context World}
    {signature : RelationalSignature SemanticType} {Carrier : SemanticType → Type w}
    {trace : TracedDataInstance}
    {data : SemanticInstance.{u, v, w, x} context signature Carrier}
    {ground : World → GroundInstance signature Carrier}
    {required : StructuralRequirement (signature := signature) (Entry := data.Atom)}
    {checked : CheckedStructuralTrace trace}
    (certificate : ComputedStructuralCertificate trace data ground required checked) :
    Completes context data ground ∧ StructurallyComplete data required :=
  ⟨certificate.adequate, certificate.structurallyComplete⟩

end ComputedStructuralCertificate

end SpytialLean.Metatheory
