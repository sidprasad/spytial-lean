module

public import SpytialLeanMetatheory.LeanExprMeaning
public import SpytialLean.Types
public import SpytialLean.Relationalizer
public meta import SpytialLean.InContext

public section

/-!
# One relational meaning for production tuples

The finite production trace does not define truth. `LeanExprMeaning.ground`
interprets relation symbols independently of any trace. Opaque tokens record
successful Lean checks, and `ProductionEvidenceMeaning` states what those
checks mean. Tuple soundness crosses both boundaries explicitly.
-/

namespace SpytialLean.Metatheory

open Lean SpytialLean

universe u v

namespace LeanExprMeaning

/-- A semantic instance made from expression-backed tuples. -/
@[expose] public def instanceOfTuples {World : Type u}
    {context : Iykyk.Metatheory.Context World}
    (meaning : LeanExprMeaning World context)
    (tuples : List (RelationalTuple meaning.signature (ExprAtom meaning))) :
    SemanticInstance context meaning.signature meaning.Carrier :=
  SemanticInstance.ofTuples context meaning.signature meaning.Carrier
    (ExprAtom meaning) ExprAtom.denote tuples

end LeanExprMeaning

/-- Unfold the expression-backed signature at a relation symbol. -/
@[expose] public def exprRelation {World : Type u}
    {context : Iykyk.Metatheory.Context World}
    {meaning : LeanExprMeaning World context}
    (relation : meaning.signature.Relation) : LeanExprMeaning.ExprRelation meaning :=
  relation

/-- The production atom identifiers used by one expression-backed tuple. -/
@[expose] public def exprTupleAtomIds {World : Type u}
    {context : Iykyk.Metatheory.Context World}
    {meaning : LeanExprMeaning World context}
    (tuple : RelationalTuple meaning.signature (LeanExprMeaning.ExprAtom meaning)) :
    List String :=
  tuple.atoms.map fun atom => atom.value.id

/-- The checked Lean terms denoted by an expression-backed tuple. -/
@[expose] public def exprTupleTerms {World : Type u}
    {context : Iykyk.Metatheory.Context World}
    {meaning : LeanExprMeaning World context}
    (tuple : RelationalTuple meaning.signature (LeanExprMeaning.ExprAtom meaning)) :
    List Expr :=
  tuple.atoms.map fun atom => atom.value.term.expression

/-- Syntactic and typed correspondence between a checked proof origin and a
    semantic tuple. This contains no tuple-truth premise. -/
public structure ProvedTupleRealization {World : Type u}
    {context : Iykyk.Metatheory.Context World}
    (meaning : LeanExprMeaning World context) (origin : CheckedProvedOrigin)
    (tuple : RelationalTuple meaning.signature (LeanExprMeaning.ExprAtom meaning)) where
  relation_name : (exprRelation tuple.relation).name = origin.relation
  relation_head : (exprRelation tuple.relation).head =
    Quotient.mk meaning.defEq origin.head
  relation_parameters : (exprRelation tuple.relation).parameters =
    origin.parameters.toList.map fun parameter => Quotient.mk meaning.defEq parameter
  column_types : (exprRelation tuple.relation).columns =
    origin.columns.types.map fun type => Quotient.mk meaning.defEq type
  atom_ids : exprTupleAtomIds tuple = origin.atoms.toList
  atom_terms : exprTupleTerms tuple = origin.terms.toList

/-- Syntactic and typed correspondence between a checked constructor-field
    or projection origin and a semantic tuple. The Lean head is retained, so
    the ground interpretation cannot confuse equal display names. -/
public structure StructuralTupleRealization {World : Type u}
    {context : Iykyk.Metatheory.Context World}
    (meaning : LeanExprMeaning World context) (origin : CheckedStructuralOrigin)
    (tuple : RelationalTuple meaning.signature (LeanExprMeaning.ExprAtom meaning)) where
  relation_name : (exprRelation tuple.relation).name = origin.relation
  relation_head : (exprRelation tuple.relation).head =
    Quotient.mk meaning.defEq origin.head
  relation_parameters : (exprRelation tuple.relation).parameters = []
  column_types : (exprRelation tuple.relation).columns =
    origin.columns.types.map fun type => Quotient.mk meaning.defEq type
  atom_ids : exprTupleAtomIds tuple = origin.emission.tuple.atoms.toList
  atom_terms : exprTupleTerms tuple = origin.terms.toList

/-- Interpretation of the opaque evidence tokens minted by production
    checkers. Every law is conditional on a token. The final two laws connect
    checked syntax to the independently supplied relational ground. -/
public structure ProductionEvidenceMeaning {World : Type u}
    {context : Iykyk.Metatheory.Context World}
    (meaning : LeanExprMeaning World context) where
  has_type : ∀ {term type}, CheckedHasType term type → meaning.hasType term type
  def_eq : ∀ {left right}, CheckedDefEq left right → meaning.defEq.r left right
  proof_checks : ∀ {proposition proof}, CheckedProof proposition proof →
    meaning.proofChecks proposition proof
  equality_shape : ∀ {proposition type root value},
    CheckedEqualityShape proposition type root value →
      proposition.eq? = some (type, root, value) ∨
        proposition.eq? = some (type, value, root)
  proposition_defEq : ∀ (origin : CheckedProvedOrigin)
    (tuple : RelationalTuple meaning.signature (LeanExprMeaning.ExprAtom meaning)),
    ProvedTupleRealization meaning origin tuple →
    CheckedPropositionShape origin.proposition origin.kind origin.relation origin.head
      origin.parameters origin.terms →
    ∀ world (compatible : context world),
      meaning.proposition origin.proposition world ↔
        (meaning.instanceOfTuples [tuple]).TupleHolds meaning.ground tuple world compatible
  structural_relation : ∀ (origin : CheckedStructuralOrigin)
    (tuple : RelationalTuple meaning.signature (LeanExprMeaning.ExprAtom meaning)),
    StructuralTupleRealization meaning origin tuple →
    CheckedStructuralShape origin.relation origin.kind origin.source origin.child
      origin.terms →
    ∀ world (compatible : context world),
      (meaning.instanceOfTuples [tuple]).TupleHolds meaning.ground tuple world compatible

namespace ProductionEvidenceMeaning

/-- Interpret the token stored in a checked tuple column. -/
public theorem column_has_type {World : Type u}
    {context : Iykyk.Metatheory.Context World}
    {meaning : LeanExprMeaning World context}
    (evidence : ProductionEvidenceMeaning meaning)
    {term : Expr} {atom : String} (column : CheckedColumn term atom) :
    meaning.hasType term column.type :=
  evidence.has_type column.hasType

/-- Interpret the proof token stored in a checked proposition origin. -/
public theorem proved_origin_checks {World : Type u}
    {context : Iykyk.Metatheory.Context World}
    {meaning : LeanExprMeaning World context}
    (evidence : ProductionEvidenceMeaning meaning) (origin : CheckedProvedOrigin) :
    meaning.proofChecks origin.proposition origin.proof :=
  evidence.proof_checks origin.proofChecked

/-- Interpret the root-typing token stored in computation evidence. -/
public theorem computation_root_has_type {World : Type u}
    {context : Iykyk.Metatheory.Context World}
    {meaning : LeanExprMeaning World context}
    (evidence : ProductionEvidenceMeaning meaning) {knowledge : Iykyk.Afaik}
    {computed : Expr} (checked : CheckedComputedValue knowledge computed) :
    meaning.hasType knowledge.root checked.type :=
  evidence.has_type checked.rootHasType

/-- Interpret the result-typing token stored in computation evidence. -/
public theorem computation_result_has_type {World : Type u}
    {context : Iykyk.Metatheory.Context World}
    {meaning : LeanExprMeaning World context}
    (evidence : ProductionEvidenceMeaning meaning) {knowledge : Iykyk.Afaik}
    {computed : Expr} (checked : CheckedComputedValue knowledge computed) :
    meaning.hasType computed checked.type :=
  evidence.has_type checked.computedHasType

/-- Interpret the definitional-equality token stored in computation evidence. -/
public theorem computation_defEq {World : Type u}
    {context : Iykyk.Metatheory.Context World}
    {meaning : LeanExprMeaning World context}
    (evidence : ProductionEvidenceMeaning meaning) {knowledge : Iykyk.Afaik}
    {computed : Expr} (checked : CheckedComputedValue knowledge computed) :
    meaning.defEq.r knowledge.root computed :=
  evidence.def_eq checked.equal

/-- Interpret the root-typing token stored in proof refinement evidence. -/
public theorem refinement_root_has_type {World : Type u}
    {context : Iykyk.Metatheory.Context World}
    {meaning : LeanExprMeaning World context}
    (evidence : ProductionEvidenceMeaning meaning) {knowledge : Iykyk.Afaik}
    {computed : Expr} (checked : CheckedEqualityRefinement knowledge computed) :
    meaning.hasType knowledge.root checked.type :=
  evidence.has_type checked.rootHasType

/-- Interpret the value-typing token stored in proof refinement evidence. -/
public theorem refinement_value_has_type {World : Type u}
    {context : Iykyk.Metatheory.Context World}
    {meaning : LeanExprMeaning World context}
    (evidence : ProductionEvidenceMeaning meaning) {knowledge : Iykyk.Afaik}
    {computed : Expr} (checked : CheckedEqualityRefinement knowledge computed) :
    meaning.hasType checked.value checked.type :=
  evidence.has_type checked.valueHasType

/-- Interpret the result-typing token stored in proof refinement evidence. -/
public theorem refinement_computed_has_type {World : Type u}
    {context : Iykyk.Metatheory.Context World}
    {meaning : LeanExprMeaning World context}
    (evidence : ProductionEvidenceMeaning meaning) {knowledge : Iykyk.Afaik}
    {computed : Expr} (checked : CheckedEqualityRefinement knowledge computed) :
    meaning.hasType computed checked.type :=
  evidence.has_type checked.computedHasType

/-- Interpret the kernel-check token stored in proof refinement evidence. -/
public theorem refinement_proof_checks {World : Type u}
    {context : Iykyk.Metatheory.Context World}
    {meaning : LeanExprMeaning World context}
    (evidence : ProductionEvidenceMeaning meaning) {knowledge : Iykyk.Afaik}
    {computed : Expr} (checked : CheckedEqualityRefinement knowledge computed) :
    meaning.proofChecks checked.proposition checked.fact.proof :=
  evidence.proof_checks checked.proofChecked

/-- Interpret the equality-shape token stored in proof refinement evidence. -/
public theorem refinement_shape {World : Type u}
    {context : Iykyk.Metatheory.Context World}
    {meaning : LeanExprMeaning World context}
    (evidence : ProductionEvidenceMeaning meaning) {knowledge : Iykyk.Afaik}
    {computed : Expr} (checked : CheckedEqualityRefinement knowledge computed) :
    checked.proposition.eq? = some (checked.type, knowledge.root, checked.value) ∨
      checked.proposition.eq? = some (checked.type, checked.value, knowledge.root) :=
  evidence.equality_shape checked.equalityShape

/-- Interpret the value/result equality token stored in proof refinement evidence. -/
public theorem refinement_value_defEq {World : Type u}
    {context : Iykyk.Metatheory.Context World}
    {meaning : LeanExprMeaning World context}
    (evidence : ProductionEvidenceMeaning meaning) {knowledge : Iykyk.Afaik}
    {computed : Expr} (checked : CheckedEqualityRefinement knowledge computed) :
    meaning.defEq.r checked.value computed :=
  evidence.def_eq checked.valueEqualsComputed

/-- Interpret the selected root at the common checked type. -/
public theorem root_has_type {World : Type u}
    {context : Iykyk.Metatheory.Context World}
    {meaning : LeanExprMeaning World context}
    (evidence : ProductionEvidenceMeaning meaning)
    {knowledge : Iykyk.Afaik} {computed : Expr}
    (source : CheckedValueSource knowledge computed) :
    meaning.hasType knowledge.root source.type :=
  match source with
  | ⟨_, .computation checked⟩ => evidence.computation_root_has_type checked
  | ⟨_, .proof checked⟩ => evidence.refinement_root_has_type checked

/-- Interpret the walked result at the common checked type. -/
public theorem result_has_type {World : Type u}
    {context : Iykyk.Metatheory.Context World}
    {meaning : LeanExprMeaning World context}
    (evidence : ProductionEvidenceMeaning meaning)
    {knowledge : Iykyk.Afaik} {computed : Expr}
    (source : CheckedValueSource knowledge computed) :
    meaning.hasType computed source.type :=
  match source with
  | ⟨_, .computation checked⟩ => evidence.computation_result_has_type checked
  | ⟨_, .proof checked⟩ => evidence.refinement_computed_has_type checked

/-- Computation or a checked equality gives the root and walked expression
    the same denotation. -/
public theorem checked_value_denotes_same {World : Type u}
    {context : Iykyk.Metatheory.Context World}
    {meaning : LeanExprMeaning World context}
    (evidence : ProductionEvidenceMeaning meaning)
    {knowledge : Iykyk.Afaik} {computed : Expr}
    (source : CheckedValueSource knowledge computed)
    (world : World) (compatible : context world) :
    meaning.denote knowledge.root source.type (evidence.root_has_type source)
        world compatible =
      meaning.denote computed source.type (evidence.result_has_type source)
        world compatible := by
  rcases source with ⟨_, reason⟩
  cases reason with
  | computation checked =>
      exact meaning.denote_defEq
        (evidence.computation_root_has_type checked)
        (evidence.computation_result_has_type checked)
        (meaning.defEq.refl checked.type)
        (evidence.computation_defEq checked)
        world compatible
  | proof refinement =>
      have propositionHolds := meaning.proofChecks_sound
        (evidence.refinement_proof_checks refinement) world compatible
      have rootEqualsValue :
          meaning.denote knowledge.root refinement.type
              (evidence.refinement_root_has_type refinement) world compatible =
            meaning.denote refinement.value refinement.type
              (evidence.refinement_value_has_type refinement) world compatible := by
        rcases evidence.refinement_shape refinement with forward | backward
        · exact meaning.equality_sound forward
            (evidence.refinement_root_has_type refinement)
            (evidence.refinement_value_has_type refinement)
            world compatible propositionHolds
        · exact (meaning.equality_sound backward
            (evidence.refinement_value_has_type refinement)
            (evidence.refinement_root_has_type refinement)
            world compatible propositionHolds).symm
      have valueEqualsComputed :
          meaning.denote refinement.value refinement.type
              (evidence.refinement_value_has_type refinement) world compatible =
            meaning.denote computed refinement.type
              (evidence.refinement_computed_has_type refinement) world compatible :=
        meaning.denote_defEq
          (evidence.refinement_value_has_type refinement)
          (evidence.refinement_computed_has_type refinement)
          (meaning.defEq.refl refinement.type)
          (evidence.refinement_value_defEq refinement)
          world compatible
      exact rootEqualsValue.trans valueEqualsComputed

end ProductionEvidenceMeaning

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

/-- Interpret aligned checked columns as one intrinsically typed tuple. -/
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

/-- Converting checked columns preserves production atom IDs. -/
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

/-- Converting checked columns preserves their Lean terms. -/
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

/-- The typed relation symbol reconstructed from a checked proof origin. -/
@[expose] public def provedOriginRelation {World : Type u}
    {context : Iykyk.Metatheory.Context World}
    {meaning : LeanExprMeaning World context} (origin : CheckedProvedOrigin) :
    LeanExprMeaning.ExprRelation meaning where
  name := origin.relation
  head := Quotient.mk meaning.defEq origin.head
  parameters := origin.parameters.toList.map fun parameter =>
    Quotient.mk meaning.defEq parameter
  columns := origin.columns.types.map fun type => Quotient.mk meaning.defEq type

/-- The typed semantic tuple reconstructed from a checked proof origin. -/
@[expose] public def provedOriginTuple {World : Type u}
    {context : Iykyk.Metatheory.Context World}
    {meaning : LeanExprMeaning World context}
    (evidence : ProductionEvidenceMeaning meaning) (origin : CheckedProvedOrigin) :
    RelationalTuple meaning.signature (LeanExprMeaning.ExprAtom meaning) where
  relation := provedOriginRelation origin
  entries := checkedColumnEntries evidence origin.columns

/-- Canonical proof-origin tuple construction satisfies its syntactic
    realization obligations. -/
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

/-- The constructor or projection constant represented by a structural origin. -/
@[expose] public def structuralOriginHead (origin : CheckedStructuralOrigin) : Expr :=
  origin.head

/-- The typed relation symbol reconstructed from a checked structural origin. -/
@[expose] public def structuralOriginRelation {World : Type u}
    {context : Iykyk.Metatheory.Context World}
    {meaning : LeanExprMeaning World context} (origin : CheckedStructuralOrigin) :
    LeanExprMeaning.ExprRelation meaning where
  name := origin.relation
  head := Quotient.mk meaning.defEq (structuralOriginHead origin)
  parameters := []
  columns := origin.columns.types.map fun type => Quotient.mk meaning.defEq type

/-- The typed semantic tuple reconstructed from a checked structural origin. -/
@[expose] public def structuralOriginTuple {World : Type u}
    {context : Iykyk.Metatheory.Context World}
    {meaning : LeanExprMeaning World context}
    (evidence : ProductionEvidenceMeaning meaning) (origin : CheckedStructuralOrigin) :
    RelationalTuple meaning.signature (LeanExprMeaning.ExprAtom meaning) where
  relation := structuralOriginRelation origin
  entries := checkedColumnEntries evidence origin.columns

/-- Canonical structural tuple construction satisfies its syntactic
    realization obligations. -/
public theorem structuralOriginTuple_realizes {World : Type u}
    {context : Iykyk.Metatheory.Context World}
    {meaning : LeanExprMeaning World context}
    (evidence : ProductionEvidenceMeaning meaning) (origin : CheckedStructuralOrigin) :
    StructuralTupleRealization meaning origin (structuralOriginTuple evidence origin) where
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

namespace ProductionTupleHolds

/-- The ground comes from `LeanExprMeaning`, never from emitted tuples. -/
@[expose] public def ground {World : Type u}
    {context : Iykyk.Metatheory.Context World}
    (meaning : LeanExprMeaning World context) :
    World → GroundInstance meaning.signature meaning.Carrier :=
  meaning.ground

/-- A true decoded proposition establishes its tuple in the independent ground. -/
public theorem provedTupleHolds {World : Type u}
    {context : Iykyk.Metatheory.Context World}
    {meaning : LeanExprMeaning World context}
    (evidence : ProductionEvidenceMeaning meaning)
    {tuples : List (RelationalTuple meaning.signature
      (LeanExprMeaning.ExprAtom meaning))}
    {origin : CheckedProvedOrigin}
    {tuple : RelationalTuple meaning.signature (LeanExprMeaning.ExprAtom meaning)}
    (realization : ProvedTupleRealization meaning origin tuple)
    (world : World) (compatible : context world)
    (propositionHolds : meaning.proposition origin.proposition world) :
    (meaning.instanceOfTuples tuples).TupleHolds (ground meaning) tuple world compatible := by
  exact (evidence.proposition_defEq origin tuple realization origin.shapeChecked
    world compatible).mp propositionHolds

/-- A retained kernel proof establishes its decoded tuple in the ground. -/
public theorem checkedProvedTupleHolds {World : Type u}
    {context : Iykyk.Metatheory.Context World}
    {meaning : LeanExprMeaning World context}
    (evidence : ProductionEvidenceMeaning meaning)
    {tuples : List (RelationalTuple meaning.signature
      (LeanExprMeaning.ExprAtom meaning))}
    {origin : CheckedProvedOrigin}
    {tuple : RelationalTuple meaning.signature (LeanExprMeaning.ExprAtom meaning)}
    (realization : ProvedTupleRealization meaning origin tuple)
    (world : World) (compatible : context world) :
    (meaning.instanceOfTuples tuples).TupleHolds (ground meaning) tuple world compatible := by
  apply provedTupleHolds evidence realization world compatible
  exact meaning.proofChecks_sound (evidence.proved_origin_checks origin) world compatible

/-- A checked constructor-field or projection origin establishes its tuple in
    the independent ground relation. -/
public theorem structuralTupleHolds {World : Type u}
    {context : Iykyk.Metatheory.Context World}
    {meaning : LeanExprMeaning World context}
    (evidence : ProductionEvidenceMeaning meaning)
    {tuples : List (RelationalTuple meaning.signature
      (LeanExprMeaning.ExprAtom meaning))}
    {origin : CheckedStructuralOrigin}
    {tuple : RelationalTuple meaning.signature (LeanExprMeaning.ExprAtom meaning)}
    (realization : StructuralTupleRealization meaning origin tuple)
    (world : World) (compatible : context world) :
    (meaning.instanceOfTuples tuples).TupleHolds (ground meaning) tuple world compatible := by
  exact evidence.structural_relation origin tuple realization origin.shape world compatible

end ProductionTupleHolds

end SpytialLean.Metatheory
