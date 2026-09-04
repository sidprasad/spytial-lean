module

public meta import SpytialLean.InContext

namespace SpytialLean

open Lean Meta

/-- A finite mapping between atom identifiers in two production runs. -/
public abbrev AtomRenaming := List (String × String)

namespace AtomRenaming

/-- Look up the atom corresponding to a left-hand identifier. -/
@[expose] public meta def forward? (mapping : AtomRenaming) (atom : String) : Option String :=
  (mapping.find? fun pair => pair.1 == atom).map (·.2)

/-- Look up the atom corresponding to a right-hand identifier. -/
@[expose] public meta def backward? (mapping : AtomRenaming) (atom : String) : Option String :=
  (mapping.find? fun pair => pair.2 == atom).map (·.1)

end AtomRenaming

/-- Checked agreement between the constructor/projection classifications of
    two structural origins. -/
public inductive CheckedStructuralKindAgreement :
    CheckedStructuralKind → CheckedStructuralKind → Type where
  | constructorField (constructor : Name) (index : Nat) :
      CheckedStructuralKindAgreement (.constructorField constructor index)
        (.constructorField constructor index)
  | projection (field : Name) {leftApplication rightApplication : Expr}
      (application : CheckedDefEq leftApplication rightApplication) :
      CheckedStructuralKindAgreement (.projection field leftApplication)
        (.projection field rightApplication)

/-- Checked pointwise agreement between two typed column lists. It records
    definitional equality of terms and types as well as the atom mapping in
    both directions. -/
public inductive CheckedColumnsAgreement (mapping : AtomRenaming) :
    {leftTerms : List Expr} → {leftAtoms : List String} →
      CheckedColumns leftTerms leftAtoms →
    {rightTerms : List Expr} → {rightAtoms : List String} →
      CheckedColumns rightTerms rightAtoms → Type where
  | nil : CheckedColumnsAgreement mapping (.nil : CheckedColumns [] []) .nil
  | cons {leftTerm rightTerm : Expr} {leftAtom rightAtom : String}
      {leftTerms rightTerms : List Expr} {leftAtoms rightAtoms : List String}
      {leftHead : CheckedColumn leftTerm leftAtom}
      {rightHead : CheckedColumn rightTerm rightAtom}
      {leftTail : CheckedColumns leftTerms leftAtoms}
      {rightTail : CheckedColumns rightTerms rightAtoms}
      (term : CheckedDefEq leftTerm rightTerm)
      (type : CheckedDefEq leftHead.type rightHead.type)
      (forward : mapping.forward? leftAtom = some rightAtom)
      (backward : mapping.backward? rightAtom = some leftAtom)
      (tail : CheckedColumnsAgreement mapping leftTail rightTail) :
      CheckedColumnsAgreement mapping (.cons leftHead leftTail)
        (.cons rightHead rightTail)

/-- One aligned pair of structural origins has the same relation, structural
    rule, Lean terms, Lean types, and graph endpoints up to atom mapping. -/
public structure CheckedStructuralOriginAgreement (mapping : AtomRenaming)
    (left right : CheckedStructuralOrigin) where
  relation : left.relation = right.relation
  kind : CheckedStructuralKindAgreement left.kind right.kind
  source : CheckedDefEq left.source right.source
  child : CheckedDefEq left.child right.child
  head : CheckedDefEq left.head right.head
  columns : CheckedColumnsAgreement mapping left.columns right.columns

/-- Ordered checked origins from two independent runs correspond one for one.
    The independent production walks give the checker this aligned witness. -/
public inductive CheckedStructuralOriginsAgreement (mapping : AtomRenaming) :
    List CheckedStructuralOrigin → List CheckedStructuralOrigin → Type where
  | nil : CheckedStructuralOriginsAgreement mapping [] []
  | cons {left right lefts rights}
      (head : CheckedStructuralOriginAgreement mapping left right)
      (tail : CheckedStructuralOriginsAgreement mapping lefts rights) :
      CheckedStructuralOriginsAgreement mapping (left :: lefts) (right :: rights)

/-- A checked structural isomorphism between two actual production traces.
    Every active atom is paired in both directions by the aligned columns. -/
public structure CheckedStructuralIso {leftTrace rightTrace : TracedDataInstance}
    (left : CheckedStructuralTrace leftTrace)
    (right : CheckedStructuralTrace rightTrace) where
  mapping : AtomRenaming
  origins : CheckedStructuralOriginsAgreement mapping left.origins.toList
    right.origins.toList

private meta def insertAtomPair? (mapping : AtomRenaming) (left right : String) :
    Option AtomRenaming :=
  match mapping.forward? left, mapping.backward? right with
  | none, none => some ((left, right) :: mapping)
  | some knownRight, some knownLeft =>
      if knownRight == right && knownLeft == left then some mapping else none
  | _, _ => none

private meta def insertAtomPairs? (mapping : AtomRenaming) :
    List String → List String → Option AtomRenaming
  | [], [] => some mapping
  | left :: lefts, right :: rights => do
      let mapping ← insertAtomPair? mapping left right
      insertAtomPairs? mapping lefts rights
  | _, _ => none

private meta def collectAtomRenaming? :
    List CheckedStructuralOrigin → List CheckedStructuralOrigin →
      Option AtomRenaming
  | [], [] => some []
  | left :: lefts, right :: rights => do
      let mapping ← collectAtomRenaming? lefts rights
      insertAtomPairs? mapping left.emission.tuple.atoms.toList
        right.emission.tuple.atoms.toList
  | _, _ => none

private meta def checkKindAgreement : (left right : CheckedStructuralKind) →
    MetaM (CheckedStructuralKindAgreement left right)
  | .constructorField leftConstructor leftIndex,
      .constructorField rightConstructor rightIndex => do
    if constructorEq : leftConstructor = rightConstructor then
      if indexEq : leftIndex = rightIndex then
        return by
          simpa [constructorEq, indexEq] using
            (CheckedStructuralKindAgreement.constructorField leftConstructor leftIndex)
      else
        throwError "spytial: fresh structural runs disagree on constructor field index"
    else
      throwError "spytial: fresh structural runs disagree on constructor"
  | .projection leftField leftApplication, .projection rightField rightApplication => do
    if fieldEq : leftField = rightField then
      let application ← CheckedDefEq.check leftApplication rightApplication
      return by
        simpa [fieldEq] using
          (CheckedStructuralKindAgreement.projection leftField application)
    else
      throwError "spytial: fresh structural runs disagree on projection"
  | _, _ =>
      throwError "spytial: fresh structural runs disagree on structural rule"

private meta def checkColumnsAgreement (mapping : AtomRenaming) :
    {leftTerms : List Expr} → {leftAtoms : List String} →
      (left : CheckedColumns leftTerms leftAtoms) →
    {rightTerms : List Expr} → {rightAtoms : List String} →
      (right : CheckedColumns rightTerms rightAtoms) →
      MetaM (CheckedColumnsAgreement mapping left right)
  | _, _, .nil, _, _, .nil => pure .nil
  | _, _, .cons (term := leftTerm) (atom := leftAtom) leftHead leftTail,
      _, _, .cons (term := rightTerm) (atom := rightAtom) rightHead rightTail => do
    let term ← CheckedDefEq.check leftTerm rightTerm
    let type ← CheckedDefEq.check leftHead.type rightHead.type
    if forward : mapping.forward? leftAtom = some rightAtom then
      if backward : mapping.backward? rightAtom = some leftAtom then
        let tail ← checkColumnsAgreement mapping leftTail rightTail
        return .cons term type forward backward tail
      else
        throwError "spytial: fresh structural atom mapping has no inverse"
    else
      throwError "spytial: fresh structural atom mapping is inconsistent"
  | _, _, _, _, _, _ =>
      throwError "spytial: fresh structural runs have different tuple arities"

private meta def checkOriginAgreement (mapping : AtomRenaming)
    (left right : CheckedStructuralOrigin) :
    MetaM (CheckedStructuralOriginAgreement mapping left right) := do
  if relation : left.relation = right.relation then
    let kind ← checkKindAgreement left.kind right.kind
    let source ← CheckedDefEq.check left.source right.source
    let child ← CheckedDefEq.check left.child right.child
    let head ← CheckedDefEq.check left.head right.head
    let columns ← checkColumnsAgreement mapping left.columns right.columns
    return { relation, kind, source, child, head, columns }
  else
    throwError "spytial: fresh structural runs disagree on relation name"

private meta def checkOriginsAgreement (mapping : AtomRenaming) :
    (left right : List CheckedStructuralOrigin) →
      MetaM (CheckedStructuralOriginsAgreement mapping left right)
  | [], [] => pure .nil
  | left :: lefts, right :: rights => do
      let head ← checkOriginAgreement mapping left right
      let tail ← checkOriginsAgreement mapping lefts rights
      return .cons head tail
  | _, _ =>
      throwError "spytial: fresh structural runs emitted different tuple counts"

namespace CheckedStructuralIso

/-- Validate structural correspondence between two independent checked
    production traces. -/
public meta def check {leftTrace rightTrace : TracedDataInstance}
    (left : CheckedStructuralTrace leftTrace)
    (right : CheckedStructuralTrace rightTrace) : MetaM (CheckedStructuralIso left right) := do
  let some mapping := collectAtomRenaming? left.origins.toList right.origins.toList
    | throwError "spytial: fresh structural runs do not admit an atom bijection"
  let origins ← checkOriginsAgreement mapping left.origins.toList right.origins.toList
  return { mapping, origins }

end CheckedStructuralIso

/-- The structural origins retained after the root walk are the first
    structural origins of the completed proof-guided inspection. Later origins
    may describe values introduced by contextual facts. -/
public structure CheckedRootPrefix {rootTrace fullTrace : TracedDataInstance}
    (root : CheckedStructuralTrace rootTrace)
    (full : CheckedStructuralTrace fullTrace) where
  mapping : AtomRenaming
  agreement : CheckedStructuralOriginsAgreement mapping root.origins.toList
    (full.origins.toList.take root.origins.size)

namespace CheckedRootPrefix

/-- Check the retained root phase against the corresponding prefix of the
    completed proof-guided structural trace. -/
public meta def check {rootTrace fullTrace : TracedDataInstance}
    (root : CheckedStructuralTrace rootTrace)
    (full : CheckedStructuralTrace fullTrace) : MetaM (CheckedRootPrefix root full) := do
  let rootOrigins := root.origins.toList
  let fullPrefix := full.origins.toList.take root.origins.size
  let some mapping := collectAtomRenaming? rootOrigins fullPrefix
    | throwError "spytial: the completed inspection does not retain its root structure"
  let agreement ← checkOriginsAgreement mapping rootOrigins fullPrefix
  return { mapping, agreement }

end CheckedRootPrefix

/-- A proof-guided inspection and a genuinely fresh call to
    `relationalizeWithTrace` on its retained value, together with checked
    correspondence between the two structural traces. -/
public meta structure CheckedFreshRelationalization (knowledge : Iykyk.Afaik) where
  private mk ::
  inspection : CheckedKnownValueInspection knowledge
  trace : TracedDataInstance
  checked : CheckedStructuralTrace trace
  rootPrefix : CheckedRootPrefix inspection.run.computedChecked
    inspection.run.structuralChecked
  correspondence : CheckedStructuralIso inspection.run.computedChecked checked

namespace CheckedFreshRelationalization

/-- Rerun the actual ordinary relationalizer on the retained computed term.
    The core correspondence excludes observations, whose proof-assisted
    simplification has separate semantic rules. -/
public meta def check {knowledge : Iykyk.Afaik}
    (inspection : CheckedKnownValueInspection knowledge) :
    MetaM (CheckedFreshRelationalization knowledge) := do
  unless inspection.run.observations.isEmpty do
    throwError "spytial: fresh structural correspondence does not include observations"
  let config : WalkConfig := {
    inspection.run.baseConfig with
    functionGraphs := true
    shareSymbolicValues := true }
  let (trace, provenance, evidence) ←
    relationalizeWithTrace inspection.run.computedTerm config
  let checked ← checkStructuralTrace config trace provenance evidence
  let rootPrefix ← CheckedRootPrefix.check inspection.run.computedChecked
    inspection.run.structuralChecked
  let correspondence ← CheckedStructuralIso.check inspection.run.computedChecked checked
  return .mk inspection trace checked rootPrefix correspondence

/-- Run proof-guided inspection and independently rerun the ordinary
    relationalizer on the value that inspection obtained. A returned value
    carries the checked correspondence used by the semantic theorem. -/
public meta def inspect (knowledge : Iykyk.Afaik) (baseConfig : WalkConfig := {}) :
    MetaM (CheckedFreshRelationalization knowledge) := do
  check (← inspectKnownValue knowledge baseConfig)

end CheckedFreshRelationalization

end SpytialLean
