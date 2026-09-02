module

public import Lean

namespace SpytialLean

open Lean

/-! # The display layer

Declarations a type makes about how the walker draws it — orthogonal to
`SpytialIdentity` (which occurrences merge) and to the spec language (how the
drawn graph is laid out). Everything here is consulted by the walker
(`Relationalizer`) and by the static checkers (`TypeShape`, the selector
scope), so a declaration changes the datum and the vocabulary together.

These exist so that a type whose interesting picture is not its constructor
cells — `Lean.Expr`, `Lean.Name` — can be drawn through the ordinary walk
instead of hand-emitting atoms: see `SpytialView` in `Relationalizer.lean` for
the rewrite step that pairs with them. -/

/-! ## Field wrappers

Real structures, not `Raw`-style transparent defs: a field is recognized by
its declared type head, and nothing should melt to the carrier by accident.
The cost is spelling `.mk` at construction sites, which for view types are a
single builder function. -/

/-- A field the walker never walks: no atom, no relation, invisible to the
    selector vocabulary. For data that exists to be *read* by the type's own
    instances — an identity key, a display label — not to be drawn. Distinct
    from the spec's `hideField`, which hides the drawn edge and leaves the
    child atom behind. -/
public structure Hidden (α : Type u) : Type u where
  val : α

/-- A field that is a relation extension, not a child atom: each element
    becomes one tuple in the field-named relation, owner-prefixed. An element
    of product type contributes one column per component; any other element
    type is a single column. `Rel.nil` declares the relation with no tuples —
    also the idiom for an optional edge (`Rel [x]` / `Rel.nil`). The syntactic
    counterpart of function-field tabulation, which already emits relations,
    not atoms. -/
public structure Rel (α : Type u) : Type u where
  elems : List α

public def Rel.nil {α : Type u} : Rel α := ⟨[]⟩

public meta instance {α : Type u} [ToLevel.{u}] [ToExpr α] : ToExpr (Hidden α) :=
  let type := toTypeExpr α
  { toExpr h := mkApp2 (mkConst ``Hidden.mk [toLevel.{u}]) type (toExpr h.val),
    toTypeExpr := mkApp (mkConst ``Hidden [toLevel.{u}]) type }

public meta instance {α : Type u} [ToLevel.{u}] [ToExpr α] : ToExpr (Rel α) :=
  let type := toTypeExpr α
  { toExpr r := mkApp2 (mkConst ``Rel.mk [toLevel.{u}]) type (toExpr r.elems),
    toTypeExpr := mkApp (mkConst ``Rel [toLevel.{u}]) type }

/-! ## Display classes -/

/-- The label of `α`'s atoms, computed from the value. Evaluated compiled on
    closed values (the same machinery as `Repr` leaf labels — which this
    outranks); an open or stuck value keeps the default label. Labels only:
    a non-injective label never merges atoms, that is `SpytialIdentity`. -/
public class SpytialDisplay (α : Type u) where
  label : α → String

/-- `α` never decomposes: one atom per value, labeled by `SpytialDisplay`,
    else `Repr`, else its spelling. For types whose structure is plumbing —
    `Lean.Name`'s string chains. Identity still applies: equal leaves merge
    per the type's declared or derived identity. -/
public class SpytialLeaf (α : Type u) where

/-- Atoms of this inductive take their *constructor's* short name as their
    atom type (the tuple columns follow). For a sum-of-roles type — a view
    type whose constructors are the vocabulary a spec targets — where the one
    inductive name would make every role the same type. The type vocabulary
    is the constructor list, so it stays closed and checkable. -/
public class SpytialCtorTypes (α : Type u) where

end SpytialLean
