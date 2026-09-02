module

public import Lean
public import SpytialLean.Display
public import SpytialLean.Identity

namespace SpytialLean

open Lean

/-! # Lean's own metaprogramming values under the walker

Everything a tactic author points `#spytial` at is full of `Name`s, and a
`Name` walks as its cons spine — five atoms for `` `HAdd.hAdd `` — that say
nothing its literal would not. And `Expr` itself can neither derive an
identity (its `KVMap` reaches `Syntax`, whose nested inductives the deriver
refuses) nor want one — a syntax view must keep two occurrences of `bvar 0`
apart — so every walk over an `Expr` warned.

This module is the policy for those types, as display-layer declarations —
no hand emission anywhere. Imported by the library root, so it holds out of
the box; `ExprView.lean` carries `Expr`'s view itself. -/

/-- One leaf atom per `Name`: the cons spine is plumbing. -/
public meta instance : SpytialLeaf Lean.Name := ⟨⟩

/-- A closed name is labeled with its literal (`` `HAdd.hAdd ``), the empty
    name as `anonymous`. A stuck or open name declines evaluation and keeps
    the walker's fallback label (the pretty-printed spine). -/
public meta instance : SpytialDisplay Lean.Name :=
  ⟨fun n => if n.isAnonymous then "anonymous" else s!"`{n}"⟩

/-- Position is the meaning in a syntax view: two occurrences of `bvar 0`
    under different binders must stay two atoms. Also the honest answer —
    nothing derivable exists — so declaring it silences the per-walk decline
    warning. With `ExprView`'s registered view, this is what decides whether
    two occurrences of one `Expr` value share a drawn subtree: they do not. -/
public instance : SpytialIdentity Lean.Expr := .asWritten

end SpytialLean
