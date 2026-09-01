module

/-! # The Lean selector contract

A layout op needs a selector: a set of tuples of diagram atoms. This file
defines what a selector *is* when written in Lean: a plain Lean function, in
one of two forms.

* **A predicate over represented values.** `σ → Bool` or `σ → Prop` (curried
  up to arity 4) selects represented tuples whose predicate can be established
  by computation or retained Lean evidence. Nothing is returned, so no equality
  instances are needed. Inputs can be symbolic.
* **A function of the value being drawn.** `Sel T α` wraps `T → Tuples α`;
  Spytial calls it on the datum at resolution time, and the returned tuples
  are selected — each returned value located by `==` (`BEq`).

Two rules complete the contract:

* **Selection is by value.** Atoms are keyed by value (structural identity,
  derived on demand), and derived `BEq` computes the same equality, so a
  returned value names exactly one atom. A type declared
  `SpytialIdentity.asWritten` keeps one atom per occurrence; a value then
  selects all of its occurrences, and questions of position belong to the
  relational selector language.
* **`Tuples` is read as a set.** Order and duplicates are ignored; Spytial
  deduplicates and sorts the result before it reaches the diagram.

Whole-value programs and Boolean predicates are ordinary computable code and
can be tested with `#eval`. Compiled execution at elaboration time requires
`meta import` for functions from other modules. Predicate resolution can also
use direct proofs and bounded simplification on symbolic inputs; no Decidable
instance is required for that path. All selections remain within the datum's
represented atoms.
-/

namespace Spytial

/-- A list read as a set: order and duplicates are ignored. -/
public abbrev Tuples (α : Type u) := List α

/-- A Lean selector for values of type `T`, selecting tuples of type `α`:
    a function Spytial calls on the value being drawn, at resolution time.
    `α` is one column (`Sel T RBNode`) or a product (`Sel T (RBNode × RBNode)`);
    its product structure is the selector's arity. Build one with the
    anonymous constructor: `⟨fun root => …⟩`. -/
public structure Sel (T : Type u) (α : Type v) : Type (max u v) where
  /-- The wrapped function: the tuples to select, computed from the datum. -/
  select : T → Tuples α

namespace Sel

/-- A selector applies like the function it wraps. -/
public instance instCoeFun {T : Type u} {α : Type v} :
    CoeFun (Sel T α) (fun _ => T → Tuples α) := ⟨Sel.select⟩

/-- Selectors form a union algebra; `Tuples` is a set, so `++` is `∪`. -/
public instance instUnion {T : Type u} {α : Type v} : Union (Sel T α) :=
  ⟨fun s r => ⟨fun t => s.select t ++ r.select t⟩⟩

/-! ## Resolution helpers

Everything below is called by Spytial inside the one term it evaluates per
selector; the names are stable because the resolver builds calls to them.
`u` arrays hold the walked values of one column, in atom order, so an index
into `u` *is* an atom. Results are index tuples. -/

/-- Positions in `u` holding a value equal to `x` — "every atom holding it". -/
public def idxOf {σ : Type u} [BEq σ] (u : Array σ) (x : σ) : List Nat :=
  (List.range u.size).filter fun i => u[i]? == some x

/-- A unary predicate, decided once per walked value. No equality needed:
    a predicate never returns a value, so nothing has to be located. -/
public def selIdx1 {σ : Type u} (u : Array σ) (p : σ → Bool) : List (List Nat) :=
  (List.range u.size).filterMap fun i =>
    u[i]?.bind fun v => if p v then some [i] else none

/-- A binary predicate, decided once per point of the product. -/
public def selIdx2 {σ₁ : Type u} {σ₂ : Type v} (u₁ : Array σ₁) (u₂ : Array σ₂)
    (p : σ₁ → σ₂ → Bool) : List (List Nat) :=
  (List.range u₁.size).flatMap fun i =>
    (List.range u₂.size).filterMap fun j =>
      u₁[i]?.bind fun a => u₂[j]?.bind fun b =>
        if p a b then some [i, j] else none

public def selIdx3 {σ₁ : Type u} {σ₂ : Type v} {σ₃ : Type w} (u₁ : Array σ₁)
    (u₂ : Array σ₂) (u₃ : Array σ₃) (p : σ₁ → σ₂ → σ₃ → Bool) : List (List Nat) :=
  (List.range u₁.size).flatMap fun i =>
    (List.range u₂.size).flatMap fun j =>
      (List.range u₃.size).filterMap fun k =>
        u₁[i]?.bind fun a => u₂[j]?.bind fun b => u₃[k]?.bind fun c =>
          if p a b c then some [i, j, k] else none

public def selIdx4 {σ₁ : Type u} {σ₂ : Type v} {σ₃ : Type w} {σ₄ : Type x}
    (u₁ : Array σ₁) (u₂ : Array σ₂) (u₃ : Array σ₃) (u₄ : Array σ₄)
    (p : σ₁ → σ₂ → σ₃ → σ₄ → Bool) : List (List Nat) :=
  (List.range u₁.size).flatMap fun i =>
    (List.range u₂.size).flatMap fun j =>
      (List.range u₃.size).flatMap fun k =>
        (List.range u₄.size).filterMap fun l =>
          u₁[i]?.bind fun a => u₂[j]?.bind fun b => u₃[k]?.bind fun c =>
            u₄[l]?.bind fun d =>
              if p a b c d then some [i, j, k, l] else none

/-- A `Sel`'s result: each returned value is located by `==` in its column —
    the "returning a value needs equality" half of the contract. Every column
    needs `BEq`, because every column is a returned value. -/
public def locate1 {σ : Type u} [BEq σ] (u : Array σ) (ts : Tuples σ) :
    List (List Nat) :=
  ts.flatMap fun x => (idxOf u x).map ([·])

public def locate2 {σ₁ σ₂ : Type u} [BEq σ₁] [BEq σ₂] (u₁ : Array σ₁)
    (u₂ : Array σ₂) (ts : Tuples (σ₁ × σ₂)) : List (List Nat) :=
  ts.flatMap fun (a, b) =>
    (idxOf u₁ a).flatMap fun i => (idxOf u₂ b).map fun j => [i, j]

public def locate3 {σ₁ σ₂ σ₃ : Type u} [BEq σ₁] [BEq σ₂] [BEq σ₃]
    (u₁ : Array σ₁) (u₂ : Array σ₂) (u₃ : Array σ₃)
    (ts : Tuples (σ₁ × σ₂ × σ₃)) : List (List Nat) :=
  ts.flatMap fun (a, b, c) =>
    (idxOf u₁ a).flatMap fun i =>
      (idxOf u₂ b).flatMap fun j => (idxOf u₃ c).map fun k => [i, j, k]

public def locate4 {σ₁ σ₂ σ₃ σ₄ : Type u} [BEq σ₁] [BEq σ₂] [BEq σ₃] [BEq σ₄]
    (u₁ : Array σ₁) (u₂ : Array σ₂) (u₃ : Array σ₃) (u₄ : Array σ₄)
    (ts : Tuples (σ₁ × σ₂ × σ₃ × σ₄)) : List (List Nat) :=
  ts.flatMap fun (a, b, c, d) =>
    (idxOf u₁ a).flatMap fun i =>
      (idxOf u₂ b).flatMap fun j =>
        (idxOf u₃ c).flatMap fun k => (idxOf u₄ d).map fun l => [i, j, k, l]

end Sel

end Spytial
