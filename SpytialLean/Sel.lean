module

/-! # The Lean selector contract

A selector is a plain Lean function in one of two forms: a predicate over
represented values (`σ → Bool` or `σ → Prop`, curried up to arity 4), keeping
the tuples it establishes, or a `Sel T α`, called on the value being drawn.

Selection is by value, so a type declared `SpytialIdentity.asWritten` keeps one
atom per occurrence and a value then selects all of its occurrences. Spytial
runs a selector at elaboration time, so a function it calls from another module
must be reachable by `meta import`. A predicate over symbolic inputs is instead
established from retained evidence and bounded simplification, which needs no
`Decidable` instance. -/

namespace Spytial

/-- A list read as a set: order and duplicates are ignored. -/
public abbrev Tuples (α : Type u) := List α

/-- The product structure of `α` is the selector's arity: `Sel T (Node × Node)`
    selects pairs. -/
public structure Sel (T : Type u) (α : Type v) : Type (max u v) where
  select : T → Tuples α

namespace Sel

public instance instCoeFun {T : Type u} {α : Type v} :
    CoeFun (Sel T α) (fun _ => T → Tuples α) := ⟨Sel.select⟩

/-- `Tuples` is a set, so `++` is `∪`. -/
public instance instUnion {T : Type u} {α : Type v} : Union (Sel T α) :=
  ⟨fun s r => ⟨fun t => s.select t ++ r.select t⟩⟩

/-! ## Resolution helpers

The resolver builds calls to these by name, so the names are load-bearing. A
`u` array holds one column's walked values in atom order, so an index into `u`
*is* an atom. -/

public def idxOf {σ : Type u} [BEq σ] (u : Array σ) (x : σ) : List Nat :=
  (List.range u.size).filter fun i => u[i]? == some x

/-- One column in front of a narrower selection. -/
private def over {σ : Type u} (u : Array σ) (rest : σ → List (List Nat)) :
    List (List Nat) :=
  (List.range u.size).flatMap fun i => ((u[i]?.map rest).getD []).map (i :: ·)

/-- No equality needed anywhere below: a predicate returns no value, so nothing
    has to be located. -/
public def selIdx1 {σ : Type u} (u : Array σ) (p : σ → Bool) : List (List Nat) :=
  over u fun a => if p a then [[]] else []

public def selIdx2 {σ₁ : Type u} {σ₂ : Type v} (u₁ : Array σ₁) (u₂ : Array σ₂)
    (p : σ₁ → σ₂ → Bool) : List (List Nat) :=
  over u₁ fun a => selIdx1 u₂ (p a)

public def selIdx3 {σ₁ : Type u} {σ₂ : Type v} {σ₃ : Type w} (u₁ : Array σ₁)
    (u₂ : Array σ₂) (u₃ : Array σ₃) (p : σ₁ → σ₂ → σ₃ → Bool) : List (List Nat) :=
  over u₁ fun a => selIdx2 u₂ u₃ (p a)

public def selIdx4 {σ₁ : Type u} {σ₂ : Type v} {σ₃ : Type w} {σ₄ : Type x}
    (u₁ : Array σ₁) (u₂ : Array σ₂) (u₃ : Array σ₃) (u₄ : Array σ₄)
    (p : σ₁ → σ₂ → σ₃ → σ₄ → Bool) : List (List Nat) :=
  over u₁ fun a => selIdx3 u₂ u₃ u₄ (p a)

/-- The other half: every column of a `Sel` result is a returned value, and a
    returned value is located by `==`. -/
public def locate1 {σ : Type u} [BEq σ] (u : Array σ) (ts : Tuples σ) :
    List (List Nat) :=
  ts.flatMap fun x => (idxOf u x).map ([·])

public def locate2 {σ₁ σ₂ : Type u} [BEq σ₁] [BEq σ₂] (u₁ : Array σ₁)
    (u₂ : Array σ₂) (ts : Tuples (σ₁ × σ₂)) : List (List Nat) :=
  ts.flatMap fun (a, b) =>
    (idxOf u₁ a).flatMap fun i => (locate1 u₂ [b]).map (i :: ·)

public def locate3 {σ₁ σ₂ σ₃ : Type u} [BEq σ₁] [BEq σ₂] [BEq σ₃]
    (u₁ : Array σ₁) (u₂ : Array σ₂) (u₃ : Array σ₃)
    (ts : Tuples (σ₁ × σ₂ × σ₃)) : List (List Nat) :=
  ts.flatMap fun (a, b) =>
    (idxOf u₁ a).flatMap fun i => (locate2 u₂ u₃ [b]).map (i :: ·)

public def locate4 {σ₁ σ₂ σ₃ σ₄ : Type u} [BEq σ₁] [BEq σ₂] [BEq σ₃] [BEq σ₄]
    (u₁ : Array σ₁) (u₂ : Array σ₂) (u₃ : Array σ₃) (u₄ : Array σ₄)
    (ts : Tuples (σ₁ × σ₂ × σ₃ × σ₄)) : List (List Nat) :=
  ts.flatMap fun (a, b) =>
    (idxOf u₁ a).flatMap fun i => (locate3 u₂ u₃ u₄ [b]).map (i :: ·)

end Sel

end Spytial
