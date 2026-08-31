module

/-! # The Lean selector contract

A selector is a plain Lean function in one of two forms: a predicate over
walked values (`σ → Bool`, curried up to arity 4), keeping the tuples it
accepts, or a `Sel T α`, called on the value being drawn.

Selection is by value, so a type declared `SpytialIdentity.asWritten` keeps one
atom per occurrence and a value then selects all of its occurrences. Spytial
runs a selector at elaboration time, so a function it calls from another module
must be reachable by `meta import`. -/

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

/-- No equality needed anywhere below: a predicate returns no value, so nothing
    has to be located. -/
public def selIdx1 {σ : Type u} (u : Array σ) (p : σ → Bool) : List (List Nat) :=
  (List.range u.size).filterMap fun i =>
    u[i]?.bind fun v => if p v then some [i] else none

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

/-- The other half: every column of a `Sel` result is a returned value, and a
    returned value is located by `==`. -/
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
