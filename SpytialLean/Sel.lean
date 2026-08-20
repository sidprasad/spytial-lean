module

/-! # The Lean selector contract

A layout op needs a selector: a set of tuples of diagram atoms. This file
defines what a selector *is* when written in Lean, as ordinary Lean code that
users can read and call.

The contract is one sentence: **a selector is a function that Spytial calls on
the value being drawn, at resolution time; it returns the selected tuples of
values.**

```
Sel T α := T → Tuples α
```

Two rules complete it:

* **Selection is by value.** A returned value selects every atom holding an
  equal value (equality is the type's `BEq`; with a derived instance that is
  structural equality). Atoms holding equal values cannot be told apart. When
  the *position* matters, use the relational selector language instead.
* **`Tuples` is read as a set.** Order and duplicates are ignored; Spytial
  deduplicates and sorts the result before it reaches the diagram.

The shorthand forms — a bare predicate `σ → Bool`, a function `σ → τ`, a
function `σ → List τ` — mean exactly what the combinators below say they mean.
The only primitive connecting a selector to the diagram is `walked`: the values
the relationalizer visited. Spytial substitutes the real walked values for each
`walked` call when it resolves the selector; nothing here can run on its own.

Because a selector runs at elaboration time, a function it calls from another
module must be imported with `meta import` (Lean reports this itself when it is
missing). Definitions in the same file need nothing.
-/

namespace Spytial

/-- A list read as a set: order and duplicates are ignored. -/
public abbrev Tuples (α : Type u) := List α

/-- A Lean selector for values of type `T`, selecting tuples of type `α`.
    `α` is one column (`Sel T RBNode`) or a product (`Sel T (RBNode × RBNode)`);
    its product structure is the selector's arity. Spytial calls the function
    on the value being drawn, at resolution time. -/
public abbrev Sel (T : Type u) (α : Type v) : Type (max u v) := T → Tuples α

/-- The values of type `σ` that Spytial walked from the datum. This is the one
    primitive a selector has beyond plain Lean: Spytial replaces each call with
    the actual walked values when it resolves the selector. The body below is
    marked `noncomputable` because it cannot run on its own — which also makes
    a call Spytial failed to see a loud compile error, never a silent empty
    selection. A definition of your own that calls `walked` must carry the
    same `noncomputable` marker, and `@[expose]` if other modules use it. -/
public noncomputable def walked {T : Type u} {σ : Type v} (_ : T) : List σ := []

namespace Sel

/-- The selector "every walked `σ` where `p` holds". This is what a bare
    predicate `lean (p)` means. -/
@[expose] public noncomputable def ofPred {T : Type u} {σ : Type v} (p : σ → Bool) : Sel T σ :=
  fun t => (walked t).filter p

/-- The selector "every walked `σ`, paired with what `f` returns for it".
    This is what a bare function `lean (f)` means. -/
@[expose] public noncomputable def ofFn {T : Type u} {σ τ : Type v} (f : σ → τ) : Sel T (σ × τ) :=
  fun t => (walked t).map fun x => (x, f x)

/-- Like `ofFn` for a function returning several values: one tuple per
    element. This is what `lean (f)` means for `f : σ → List τ`. -/
@[expose] public noncomputable def ofMany {T : Type u} {σ τ : Type v} (f : σ → List τ) : Sel T (σ × τ) :=
  fun t => (walked t).flatMap fun x => (f x).map (x, ·)

/-- Selectors form a union algebra; `Tuples` is a set, so `++` is `∪`. -/
public instance instUnion {T : Type u} {α : Type v} : Union (Sel T α) :=
  ⟨fun s r t => s t ++ r t⟩

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

/-- A computed column: the returned value is located by `==` — the "returning
    a value needs equality" half of the contract. -/
public def selFn1 {σ τ : Type u} [BEq τ] (u : Array σ) (uτ : Array τ)
    (f : σ → τ) : List (List Nat) :=
  (List.range u.size).flatMap fun i =>
    match u[i]? with
    | some v => (idxOf uτ (f v)).map fun j => [i, j]
    | none => []

public def selFn2 {σ₁ σ₂ τ : Type u} [BEq τ] (u₁ : Array σ₁) (u₂ : Array σ₂)
    (uτ : Array τ) (f : σ₁ → σ₂ → τ) : List (List Nat) :=
  (List.range u₁.size).flatMap fun i =>
    (List.range u₂.size).flatMap fun j =>
      match u₁[i]?, u₂[j]? with
      | some a, some b => (idxOf uτ (f a b)).map fun k => [i, j, k]
      | _, _ => []

public def selMany1 {σ τ : Type u} [BEq τ] (u : Array σ) (uτ : Array τ)
    (f : σ → List τ) : List (List Nat) :=
  (List.range u.size).flatMap fun i =>
    match u[i]? with
    | some v => (f v).flatMap fun y => (idxOf uτ y).map fun j => [i, j]
    | none => []

public def selMany2 {σ₁ σ₂ τ : Type u} [BEq τ] (u₁ : Array σ₁) (u₂ : Array σ₂)
    (uτ : Array τ) (f : σ₁ → σ₂ → List τ) : List (List Nat) :=
  (List.range u₁.size).flatMap fun i =>
    (List.range u₂.size).flatMap fun j =>
      match u₁[i]?, u₂[j]? with
      | some a, some b =>
        (f a b).flatMap fun y => (idxOf uτ y).map fun k => [i, j, k]
      | _, _ => []

/-- A canonical `Sel`'s result: each returned value is located by `==` in its
    column. Every column needs `BEq`, because every column is a returned value. -/
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

/-- `Array`- and `Option`-returning functions, as their `List` forms. -/
public def listOfArray {σ τ : Type u} (f : σ → Array τ) : σ → List τ :=
  fun x => (f x).toList

public def listOfOption {σ τ : Type u} (f : σ → Option τ) : σ → List τ :=
  fun x => (f x).toList

end Sel

end Spytial
