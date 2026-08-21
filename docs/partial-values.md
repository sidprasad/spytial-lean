# Values under partial knowledge

> **The diagram is a faithful visualization of the user's current knowledge
> of a value — not a visualization of the proof state.**

This one sentence separates spytial from proof-state visualization work.

Proof-state visualization asks: *what is Lean asking me to prove, and what
assumptions are in scope?* Spytial asks: *given everything Lean currently
knows, what can I say about the thing I am looking at?* Those are different
objects. Given

```
x  : Tree α
h₁ : root x = a
h₂ : height x = 3
⊢ Balanced x
```

a proof-state visualizer draws the context and the goal as lists. Spytial
instead asks "what is `x`?" and draws the best tree it can justify. The
hypotheses disappear into the representation: they are not the thing shown,
they are the evidence used to produce the best possible diagram.

## The formal object

The underlying object is not the proof state `Γ`. It is the
knowledge-refined denotation of a term:

```
⟦t⟧_Γ
```

where `t` is the value being visualized, `Γ` is the local context, and the
result is the structure consistent with what is known. Three layers:

1. **The value** — `t : Tree`. The thing the user cares about.
2. **The knowledge context** — `Γ = {h₁, h₂, …}`. Not shown directly; used
   to refine understanding.
3. **The visualization** — `diagram(t | Γ)`. A faithful representation of
   the value under current knowledge.

Positive knowledge is what aspects of the value we can determine. Negative
knowledge is what aspects are impossible given what we know. Both are about
the value, never about the proof state.

## What faithfulness dictates

Every rule in `SpytialLean/InContext.lean` derives from the sentence:

- **The goal is never drawn.** The goal is what is still being proven — it
  is the proof state's business, not knowledge of the value.
- **Hypotheses are evidence, not content.** An equation or `let` *shapes*
  the value (refinement); a ground fact becomes an arrow anchored on the
  value's atoms; a hypothesis not about the subject is ignored.
- **`∧` splits; `∨` and `∀` do not.** Every part of a true conjunction is
  knowledge. A disjunction leaves *which* side unknown, and a universal is a
  rule rather than one fact — drawing either would be a guess, and a
  faithful diagram never guesses. They are counted and reported.
- **Negative facts draw only between values already in the world.** Ruling
  a term out is not license to materialize it.
- **The library never styles.** Semantics live in the data (relation names
  like `≠`, `¬R`); appearance belongs to the spec author.

## The ladder

Kinds of knowledge about a value, in order of increasing machinery:

1. **Whole-value knowledge** — `x = t`, `let x := t`, elaborator-assigned
   metavariables. Refines the subject's own structure. *(done)*
2. **Ground facts** — `R x y`, `x ≠ y`, conjunctions thereof. Arrows on the
   subject's atoms. *(done)*
3. **Part-of-value knowledge** — `root x = a`, `height x = 3`: knowledge
   addressing the *inside* of the value. Today these draw as honest `=`
   arrows against the stuck term; absorbing them into the subject's drawn
   structure needs projection inversion. *(future)*
4. **Derived knowledge** — universals applied to the finite picture:
   `hsymm : ∀ a b, R a b → R b a` plus a drawn `R x y` *proves* `R y x`.
   Saturate the diagram under the context's rules, by proof. *(future)*
5. **Possibility knowledge** — what the value *can* be: bounded enumeration
   filtered by decidable hypotheses, drawing a witness. *(staged on the
   `model-finding` branch)*

Rungs 1–2 are the simplest faithful start and are this library's surface
today. Rungs 3–5 are compute: they *use* knowledge the diagram cannot state
as an arrow. Keeping them separate keeps spytial a diagramming tool — and
keeps it out of the trap of becoming a generic theorem-prover UI.
