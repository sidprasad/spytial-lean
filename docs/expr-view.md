# Drawing a `Lean.Expr`

`#spytial (e : Expr)` draws the term as syntax. `spytial.goal` draws the current goal in a tactic proof. A `Lean.Name` draws as one leaf labeled with its literal.

The view shows:

- an application as one `App` atom with an `fn` edge and an `args[i]` edge per explicit argument, in source order
- an implicit or instance argument as a gray `Implicit` stub, labeled with its head
- a binder (`fun`, `∀`, `let`, `→`) as a `Binder` atom with `type`, `body`, and `value` edges
- a bound variable as a `Var` atom with a dotted `binder` edge back to its binder
- a loose de Bruijn index as a red `Loose` atom
- a metavariable as a yellow `MVar` atom, marked `(assigned)` when it has an assignment
- `mdata` as an `MData` atom around its `inner` term

`set_option spytial.expr.full true` draws every argument at its position, implicit ones included, and adds the de Bruijn index to each variable.

## The shape

The view is a custom relationalizer that declares what it emits:

```lean
spytial_relationalizer Lean.Expr exprView emits ExprShape
```

`ExprShape` is an inductive that is never instantiated. Each constructor is an atom type and each field is a relation. A spec over `Expr` checks against this vocabulary, so `atomStyle Bindr …` is an error that suggests `Binder`. The attached spec in `SpytialLean/ExprView.lean` is written against it.

A relationalizer with no `emits` keeps the previous behaviour: the scope is open past it, and unknown names in a spec are warnings.

## Entry points

`exprViewProps (e : Expr) : MetaM Json` returns the widget props for `e`: the datum and the attached spec filtered to the types and relations the datum contains. Build the props in the same `MetavarContext` as the meta program that made `e`; a second lift gets a fresh context and reads every metavariable as unassigned.
