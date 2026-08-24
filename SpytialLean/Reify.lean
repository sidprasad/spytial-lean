module

public import Lean
public import Lean.Elab.Command
public meta import SpytialLean.Types
public meta import SpytialLean.TypeShape
public meta import SpytialLean.Relationalizer

namespace SpytialLean

open Lean Meta Elab

/-! # Reifying a value from its datum

The executable side of the fidelity story (the abstract version is the
`fidelity` theorem in `SpytialLean.Fidelity`): a program that sees only the
`JsonDataInstance` — never the original expression — rebuilds the value, and
the host's own `Repr` then prints it. `#spytial.fidelity v` compares the two
paths the multilanguage commitment names:

    v ─ reprStr ────────────────────────────→ string
    v ─ relationalize ─ reifyDatum ─ reprStr → string

The datum may contain *more* than the printout (sharing, identity, `Nat.zero`
spelled as a constructor); reconstruction reads it back out. What it cannot
contain less of is the constructor structure, and that is what this checks.

The reconstructor is type-vocabulary-aware and value-blind, like `Repr`
itself: it consults the environment for constructor signatures (the same
`fieldRelName` the walker used, so the two agree by construction), but every
fact about the *value* comes from the datum. Erased fields are refilled at
their type: proofs by `decide`, and a type parameter no value pinned down is
defaulted — it cannot reach the printout, since derived `Repr` output mentions
only constructors and data. -/

/-- A datum indexed for reconstruction: atoms by id, the child at each
    `(relation, parent)`, and the root — the unique atom no tuple points at. -/
meta structure DatumIndex where
  atoms : Std.HashMap String JsonAtom
  children : Std.HashMap (String × String) (Array String)
  root : String

private meta def buildIndex (di : JsonDataInstance) : TermElabM DatumIndex := do
  let mut atoms : Std.HashMap String JsonAtom := {}
  for a in di.atoms do
    atoms := atoms.insert a.id a
  let mut children : Std.HashMap (String × String) (Array String) := {}
  let mut nonRoot : Std.HashSet String := {}
  for rel in di.relations do
    for t in rel.tuples do
      for i in [1:t.atoms.size] do
        nonRoot := nonRoot.insert t.atoms[i]!
      -- field edges are binary; `maps`/`scrutinee` tuples still mark non-roots
      if t.atoms.size == 2 then
        let key := (rel.name, t.atoms[0]!)
        let cs := children.getD key #[]
        unless cs.contains t.atoms[1]! do
          children := children.insert key (cs.push t.atoms[1]!)
  let roots := di.atoms.filterMap fun a =>
    if nonRoot.contains a.id then none else some a.id
  match roots with
  | #[r] => return { atoms, children, root := r }
  | _ => throwError "reify: expected exactly one root atom, found {roots}"

/-- Resolve the constructor a `(type, label)` atom names. The datum records
    only the short head name (`sigOfType`), so resolution at the command site
    is tried first; a type not in scope there falls back to the unique
    non-private environment inductive with that short name carrying a
    constructor matching the label — more than one is genuine ambiguity the
    datum cannot settle. -/
private meta def resolveAtomCtor (tyShort ctorLabel : String) : TermElabM Name := do
  let matching (iv : InductiveVal) : Option Name :=
    iv.ctors.find? (fun c => shortName c == ctorLabel)
  let fromScope? ← try
      some <$> resolveGlobalConstNoOverload (mkIdent (Name.mkSimple tyShort))
    catch _ => pure none
  if let some n := fromScope? then
    if let some (.inductInfo iv) := (← getEnv).find? n then
      if let some c := matching iv then return c
  let cands := (← getEnv).constants.fold (init := #[]) fun acc n ci =>
    match ci with
    | .inductInfo iv =>
      if shortName n == tyShort && !isPrivateName n then
        match matching iv with
        | some c => acc.push c
        | none => acc
      else acc
    | _ => acc
  match cands with
  | #[c] => return c
  | #[] => throwError "reify: no inductive `{tyShort}` has a constructor `{ctorLabel}`"
  | _ => throwError "reify: atom `{tyShort}|{ctorLabel}` is ambiguous between {cands}"

/-- Rebuild the term drawn at atom `id` as surface syntax. Literal leaves keep
    their printed form in the label; a constructor atom resolves its inductive
    from the type head and its constructor from the label, then recovers each
    field through the same relation name the walker emitted for it. -/
private meta partial def reifyTerm (idx : DatumIndex) (id : String) : TermElabM Term := do
  let some atom := idx.atoms[id]? | throwError "reify: unknown atom id {id}"
  if atom.type == "Nat" && atom.label.toNat?.isSome then
    let n : Term := Syntax.mkNumLit atom.label
    return ← `(($n : Nat))
  if atom.type == "String" && atom.label.startsWith "\"" then
    -- the label is `"` ++ contents ++ `"`, contents unescaped
    let s : Term := Syntax.mkStrLit ((atom.label.drop 1).dropEnd 1).copy
    return ← `(($s : String))
  let ctorName ← resolveAtomCtor atom.type atom.label
  let ci ← getConstInfoCtor ctorName
  let binderNames := ctorDataBinderNames ci
  let ctorShort := shortName ctorName
  forallTelescopeReducing ci.type fun xs _ => do
    let mut args : Array Term := #[]
    for i in [ci.numParams : xs.size] do
      let x := xs[i]!
      let decl ← x.fvarId!.getDecl
      unless decl.binderInfo.isExplicit do
        if (idx.children[(fieldRelName ctorShort binderNames (i - ci.numParams), id)]?).isSome then
          throwError "reify: implicit data field of {ctorName} is unsupported"
        continue
      let fieldTy ← inferType x
      if ← isProofLikeType fieldTy then
        -- erased at the walk: resynthesize a proof, leave a type to inference
        args := args.push (← if ← Meta.isProp fieldTy then `(by decide) else `(_))
        continue
      let relName := fieldRelName ctorShort binderNames (i - ci.numParams)
      match idx.children[(relName, id)]? with
      | some #[childId] => args := args.push (← reifyTerm idx childId)
      | some cs =>
        throwError "reify: relation {relName} holds {cs.size} children of atom {id} — colliding field names"
      | none =>
        throwError "reify: field {relName} of {ctorName} missing from the datum"
    return Syntax.mkApp (mkCIdent ctorName) args

/-- Rebuild, from the datum alone, surface syntax for the value it draws. -/
public meta def reifyDatumSyntax (di : JsonDataInstance) : TermElabM Term := do
  let idx ← buildIndex di
  reifyTerm idx idx.root

/-- Elaborate reconstructed syntax into a value. The expected type is not part
    of the datum; it parameterizes the *statement* a caller wants to place the
    value in (see `checkFidelity`), never the reconstruction itself. -/
private meta def elabReified (stx : Term) (expectedType? : Option Expr) : TermElabM Expr := do
  -- errors must throw, not log-and-sorry: a failed `decide` on an erased proof
  -- is a reconstruction failure, and callers assert on it
  let e ← Term.withoutErrToSorry do
    let e ← match expectedType? with
      | some ty => Term.elabTermEnsuringType stx ty
      | none => Term.elabTerm stx none
    Term.synthesizeSyntheticMVarsNoPostponing
    instantiateMVars e
  -- a type parameter no value pinned down cannot reach the printout; default it
  for mvarId in ← getMVars e do
    let ty ← instantiateMVars (← mvarId.getType)
    if ty.isSort then
      discard <| isDefEq (mkMVar mvarId) (mkConst ``Nat)
  let e ← instantiateMVars e
  if e.hasSorry then
    throwError "reify: reconstruction contains sorry"
  if e.hasMVar then
    -- e.g. an index the datum does not record (`Fin ?n`)
    throwError "reify: reconstruction leaves metavariables: {e}"
  return e

/-- Rebuild the value a datum draws, from the datum alone. -/
public meta def reifyDatum (di : JsonDataInstance) : TermElabM Expr := do
  elabReified (← reifyDatumSyntax di) none

private meta unsafe def evalStringUnsafe (e : Expr) : MetaM String :=
  Meta.evalExpr String (mkConst ``String) e

@[implemented_by evalStringUnsafe]
private meta opaque evalStringOpaque (e : Expr) : MetaM String

/-- The host's inspection string for a value: evaluated `reprStr`. -/
public meta def reprStrOfValue (e : Expr) : MetaM String := do
  evalStringOpaque (← mkAppM ``reprStr #[e])

/-- Compare the two paths for an elaborated value, and kernel-certify the
    result: beyond the strings agreeing, the kernel must accept
    `rfl : e = reconstructed` — so every passing check is a machine-checked
    instance of fidelity for that value, not a string coincidence. Returns the
    shared string. -/
public meta def checkFidelity (e : Expr) : TermElabM String := do
  let di ← relationalize e
  let direct ← reprStrOfValue e
  let stx ← reifyDatumSyntax di
  -- the commitment's check: the string, reconstructed from the datum alone
  let reconStr ← reprStrOfValue (← elabReified stx none)
  unless direct == reconStr do
    throwError "fidelity failure:\n  direct:        {direct}\n  reconstructed: {reconStr}"
  -- the certificate: the same datum-only syntax, placed at the original type
  -- (the datum records no type parameters, so stating value equality needs
  -- the type from outside; the reconstruction itself never saw it)
  let recon ← elabReified stx (some (← inferType e))
  match Kernel.isDefEq (← getEnv) {} e recon with
  | .ok true => pure ()
  | .ok false =>
    throwError "fidelity failure: strings agree but the kernel refutes {e} ≡ {recon}"
  | .error ex => throwKernelException ex
  return direct

/-- `#spytial.fidelity <term>` checks that the value's inspection string is
    reconstructible from its datum alone: it prints `reprStr` of the value the
    datum reifies to, and errors if that differs from `reprStr` of the value
    itself. -/
syntax (name := spytialFidelity) "#spytial.fidelity " term : command

@[command_elab spytialFidelity]
public meta def elabSpytialFidelity : Command.CommandElab := fun
  | `(#spytial.fidelity $t:term) => do
    Command.liftTermElabM do
      let e ← Term.elabTerm t none
      Term.synthesizeSyntheticMVarsNoPostponing
      logInfo m!"{← checkFidelity (← instantiateMVars e)}"
  | stx => throwError "Unexpected syntax {stx}."

end SpytialLean
