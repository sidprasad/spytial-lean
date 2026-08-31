module

public import SpytialLean.Identity
public meta import SpytialLean.MetaEncode
meta import SpytialLean.InContext
meta import WalkCanon

open SpytialLean Lean Meta

namespace ContextInspectionTest

inductive Tree where
  | leaf
  | node (left : Tree) (key : Nat) (right : Tree)

def Tree.height : Tree → Nat
  | .leaf => 0
  | .node l _ r => 1 + max (height l) (height r)

private meta def tree : Expr := mkConst ``Tree

private meta def node (l : Expr) (key : Nat) (r : Expr) : Expr :=
  mkApp3 (mkConst ``Tree.node) l (mkRawNatLit key) r

private meta def height (t : Expr) : Expr := mkApp (mkConst ``Tree.height) t

private meta def view (root : Expr) (rootOnly := true) : MetaM ContextView := do
  let (status, result) ← wdykInContext root {} { rootOnly, mechanisms := #[.simp] } #[height root]
  if status.inconsistent || status.truncated then throwError "unexpected extraction status"
  let some result := result | throwError "missing context view"
  return result

private meta def tuples (data : JsonDataInstance) (name : String) : Array JsonTuple :=
  (data.relations.find? (·.name == name)).map (·.tuples) |>.getD #[]

private meta def assertCount (label : String) (data : JsonDataInstance)
    (relation : String) (count : Nat) : MetaM Unit := do
  unless (tuples data relation).size == count do
    throwError "{label}: expected {count} {relation} tuples\n{canonInstance data}"

private meta def assertTrees (label : String) (data : JsonDataInstance) (count : Nat) :
    MetaM Unit := do
  unless (data.atoms.filter (·.type == "Tree")).size == count do
    throwError "{label}: expected {count} tree atoms\n{canonInstance data}"

private meta def assertInspectionMetadata (view : ContextView) : MetaM Unit := do
  unless view.data.atoms.any (·.id == view.inspection.root) do
    throwError "inspected root is missing from the context-informed datum"
  unless view.inspection.facts.size == view.afaik.facts.size do
    throwError "inspection omitted a certified context fact"

/- The LR branch has facts about subtrees, not just the selected whole tree.
   Naming the child and then the root must leave the entire datum unchanged. -/
#eval show Lean.Elab.TermElabM Unit from do
  withLocalDeclD `ll tree fun ll => do
  withLocalDeclD `a tree fun a => do
  withLocalDeclD `b tree fun b => do
  withLocalDeclD `r tree fun r => do
  withLocalDeclD `unrelated tree fun unrelated => do
    let inner := node a 2 b
    let left := node ll 1 inner
    let root := node left 3 r
    let more ← mkAppM ``HAdd.hAdd #[height r, mkRawNatLit 1]
    withLocalDeclD `outer (← mkAppM ``LT.lt #[more, height left]) fun _ => do
    withLocalDeclD `inner (← mkAppM ``LT.lt #[height ll, height inner]) fun _ => do
    withLocalDeclD `noise (← mkAppM ``LT.lt #[height unrelated, mkRawNatLit 1]) fun _ => do
      let direct ← view root
      assertCount "inline LR" direct.data "lt" 2
      assertTrees "inline LR" direct.data 7
      if direct.data.atoms.any (·.label == "unrelated") then
        throwError "an incidental shared numeral pulled an unrelated tree into the view"
      withLetDecl `left tree left fun namedLeft => do
      withLetDecl `before tree (node namedLeft 3 r) fun before => do
        let named ← view before
        assertCanon "named LR" named.data (canonInstance direct.data)
        unless named.inspection.term == "before" do
          throwError "inspection lost the selected local name"
        unless named.afaik.facts.size == direct.afaik.facts.size do
          throwError "naming changed the retained facts"

/- A context occurrence of the left subtree, nested inside an observation,
   must use the atom already reached by the parent's left relation. -/
#eval show Lean.Elab.TermElabM Unit from do
  withLocalDeclD `ll tree fun ll => do
  withLocalDeclD `lr tree fun lr => do
  withLocalDeclD `r tree fun r => do
    let left := node ll 1 lr
    let root := node left 2 r
    withLocalDeclD `bound (← mkAppM ``LT.lt #[height r, height left]) fun _ => do
      let result ← view root false
      assertTrees "shared contextual subtree" result.data 5
      assertCount "one observation per subtree" result.data "height" 5
      let some rootAtom := result.data.atoms[0]? | throwError "missing root"
      let some edge := (tuples result.data "left").find? (·.atoms[0]? == some rootAtom.id)
        | throwError "missing root's left child"
      let some child := edge.atoms[1]? | throwError "missing child endpoint"
      let some observed := (tuples result.data "height").find? (·.atoms[0]? == some child)
        | throwError "left child has no height"
      let some bound := (tuples result.data "lt")[0]? | throwError "missing bound"
      unless bound.atoms[1]? == observed.atoms[1]? do
        throwError "bound refers to a different subtree's height"

/- The new root is not mentioned in the old inequalities. Unchanged subtrees
   still connect the result to those facts; the old parent is a distinct value. -/
#eval show Lean.Elab.TermElabM Unit from do
  withLocalDeclD `ll tree fun ll => do
  withLocalDeclD `a tree fun a => do
  withLocalDeclD `b tree fun b => do
  withLocalDeclD `r tree fun r => do
    let inner := node a 2 b
    let oldLeft := node ll 1 inner
    let after := node (node ll 1 a) 2 (node b 3 r)
    withLocalDeclD `outer (← mkAppM ``LT.lt #[height r, height oldLeft]) fun _ => do
    withLocalDeclD `inner (← mkAppM ``LT.lt #[height ll, height inner]) fun _ => do
      let result ← view after
      assertCount "after retains old bounds" result.data "lt" 2
      assertTrees "old and new parents stay distinct" result.data 9
      assertInspectionMetadata result

/- A refinement of the selected variable exposes children whose facts also
   belong to its view. No unrelated relation is admitted through the type. -/
#eval show Lean.Elab.TermElabM Unit from do
  withLocalDeclD `t tree fun t => do
  withLocalDeclD `l tree fun l => do
  withLocalDeclD `r tree fun r => do
  withLocalDeclD `shape (← mkAppM ``Eq #[t, node l 1 r]) fun _ => do
  withLocalDeclD `bound (← mkAppM ``LT.lt #[height l, height r]) fun _ => do
    let result ← view t
    assertTrees "refined subject" result.data 3
    assertCount "refined subject's child facts" result.data "lt" 1

/- The selected expression includes explicit function graphs even though their
   arguments are not reached by following edges forward from the result. -/
#eval show Lean.Elab.TermElabM Unit from do
  let nat := mkConst ``Nat
  withLocalDeclD `f (← mkArrow nat nat) fun f => do
  withLocalDeclD `x nat fun x => do
    let leaf := mkConst ``Tree.leaf
    let root := mkApp3 (mkConst ``Tree.node) leaf (mkApp f x) leaf
    let result ← view root
    assertInspectionMetadata result
    assertCount "explicit application belongs to the inspection" result.data "f" 1
    unless result.data.atoms.any (·.label == "x") do
      throwError "inspection lost the argument of its explicit application"

/- Relevant context witnesses belong to the same inspected datum and receive
   the requested observation. -/
#eval show Lean.Elab.TermElabM Unit from do
  withLocalDeclD `R (← mkArrow tree (← mkArrow tree (mkSort Level.zero))) fun R => do
  withLocalDeclD `l tree fun l => do
    let proposition ← withLocalDeclD `w tree fun w => do
      mkAppM ``Exists #[← mkLambdaFVars #[w] (mkApp2 R l w)]
    withLocalDeclD `h proposition fun _ => do
      let result ← view (node l 1 (mkConst ``Tree.leaf)) false
      assertInspectionMetadata result
      assertTrees "witness retained in inspection" result.data 4
      assertCount "witness also observed" result.data "height" 4

/- An existing fact's neighbor can bring another relevant fact into scope,
   regardless of declaration order. The third tree need not be in the root. -/
#eval show Lean.Elab.TermElabM Unit from do
  withLocalDeclD `l tree fun l => do
  withLocalDeclD `r tree fun r => do
  withLocalDeclD `neighbor tree fun neighbor => do
  withLocalDeclD `tail (← mkAppM ``LT.lt #[height neighbor, height r]) fun _ => do
  withLocalDeclD `head (← mkAppM ``LT.lt #[height l, height neighbor]) fun _ => do
    let result ← view (node l 1 r)
    assertCount "connected facts" result.data "lt" 2
    assertTrees "connected neighbor" result.data 4

/- Distinct unknowns are not equal just because their parents have the same
   constructor and key. Command-mode occurrence identity is unchanged too. -/
#eval show Lean.Elab.TermElabM Unit from do
  withLocalDeclD `a tree fun a => do
  withLocalDeclD `b tree fun b => do
  withLocalDeclD `r tree fun r => do
    let root := node (node a 1 r) 2 (node b 1 r)
    assertTrees "different symbolic trees" (← view root).data 6
    let repeated := node (node a 1 r) 2 (node a 1 r)
    assertTrees "ordinary walk stays occurrence-based" (← relationalize repeated) 5
    let cfg : WalkConfig := { shareSymbolicValues := true }
    let shared ← relationalize repeated cfg
    assertTrees "contextual walk shares references" shared 4
    let (_, reference) ← withoutModifyingEnv <| referenceRelationalize repeated cfg
    assertCanon "contextual fused/reference agreement" shared (canonInstance reference)
    let raw ← mkAppM ``Raw.mk #[repeated]
    assertTrees "Raw retains occurrence semantics" (← relationalize raw cfg) 5
    withLetDecl `child tree (node a 1 r) fun child => do
      let aliased := node child 2 (node a 1 r)
      assertCanon "symbolic alias shares its atom" (← relationalize aliased cfg)
        (canonInstance shared)

/- Unknowns are compared syntactically, never unified to make a view fit. -/
#eval show Lean.Elab.TermElabM Unit from do
  let a ← mkFreshExprMVar tree
  let b ← mkFreshExprMVar tree
  let root := node (node a 1 a) 2 (node b 1 b)
  let result ← relationalize root { shareSymbolicValues := true }
  assertTrees "distinct metavariables" result 5
  if (← a.mvarId!.isAssigned) || (← b.mvarId!.isAssigned) then
    throwError "contextual sharing assigned a metavariable"

/- Overloaded literal notation must be reduced through its actual instance. -/
#eval show Lean.Elab.TermElabM Unit from do
  let nat := mkConst ``Nat
  let unusual ← mkAppOptM ``OfNat.mk #[some nat, some (mkRawNatLit 1), some (mkRawNatLit 9)]
  let literal ← mkAppOptM ``OfNat.ofNat #[some nat, some (mkRawNatLit 1), some unusual]
  unless (← normalizeReferenceTerm literal).equal (mkRawNatLit 9) do
    throwError "reference normalization ignored the literal's instance"

section

local instance : SpytialIdentity Tree := .asWritten

#eval show Lean.Elab.TermElabM Unit from do
  withLocalDeclD `a tree fun a => do
  withLocalDeclD `r tree fun r => do
    let repeated := node (node a 1 r) 2 (node a 1 r)
    assertTrees "type-level asWritten" (← view repeated).data 5

end

section

local instance : SpytialIdentity Tree := ⟨.eqv (fun _ _ => false), none⟩

#eval show Lean.Elab.TermElabM Unit from do
  withLocalDeclD `a tree fun a => do
  withLocalDeclD `r tree fun r => do
    let repeated := node (node a 1 r) 2 (node a 1 r)
    assertTrees "non-reflexive identity decider" (← view repeated).data 5

end

/- Observing height requests its values, not its implementation's call graph.
   Unknown subtrees do not determine heights or an ordering between them. -/
#eval show Lean.Elab.TermElabM Unit from do
  withLocalDeclD `l tree fun l => do
  withLocalDeclD `r tree fun r => do
    let result ← view (node l 1 r)
    assertCount "symbolic heights" result.data "height" 3
    assertCount "no implicit maximum observation" result.data "max" 0
    assertCount "no implicit addition observation" result.data "add" 0
    assertCount "no invented ordering" result.data "le" 0

/- Facts about the children compute the parent's height before any context
   expression can allocate a separate unknown for it. -/
#eval show Lean.Elab.TermElabM Unit from do
  withLocalDeclD `l tree fun l => do
  withLocalDeclD `r tree fun r => do
    let root := node l 7 r
    withLocalDeclD `hl (← mkEq (height l) (mkRawNatLit 2)) fun _ => do
    withLocalDeclD `hr (← mkEq (height r) (mkRawNatLit 1)) fun _ => do
    withLocalDeclD `bound (← mkAppM ``LT.lt #[height root, mkRawNatLit 5]) fun _ => do
      let result ← view root
      assertCount "computed observations" result.data "height" 3
      let some observed := (tuples result.data "height").find?
          (·.atoms[0]? == result.data.atoms[0]?.map (·.id))
        | throwError "missing root observation"
      let some output := result.data.atoms.find? (some ·.id == observed.atoms[1]?)
        | throwError "missing height result"
      unless output.label == "3" do
        throwError "context-known child heights did not compute the parent: {output.label}"
      assertInspectionMetadata result
      let some bound := (tuples result.data "lt")[0]? | throwError "missing bound"
      unless bound.atoms[0]? == some output.id do
        throwError "branch condition uses a stale height result"

/- A scalar and its contextual relationships inhabit the same inspection. -/
#eval show Lean.Elab.TermElabM Unit from do
  withLocalDeclD `x (mkConst ``Nat) fun x => do
  withLocalDeclD `y (mkConst ``Nat) fun y => do
  withLocalDeclD `h (← mkAppM ``LT.lt #[x, y]) fun _ => do
    let (_, some result) ← wdykInContext x | throwError "missing scalar context"
    assertInspectionMetadata result
    assertCount "scalar retains comparison" result.data "lt" 1

/- Known symbolic heights remain shared values. Arithmetic used internally to
   calculate the parent does not become an additional observation. -/
#eval show Lean.Elab.TermElabM Unit from do
  withLocalDeclD `l tree fun l => do
  withLocalDeclD `r tree fun r => do
  withLocalDeclD `n (mkConst ``Nat) fun n => do
  withLocalDeclD `hl (← mkEq (height l) n) fun _ => do
  withLocalDeclD `hr (← mkEq (height r) (mkRawNatLit 0)) fun _ => do
    let result ← view (node l 7 r)
    assertCount "symbolic result does not expose addition" result.data "add" 0
    assertCount "maximum simplifies away" result.data "max" 0
    assertCount "no Nat implementation field" result.data "n" 0
    if result.data.atoms.any (·.label == "succ") then
      throwError "residual arithmetic unfolded to Nat.succ"
    let some scalar := result.data.atoms.find? (·.label == "n")
      | throwError "lost the known symbolic height"
    unless (tuples result.data "height").any (·.atoms[1]? == some scalar.id) do
      throwError "the child's observation does not use its known height"

/- An irrelevant unknown key does not prevent height evaluation. Command
   mode has the same reduction semantics, without importing context facts. -/
#eval show Lean.Elab.TermElabM Unit from do
  withLocalDeclD `key (mkConst ``Nat) fun key => do
    let leaf := mkConst ``Tree.leaf
    let root := mkApp3 (mkConst ``Tree.node) leaf key leaf
    let data ← relationalize root {} #[height root]
    assertCount "command observations" data "height" 2
    assertCount "fully computed height" data "add" 0
    let some observed := (tuples data "height").find?
        (·.atoms[0]? == data.atoms[0]?.map (·.id))
      | throwError "missing root height"
    unless data.atoms.any (fun atom => some atom.id == observed.atoms[1]? && atom.label == "1") do
      throwError "unknown key blocked a known height"

def Tree.children : Tree → Option (Tree × Tree)
  | .leaf => none
  | .node l _ r => some (l, r)

/- Partial observation results are not restricted to scalars. Constructors
   and their unknown fields belong to the same ordinary relational datum. -/
#eval show Lean.Elab.TermElabM Unit from do
  withLocalDeclD `l tree fun l => do
  withLocalDeclD `r tree fun r => do
    let root := node l 7 r
    let data ← relationalize root {} #[mkApp (mkConst ``Tree.children) root]
    assertCount "structured results" data "children" 3
    assertCount "pair first" data "fst" 1
    assertCount "pair second" data "snd" 1
    unless data.atoms.any (·.label == "some") do
      throwError "partially symbolic Option result was discarded"
    assertTrees "structured result reuses its children" data 3

def Tree.singleton (key : Nat) : Tree := .node .leaf key .leaf

def Tree.singletonAlias (key : Nat) : Tree := .singleton key

def Tree.heightAlias (t : Tree) : Nat := t.height

private meta def assertRootObservation (data : JsonDataInstance) (relation label : String) :
    MetaM Unit := do
  let some observed := (tuples data relation).find?
      (·.atoms[0]? == data.atoms[0]?.map (·.id))
    | throwError "missing root {relation}"
  unless data.atoms.any (fun a => some a.id == observed.atoms[1]? && a.label == label) do
    throwError "expected root {relation} = {label}\n{canonInstance data}"

/- Evaluation can discard unknown keys, and must follow ordinary helper
   definitions without requiring the user to mark those helpers as simp rules. -/
#eval show Lean.Elab.TermElabM Unit from do
  withLocalDeclD `key (mkConst ``Nat) fun key => do
    let leaf := mkConst ``Tree.leaf
    let single := mkApp (mkConst ``Tree.singletonAlias) key
    let root := node single 7 leaf
    let inlineRoot := node (mkApp3 (mkConst ``Tree.node) leaf key leaf) 7 leaf
    let data ← relationalize root {} #[height root]
    assertRootObservation data "height" "2"
    assertCount "every helper-built subtree observed" data "height" 3
    assertCanon "helpers and inline constructors agree" data
      (canonInstance (← relationalize inlineRoot {} #[height inlineRoot]))
    let alias ← relationalize root {} #[mkApp (mkConst ``Tree.heightAlias) root]
    assertRootObservation alias "heightAlias" "2"
    assertCount "observer alias does not request its helper" alias "height" 0
    withLocalDeclD `bound (← mkAppM ``LT.lt #[height single, mkRawNatLit 5]) fun _ => do
      let result ← view root
      assertRootObservation result.data "height" "2"
      assertCount "no stale helper observation" result.data "height" 3
      let some bound := (tuples result.data "lt")[0]? | throwError "missing bound"
      unless result.data.atoms.any
          (fun a => some a.id == bound.atoms[0]? && a.label == "1") do
        throwError "a fact's helper application did not use its computed height"

/- Partial evaluation still computes the known child, without drawing the
   addition/maximum used to calculate the unresolved parent's height. -/
#eval show Lean.Elab.TermElabM Unit from do
  withLocalDeclD `r tree fun r => do
    let root := node (mkApp (mkConst ``Tree.singleton) (mkRawNatLit 4)) 7 r
    let data ← relationalize root {} #[height root]
    assertCount "partially known tree heights" data "height" 4
    assertCount "no implementation addition" data "add" 0
    assertCount "no implementation maximum" data "max" 0
    let some child := (tuples data "left").find?
        (·.atoms[0]? == data.atoms[0]?.map (·.id)) | throwError "missing child"
    let some observed := (tuples data "height").find? (·.atoms[0]? == child.atoms[1]?)
      | throwError "missing child height"
    unless data.atoms.any (fun a => some a.id == observed.atoms[1]? && a.label == "1") do
      throwError "known child height was lost in a partial result"

def Tree.heightPair (t : Tree) : Nat × Nat := (t.height, t.height + 1)

/- Computation also works inside structured results, not just Nat outputs. -/
#eval show Lean.Elab.TermElabM Unit from do
  let root := node (mkApp (mkConst ``Tree.singleton) (mkRawNatLit 4)) 7 (mkConst ``Tree.leaf)
  let data ← relationalize root {} #[mkApp (mkConst ``Tree.heightPair) root]
  assertCount "structured computed observations" data "heightPair" 3
  assertCount "structured results do not request height" data "height" 0
  assertCount "structured results do not request addition" data "add" 0
  unless data.atoms.any (·.label == "3") do throwError "pair's arithmetic did not evaluate"

opaque unavailableHeight : Tree → Nat := Tree.height

/- An opaque body is not a license to fabricate a runtime default value. -/
#eval show Lean.Elab.TermElabM Unit from do
  let leaf := mkConst ``Tree.leaf
  let data ← relationalize leaf {} #[mkApp (mkConst ``unavailableHeight) leaf]
  assertCount "opaque observation" data "unavailableHeight" 1
  unless (data.atoms.filter (·.type == "Nat")).all (·.label.startsWith "?") do
    throwError "opaque observer was reported as a concrete number"

/- Prepared simplifications carry checked equalities and leave the caller's
   metavariables untouched. -/
#eval show Lean.Elab.TermElabM Unit from do
  withLocalDeclD `l tree fun l => do
  withLocalDeclD `r tree fun r => do
  withLocalDeclD `hl (← mkEq (height l) (mkRawNatLit 2)) fun hl => do
  withLocalDeclD `hr (← mkEq (height r) (mkRawNatLit 1)) fun hr => do
    let root := node l 7 r
    let application := height root
    let cfg ← prepareObservations { observations := #[application] } #[root, l, r] #[hl, hr]
    let some result := cfg.observationResults[(⟨application⟩ : ExprStructEq)]?
      | throwError "missing prepared observation"
    unless (← whnf result.expr).equal (mkRawNatLit 3) do
      throwError "preparation did not compute the result"
    let some proof := result.proof? | throwError "missing equality certificate"
    Iykyk.kernelCheckClaim (← getLCtx) (← mkEq application result.expr) proof
    assertMatchesReference "computed observation walkers agree" application cfg
    let hole ← mkFreshExprMVar tree
    let data ← relationalize (node hole 7 hole) {} #[height (node hole 7 hole)]
    assertCount "observing holes remains finite" data "height" 2
    if ← hole.mvarId!.isAssigned then throwError "observing assigned a metavariable"
    let key ← mkFreshExprMVar (mkConst ``Nat)
    let leaf := mkConst ``Tree.leaf
    let root := mkApp3 (mkConst ``Tree.node) leaf key leaf
    let data ← relationalize root {} #[height root]
    let some observed := (tuples data "height").find?
        (·.atoms[0]? == data.atoms[0]?.map (·.id))
      | throwError "missing height for a tree with a key hole"
    unless data.atoms.any (fun a => some a.id == observed.atoms[1]? && a.label == "1") do
      throwError "an irrelevant metavariable prevented evaluation"
    if ← key.mvarId!.isAssigned then throwError "observing filled the key hole"

def bump (n : Nat) : Nat := n + 1

/- The observer's own newly created outputs must not extend its domain. -/
#eval show Lean.Elab.TermElabM Unit from do
  let one := mkRawNatLit 1
  let data ← relationalize one {} #[mkApp (mkConst ``bump) one]
  assertCount "fixed observation domain" data "bump" 1
  unless data.atoms.size == 2 && data.atoms.any (·.label == "2") do
    throwError "observations recursed into newly computed values"

def Tree.rotateLeft : Tree → Tree
  | .node l key (.node a pivot b) => .node (.node l key a) pivot b
  | t => t

/- An observer's input remains an ordinary value: a rotation inside a parent
   must expose its tree structure, not become a residual Tree graph point. -/
#eval show Lean.Elab.TermElabM Unit from do
  withLocalDeclD `l tree fun l => do
  withLocalDeclD `a tree fun a => do
  withLocalDeclD `b tree fun b => do
  withLocalDeclD `r tree fun r => do
    let rotated := mkApp (mkConst ``Tree.rotateLeft) (node l 1 (node a 2 b))
    let result ← view (node rotated 3 r)
    assertTrees "rotation remains structural" result.data 7
    assertCount "rotation is not an opaque application" result.data "rotateLeft" 0
    assertCount "all rotated nodes are observed" result.data "height" 7
    unless (result.data.atoms.filter (fun a => a.type == "Tree" && a.label == "node")).size == 3 do
      throwError "observing hid a rotated tree's structure"
    let root := node rotated 3 r
    let paired ← relationalize root {} #[mkApp (mkConst ``Tree.heightPair) root]
    assertTrees "input helpers remain structural for other observers" paired 7
    assertCount "every input gets a structured observation" paired "heightPair" 7
    assertCount "partial structured results do not request height" paired "height" 0
    assertCount "partial structured results do not request addition" paired "add" 0

end ContextInspectionTest
