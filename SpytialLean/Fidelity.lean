module

/-!
# Fidelity: reifying a value from its relationalization

The walker turns a value into atoms and field relations, merging subterms that
share a declared identity (`SpytialLean.Identity`). This file asks what it takes
for that to lose nothing, and proves it:

    reifyRoot (relationalize key d) d.depth = some d

`reify` here is a specification device pinning down what "the diagram is the
value" means: a reader who sees only atoms and field relations can rebuild `d`
exactly. The executable counterpart is `SpytialLean.Reify`, which rebuilds a
value from the real walker's `JsonDataInstance` and is differentially tested
against `reprStr` in `tests/FidelityTest.lean`.

## What is modelled

The real walker is `Expr → MetaM JsonDataInstance`. This is a value-level model
of the constructor case of `emitNode`: a node draws an atom labelled with its
constructor, and each data field becomes one tuple in the relation named for
that field. Two things in that case can lose information, and both are kept:

* the **merge** — subterms of equal identity become one atom, so a coarse
  identity can collapse values the reader then cannot tell apart;
* **recovery by relation name** — a child is found by its field's relation
  name, so two fields sharing a name collapse into one relation.

`Faithful` and `Fields.Distinct` are exactly the hypotheses that rule those out,
and §8 shows neither can be dropped.

## What is not modelled, and why

Every other departure of the walker from the term is lossy *on purpose*, so no
theorem of this shape covers it: `whnf` (draws the value, not the spelling),
proof filtering (drops `Prop` fields), opaque leaves (a stuck application draws
as a pretty-printed label), function tabulation (draws the graph, so a function
returns only up to `funext`, and not at all past `maxTableTuples`), and the
unfold guard (cuts a self-similar unfolding with a cycle edge). Read this as
fidelity for the constructor fragment.
-/

namespace SpytialLean.Fidelity

/-! ## 1. Values -/

mutual
/-- A fully known value: a constructor node with named fields. -/
public inductive Datum where
  | node (type ctor : String) (fields : Fields)
/-- A node's fields: relation name paired with child value. Spelled out rather
    than `List (String × Datum)` so every walk below is structural. -/
public inductive Fields where
  | nil
  | cons (name : String) (val : Datum) (rest : Fields)
end

deriving instance DecidableEq for Datum, Fields
deriving instance Repr for Datum, Fields

public def Fields.names : Fields → List String
  | .nil => []
  | .cons n _ r => n :: r.names

public def Fields.vals : Fields → List Datum
  | .nil => []
  | .cons _ v r => v :: r.vals

/-- Recover a field by relation name — the only handle `reify` has on a child. -/
public def Fields.find? : Fields → String → Option Datum
  | .nil, _ => none
  | .cons n v r, f => if n = f then some v else r.find? f

mutual
public def Datum.depth : Datum → Nat
  | .node _ _ fs => fs.depth + 1
public def Fields.depth : Fields → Nat
  | .nil => 0
  | .cons _ v r => max v.depth r.depth
end

mutual
/-- Every subterm, root first: the order the walker visits them. -/
public def Datum.subterms : Datum → List Datum
  | .node t c fs => .node t c fs :: fs.subterms
public def Fields.subterms : Fields → List Datum
  | .nil => []
  | .cons _ v r => v.subterms ++ r.subterms
end

public def Datum.kids : Datum → List Datum
  | .node _ _ fs => fs.vals

/-! ## 2. The relational instance -/

/-- What the walker writes at a node: type, constructor label, and the field
    relations leaving it. In the walker those names come from the constructor's
    signature (`fieldRelName`), so the label determines them; here the atom
    carries them. -/
public structure Atom where
  type   : String
  ctor   : String
  fields : List String
  deriving DecidableEq, Repr

public def Datum.atom : Datum → Atom
  | .node t c fs => ⟨t, c, fs.names⟩

public def Datum.child : Datum → String → Option Datum
  | .node _ _ fs, f => fs.find? f

/-- Atoms carrying a label, plus one binary relation per field name — the
    widget's data instance, with atom ids drawn from `Key`. -/
public structure Inst (Key : Type) where
  atom  : Key → Option Atom
  child : Key → String → Option Key
  root  : Key

variable {Key : Type}

/-! ## 3. relationalize -/

/-- The subterm drawn at atom `i`: the first occurrence in the walk, matching
    the fused walker's choice of representative. -/
public def rep [BEq Key] (key : Datum → Key) (d : Datum) (i : Key) : Option Datum :=
  d.subterms.find? (fun s => key s == i)

/-- Walk `d` into atoms and field relations, merging subterms of equal identity. -/
public def relationalize [BEq Key] (key : Datum → Key) (d : Datum) : Inst Key where
  atom  := fun i => (rep key d i).map Datum.atom
  child := fun i f => (rep key d i).bind fun s => (s.child f).map key
  root  := key d

/-! ## 4. reify -/

/-- Read one node's field relations back into a field list. `childOf` is the
    node's outgoing edges and `rec` reifies a child atom. -/
public def reifyFields (childOf : String → Option Key) (rec : Key → Option Datum) :
    List String → Option Fields
  | [] => some .nil
  | f :: fs =>
    match childOf f with
    | none => none
    | some c =>
      match rec c with
      | none => none
      | some v => (reifyFields childOf rec fs).map (Fields.cons f v)

/-- Rebuild the value drawn at atom `i`: the atom gives the node and its field
    vocabulary, the field relations give the children. `fuel` bounds the
    unfolding, since an arbitrary instance may be cyclic. -/
public def reify (inst : Inst Key) : Nat → Key → Option Datum
  | 0 => fun _ => none
  | n + 1 => fun i =>
    match inst.atom i with
    | none => none
    | some a =>
      (reifyFields (inst.child i) (reify inst n) a.fields).map
        (Datum.node a.type a.ctor)

/-- Rebuild the whole value an instance draws, starting at its root. -/
public def reifyRoot (inst : Inst Key) (fuel : Nat) : Option Datum :=
  reify inst fuel inst.root

/-! ## 5. When merging is lossless -/

/-- What the atom at a subterm has to determine: the node drawn there, and the
    target of every field edge leaving it. -/
public def Datum.skel (key : Datum → Key) (d : Datum) : Atom × (String → Option Key) :=
  (d.atom, fun f => (d.child f).map key)

/-- `key` is *faithful* on `d` when every merge it performs inside `d` merges
    subterms of equal skeleton. Structural identity is faithful everywhere; a
    coarser one need not be. -/
public def Faithful (key : Datum → Key) (d : Datum) : Prop :=
  ∀ s ∈ d.subterms, ∀ s' ∈ d.subterms, key s = key s' → s.skel key = s'.skel key

/-- No node names two fields alike. Two same-named fields become one relation
    and the second child is unreachable. -/
public def Fields.Distinct : Fields → Prop
  | .nil => True
  | .cons n _ r => r.find? n = none ∧ r.Distinct

public def Datum.Distinct : Datum → Prop
  | .node _ _ fs => fs.Distinct

/-! ## 6. Supporting lemmas -/

public theorem Fields.depth_of_mem_vals {v : Datum} :
    ∀ {fs : Fields}, v ∈ fs.vals → v.depth ≤ fs.depth
  | .cons _ v' r, h => by
    simp only [Fields.vals, List.mem_cons] at h
    simp only [Fields.depth]
    rcases h with h | h
    · exact h ▸ Nat.le_max_left _ _
    · exact Nat.le_trans (depth_of_mem_vals h) (Nat.le_max_right _ _)

public theorem Datum.mem_subterms_self (d : Datum) : d ∈ d.subterms := by
  cases d; simp [Datum.subterms]

public theorem Fields.vals_subset_subterms {v : Datum} :
    ∀ {fs : Fields}, v ∈ fs.vals → v ∈ fs.subterms
  | .cons _ v' r, h => by
    simp only [Fields.vals, List.mem_cons] at h
    simp only [Fields.subterms, List.mem_append]
    rcases h with h | h
    · exact Or.inl (h ▸ v'.mem_subterms_self)
    · exact Or.inr (vals_subset_subterms h)

mutual
/-- `subterms` is closed under taking children. -/
public theorem Datum.subterms_closed :
    ∀ (d s : Datum), s ∈ d.subterms → ∀ v ∈ s.kids, v ∈ d.subterms
  | .node t c fs, s, hs, v, hv => by
    simp only [Datum.subterms, List.mem_cons] at hs
    simp only [Datum.subterms, List.mem_cons]
    rcases hs with rfl | hs
    · exact Or.inr (Fields.vals_subset_subterms (by simpa [Datum.kids] using hv))
    · exact Or.inr (Fields.subterms_closed fs s hs v hv)
public theorem Fields.subterms_closed :
    ∀ (fs : Fields) (s : Datum), s ∈ fs.subterms → ∀ v ∈ s.kids, v ∈ fs.subterms
  | .nil, s, hs, _, _ => by simp [Fields.subterms] at hs
  | .cons _ v' r, s, hs, v, hv => by
    simp only [Fields.subterms, List.mem_append] at hs ⊢
    rcases hs with hs | hs
    · exact Or.inl (Datum.subterms_closed v' s hs v hv)
    · exact Or.inr (Fields.subterms_closed r s hs v hv)
end

/-- The atom `key s` is drawn by *some* subterm carrying that identity. -/
public theorem rep_eq_some [BEq Key] [LawfulBEq Key] (key : Datum → Key) {d s : Datum}
    (hs : s ∈ d.subterms) :
    ∃ s₀, rep key d (key s) = some s₀ ∧ s₀ ∈ d.subterms ∧ key s₀ = key s := by
  cases h : rep key d (key s) with
  | none => exact absurd (List.find?_eq_none.mp h s hs) (by simp)
  | some s₀ =>
    refine ⟨s₀, rfl, List.mem_of_find?_eq_some h, ?_⟩
    simpa using List.find?_some h

/-! ## 7. Fidelity -/

/-- Reading a node's field relations back rebuilds its field list exactly. -/
public theorem reifyFields_eq (key : Datum → Key) (childOf : String → Option Key)
    (rec : Key → Option Datum) :
    ∀ (fs : Fields), fs.Distinct →
      (∀ f v, fs.find? f = some v → childOf f = some (key v)) →
      (∀ v ∈ fs.vals, rec (key v) = some v) →
      reifyFields childOf rec fs.names = some fs
  | .nil, _, _, _ => by simp [Fields.names, reifyFields]
  | .cons f v r, hdist, hchild, hIH => by
    have hcf : childOf f = some (key v) := hchild f v (by simp [Fields.find?])
    have hrv : rec (key v) = some v := hIH v (by simp [Fields.vals])
    have hrest : reifyFields childOf rec r.names = some r := by
      refine reifyFields_eq key childOf rec r hdist.2 ?_ ?_
      · intro f' v' hf'
        refine hchild f' v' ?_
        have hne : f ≠ f' := by
          rintro rfl; rw [hdist.1] at hf'; exact absurd hf' (by simp)
        simpa [Fields.find?, hne] using hf'
      · intro v' hv'; exact hIH v' (by simp [Fields.vals, hv'])
    simp [Fields.names, reifyFields, hcf, hrv, hrest]

/-- Every subterm of `d` reifies back from the atom that draws it. -/
public theorem reify_subterm [BEq Key] [LawfulBEq Key] (key : Datum → Key) (d : Datum)
    (hF : Faithful key d) (hD : ∀ s ∈ d.subterms, s.Distinct) :
    ∀ n, ∀ s ∈ d.subterms, s.depth ≤ n →
      reify (relationalize key d) n (key s) = some s := by
  intro n
  induction n with
  | zero => intro s _ h; cases s; simp [Datum.depth] at h
  | succ n ih =>
    intro s hs hn
    obtain ⟨s₀, hrep, hs₀mem, hkey⟩ := rep_eq_some key hs
    have hskel : Datum.skel key s₀ = Datum.skel key s := hF s₀ hs₀mem s hs hkey
    have hatom : s₀.atom = s.atom := congrArg Prod.fst hskel
    have hch : ∀ f, (s₀.child f).map key = (s.child f).map key :=
      fun f => congrFun (congrArg Prod.snd hskel) f
    have hIatom : (relationalize key d).atom (key s) = some s.atom := by
      simp [relationalize, hrep, hatom]
    have hIchild : ∀ f, (relationalize key d).child (key s) f = (s.child f).map key := by
      intro f; simp [relationalize, hrep, hch f]
    match s, hn, hs, hIatom, hIchild with
    | .node t c fs, hn, hs, hIatom, hIchild =>
      have hfd : fs.depth ≤ n := by simp only [Datum.depth] at hn; omega
      have hfs : reifyFields ((relationalize key d).child (key (.node t c fs)))
          (reify (relationalize key d) n) fs.names = some fs := by
        refine reifyFields_eq key _ _ fs (hD _ hs) ?_ ?_
        · intro f v hf; rw [hIchild f]; simp [Datum.child, hf]
        · intro v hv
          have hvmem : v ∈ d.subterms :=
            Datum.subterms_closed d _ hs v (by simpa [Datum.kids] using hv)
          exact ih v hvmem (Nat.le_trans (Fields.depth_of_mem_vals hv) hfd)
      simp [reify, hIatom, Datum.atom, hfs]

/-- **Fidelity.** A value is recoverable from its relationalization, provided the
    declared identity merges only subterms of equal skeleton and no node names
    two fields alike. -/
public theorem fidelity [BEq Key] [LawfulBEq Key] (key : Datum → Key) (d : Datum)
    (hF : Faithful key d) (hD : ∀ s ∈ d.subterms, s.Distinct) :
    reifyRoot (relationalize key d) d.depth = some d :=
  reify_subterm key d hF hD d.depth d d.mem_subterms_self (Nat.le_refl _)

/-! ## 8. Both hypotheses earn their place -/

/-- An identity that separates distinct subterms — structural identity — is
    faithful on every value, so structural relationalization always round-trips. -/
public theorem faithful_of_injective (key : Datum → Key)
    (hinj : ∀ s s', key s = key s' → s = s') (d : Datum) : Faithful key d := by
  intro s _ s' _ h; rw [hinj s s' h]

/-! ### A coarse identity really does lose the value

Keying by depth merges the two distinct leaves of `pair`: the walk draws one
atom for both, and reifying puts the first-walked representative in both
positions. -/

section Coarse

private def zero : Datum := .node "L" "zero" .nil
private def one  : Datum := .node "L" "one" .nil
private def pair : Datum := .node "T" "pair" (.cons "a" zero (.cons "b" one .nil))
private def flat : Datum := .node "T" "pair" (.cons "a" zero (.cons "b" zero .nil))

private def byDepth : Datum → Nat := Datum.depth

example : ¬ Faithful byDepth pair := by
  intro h
  have := congrArg Prod.fst (h zero (by decide) one (by decide) rfl)
  simp [Datum.skel, Datum.atom, zero, one] at this

example : reifyRoot (relationalize byDepth pair) pair.depth = some flat := by rfl

example : flat ≠ pair := by decide

end Coarse

/-! ### Two fields sharing a name are no longer separable

`fieldRelName` falls back to the field index only for anonymous and
macro-scoped binders, so `inductive Pair | mk (x : Nat) (x : Nat)` — legal
Lean — names both fields `x`. The walker then emits a single relation `x`
carrying both tuples, and which child is field 0 is no longer recoverable.
The model records the same failure functionally: `Fields.find?` reaches only
the first. Either way the diagram no longer determines the value. -/

section Collide

private def leafA : Datum := .node "L" "a" .nil
private def leafB : Datum := .node "L" "b" .nil
private def dup   : Datum := .node "T" "dup" (.cons "x" leafA (.cons "x" leafB .nil))

example : ¬ dup.Distinct := by
  simp [dup, Datum.Distinct, Fields.Distinct, Fields.find?]

example : reifyRoot (relationalize id dup) dup.depth
    = some (.node "T" "dup" (.cons "x" leafA (.cons "x" leafA .nil))) := by rfl

end Collide

/-- info: 'SpytialLean.Fidelity.fidelity' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms fidelity

end SpytialLean.Fidelity
