/-
Fidelity of a pure model of spytial relationalization.

The real spytial-lean `relationalize` walks a `Lean.Expr` in `MetaM` (impure
metaprogramming), so it cannot be reasoned about inside Lean's logic. This file
gives a PURE model of relationalization (`rel`) and its inverse (`reify`) over a
universe of structured values (`Datum`), and proves the round trip

    reify (relationalize d) = some d                       (`fidelity`)

i.e. relationalization is lossless: `reify` is a left inverse. This is the
specification the Expr-based implementation is measured against.
-/

namespace SpytialFidelity

/-- The universe of relationalizable values: primitive leaves carrying a payload,
    and binary constructors. (Binary keeps the proof focused; the n-ary /
    named-field generalization is the same argument with a list fold.) -/
inductive Datum where
  | leaf : Nat → Datum
  | bin  : Datum → Datum → Datum
deriving DecidableEq, Repr

/-- A flat atom: a unique id, a type tag, and a payload (the "label"). -/
structure Atom where
  id : Nat
  type : String
  payload : Nat
deriving DecidableEq, Repr

/-- A flat relation tuple: a relation name and a source/target atom id. -/
structure Tup where
  rel : String
  src : Nat
  tgt : Nat
deriving DecidableEq, Repr

/-- A data instance: a designated root atom plus flat atoms and tuples. -/
structure DI where
  root : Nat
  atoms : List Atom
  tups : List Tup
deriving Repr

/-- The result of relationalizing a sub-value: its root id, the atoms/tuples it
    produced, and the next free id. -/
structure RelOut where
  root : Nat
  atoms : List Atom
  tups : List Tup
  next : Nat

/-- Number of nodes (= number of atoms `rel` produces). -/
def size : Datum → Nat
  | .leaf _ => 1
  | .bin l r => 1 + size l + size r

/-- Relationalize `d`, allocating fresh ids from `n` upward. The root id is `n`;
    children are allocated after it. Child atoms come first, the root atom last,
    so for any child the child's atoms are a prefix of the relevant slice. -/
def rel (d : Datum) (n : Nat) : RelOut :=
  match d with
  | .leaf k => { root := n, atoms := [⟨n, "leaf", k⟩], tups := [], next := n + 1 }
  | .bin l r =>
    let L := rel l (n + 1)
    let R := rel r L.next
    { root := n
    , atoms := L.atoms ++ R.atoms ++ [⟨n, "bin", 0⟩]
    , tups := ⟨"l", n, L.root⟩ :: ⟨"r", n, R.root⟩ :: (L.tups ++ R.tups)
    , next := R.next }

def relationalize (d : Datum) : DI :=
  let R := rel d 0
  { root := R.root, atoms := R.atoms, tups := R.tups }

/-- Reconstruct a `Datum` from a flat instance, starting at atom `id`. `fuel`
    bounds the recursion depth (the atom count is always enough). -/
def reifyAt : Nat → List Atom → List Tup → Nat → Option Datum
  | 0, _, _, _ => none
  | fuel + 1, atoms, tups, id =>
    match atoms.find? (·.id == id) with
    | none => none
    | some a =>
      if a.type == "leaf" then
        some (.leaf a.payload)
      else if a.type == "bin" then
        match tups.find? (fun t => t.src == id && t.rel == "l"),
              tups.find? (fun t => t.src == id && t.rel == "r") with
        | some tl, some tr =>
          match reifyAt fuel atoms tups tl.tgt, reifyAt fuel atoms tups tr.tgt with
          | some dl, some dr => some (.bin dl dr)
          | _, _ => none
        | _, _ => none
      else none

def reify (di : DI) : Option Datum :=
  reifyAt di.atoms.length di.atoms di.tups di.root

/-! ## `find?` over appends -/

theorem find?_append_right_none {α} {p : α → Bool} {as bs : List α}
    (h : bs.find? p = none) : (as ++ bs).find? p = as.find? p := by
  rw [List.find?_append, h]; cases as.find? p <;> rfl

theorem find?_append_left_none {α} {p : α → Bool} {as bs : List α}
    (h : as.find? p = none) : (as ++ bs).find? p = bs.find? p := by
  rw [List.find?_append, h]; rfl

/-! ## Nat-range invariants of `rel` -/

theorem rel_root (d : Datum) (n : Nat) : (rel d n).root = n := by
  cases d <;> rfl

theorem rel_lt_next : ∀ (d : Datum) (n : Nat), n < (rel d n).next := by
  intro d
  induction d with
  | leaf k => intro n; simp only [rel]; omega
  | bin l r ihl ihr =>
    intro n
    simp only [rel]
    have h1 := ihl (n + 1)
    have h2 := ihr (rel l (n + 1)).next
    omega

theorem rel_atom_ge : ∀ (d : Datum) (n : Nat) (a : Atom), a ∈ (rel d n).atoms → n ≤ a.id := by
  intro d
  induction d with
  | leaf k =>
    intro n a ha
    simp only [rel, List.mem_singleton] at ha
    subst ha; exact Nat.le_refl n
  | bin l r ihl ihr =>
    intro n a ha
    simp only [rel, List.mem_append, List.mem_singleton] at ha
    rcases ha with (ha | ha) | ha
    · have := ihl (n + 1) a ha; omega
    · have := ihr (rel l (n + 1)).next a ha
      have h2 := rel_lt_next l (n + 1)
      omega
    · subst ha; exact Nat.le_refl n

theorem rel_atom_lt : ∀ (d : Datum) (n : Nat) (a : Atom),
    a ∈ (rel d n).atoms → a.id < (rel d n).next := by
  intro d
  induction d with
  | leaf k =>
    intro n a ha
    simp only [rel, List.mem_singleton] at ha
    subst ha; simp only [rel]; omega
  | bin l r ihl ihr =>
    intro n a ha
    simp only [rel, List.mem_append, List.mem_singleton] at ha ⊢
    rcases ha with (ha | ha) | ha
    · have := ihl (n + 1) a ha
      have h2 := rel_lt_next r (rel l (n + 1)).next
      omega
    · have := ihr (rel l (n + 1)).next a ha; omega
    · subst ha
      show n < (rel r (rel l (n + 1)).next).next
      have h1 := rel_lt_next l (n + 1)
      have h2 := rel_lt_next r (rel l (n + 1)).next
      omega

theorem rel_tup_src_ge : ∀ (d : Datum) (n : Nat) (t : Tup), t ∈ (rel d n).tups → n ≤ t.src := by
  intro d
  induction d with
  | leaf k => intro n t ht; simp only [rel] at ht; exact absurd ht (List.not_mem_nil)
  | bin l r ihl ihr =>
    intro n t ht
    simp only [rel, List.mem_cons, List.mem_append] at ht
    rcases ht with ht | ht | ht | ht
    · subst ht; exact Nat.le_refl n
    · subst ht; exact Nat.le_refl n
    · have := ihl (n + 1) t ht; omega
    · have := ihr (rel l (n + 1)).next t ht
      have h2 := rel_lt_next l (n + 1); omega

theorem rel_tup_src_lt : ∀ (d : Datum) (n : Nat) (t : Tup),
    t ∈ (rel d n).tups → t.src < (rel d n).next := by
  intro d
  induction d with
  | leaf k => intro n t ht; simp only [rel] at ht; exact absurd ht (List.not_mem_nil)
  | bin l r ihl ihr =>
    intro n t ht
    simp only [rel, List.mem_cons, List.mem_append] at ht ⊢
    rcases ht with ht | ht | ht | ht
    · subst ht
      show n < (rel r (rel l (n + 1)).next).next
      have h1 := rel_lt_next l (n + 1)
      have h2 := rel_lt_next r (rel l (n + 1)).next
      omega
    · subst ht
      show n < (rel r (rel l (n + 1)).next).next
      have h1 := rel_lt_next l (n + 1)
      have h2 := rel_lt_next r (rel l (n + 1)).next
      omega
    · have := ihl (n + 1) t ht
      have h2 := rel_lt_next r (rel l (n + 1)).next
      omega
    · have := ihr (rel l (n + 1)).next t ht; omega

theorem rel_len : ∀ (d : Datum) (n : Nat), (rel d n).atoms.length = size d := by
  intro d
  induction d with
  | leaf k => intro n; simp [rel, size]
  | bin l r ihl ihr =>
    intro n
    simp only [rel, size, List.length_append, List.length_singleton]
    rw [ihl (n + 1), ihr (rel l (n + 1)).next]
    omega

/-! ## `reifyAt` reduction lemmas -/

theorem reifyAt_leaf (fuel : Nat) (A : List Atom) (T : List Tup) (id : Nat) (a : Atom)
    (ha : A.find? (·.id == id) = some a) (htype : a.type = "leaf") :
    reifyAt (fuel + 1) A T id = some (.leaf a.payload) := by
  simp only [reifyAt, ha, htype]
  rfl

theorem reifyAt_bin (fuel : Nat) (A : List Atom) (T : List Tup) (id : Nat)
    (a : Atom) (tl tr : Tup)
    (ha : A.find? (·.id == id) = some a) (htype : a.type = "bin")
    (htl : T.find? (fun t => t.src == id && t.rel == "l") = some tl)
    (htr : T.find? (fun t => t.src == id && t.rel == "r") = some tr) :
    reifyAt (fuel + 1) A T id =
      (match reifyAt fuel A T tl.tgt, reifyAt fuel A T tr.tgt with
       | some dl, some dr => some (.bin dl dr)
       | _, _ => none) := by
  simp only [reifyAt, ha, htype, htl, htr]
  rfl

/-! ## Slice lemmas: a `bin`'s flat lists, restricted to a child's id range -/

theorem bin_atom_find_left (l r : Datum) (n k : Nat)
    (h1 : n + 1 ≤ k) (h2 : k < (rel l (n + 1)).next) :
    (rel (.bin l r) n).atoms.find? (·.id == k)
      = (rel l (n + 1)).atoms.find? (·.id == k) := by
  have hnone : ((rel r (rel l (n + 1)).next).atoms ++ [(⟨n, "bin", 0⟩ : Atom)]).find? (·.id == k)
      = none := by
    rw [List.find?_append]
    have h3 : (rel r (rel l (n + 1)).next).atoms.find? (·.id == k) = none := by
      apply List.find?_eq_none.mpr; intro x hx
      have hge := rel_atom_ge r (rel l (n + 1)).next x hx
      simp only [beq_iff_eq]; omega
    have h4 : ([(⟨n, "bin", 0⟩ : Atom)]).find? (·.id == k) = none := by
      apply List.find?_eq_none.mpr; intro x hx
      simp only [List.mem_singleton] at hx; subst hx
      simp only [beq_iff_eq]; omega
    rw [h3, h4]; rfl
  have hatoms : (rel (.bin l r) n).atoms
      = (rel l (n + 1)).atoms ++ ((rel r (rel l (n + 1)).next).atoms ++ [(⟨n, "bin", 0⟩ : Atom)]) := by
    simp only [rel]; rw [List.append_assoc]
  rw [hatoms, find?_append_right_none hnone]

theorem bin_atom_find_right (l r : Datum) (n k : Nat)
    (h1 : (rel l (n + 1)).next ≤ k) :
    (rel (.bin l r) n).atoms.find? (·.id == k)
      = (rel r (rel l (n + 1)).next).atoms.find? (·.id == k) := by
  have hLnone : (rel l (n + 1)).atoms.find? (·.id == k) = none := by
    apply List.find?_eq_none.mpr; intro x hx
    have hlt := rel_atom_lt l (n + 1) x hx
    simp only [beq_iff_eq]; omega
  have hRootNone : ([(⟨n, "bin", 0⟩ : Atom)]).find? (·.id == k) = none := by
    apply List.find?_eq_none.mpr; intro x hx
    simp only [List.mem_singleton] at hx; subst hx
    have := rel_lt_next l (n + 1)
    simp only [beq_iff_eq]; omega
  have hatoms : (rel (.bin l r) n).atoms
      = (rel l (n + 1)).atoms ++ (rel r (rel l (n + 1)).next).atoms ++ [(⟨n, "bin", 0⟩ : Atom)] := by
    simp only [rel]
  rw [hatoms, find?_append_right_none hRootNone, find?_append_left_none hLnone]

theorem bin_tup_find_left (l r : Datum) (n k : Nat) (name : String)
    (h1 : n + 1 ≤ k) (h2 : k < (rel l (n + 1)).next) :
    (rel (.bin l r) n).tups.find? (fun t => t.src == k && t.rel == name)
      = (rel l (n + 1)).tups.find? (fun t => t.src == k && t.rel == name) := by
  have hne : n ≠ k := by omega
  have hRnone : (rel r (rel l (n + 1)).next).tups.find? (fun t => t.src == k && t.rel == name)
      = none := by
    apply List.find?_eq_none.mpr; intro t ht
    have hge := rel_tup_src_ge r (rel l (n + 1)).next t ht
    have hsrc : t.src ≠ k := by omega
    simp only [Bool.and_eq_true, beq_iff_eq]
    rintro ⟨h, _⟩; exact hsrc h
  simp only [rel]
  rw [List.find?_cons_of_neg (by simp [beq_false_of_ne hne]),
      List.find?_cons_of_neg (by simp [beq_false_of_ne hne]),
      find?_append_right_none hRnone]

theorem bin_tup_find_right (l r : Datum) (n k : Nat) (name : String)
    (h1 : (rel l (n + 1)).next ≤ k) :
    (rel (.bin l r) n).tups.find? (fun t => t.src == k && t.rel == name)
      = (rel r (rel l (n + 1)).next).tups.find? (fun t => t.src == k && t.rel == name) := by
  have hn1 := rel_lt_next l (n + 1)
  have hne : n ≠ k := by omega
  have hLnone : (rel l (n + 1)).tups.find? (fun t => t.src == k && t.rel == name) = none := by
    apply List.find?_eq_none.mpr; intro t ht
    have hlt := rel_tup_src_lt l (n + 1) t ht
    have hsrc : t.src ≠ k := by omega
    simp only [Bool.and_eq_true, beq_iff_eq]
    rintro ⟨h, _⟩; exact hsrc h
  simp only [rel]
  rw [List.find?_cons_of_neg (by simp [beq_false_of_ne hne]),
      List.find?_cons_of_neg (by simp [beq_false_of_ne hne]),
      find?_append_left_none hLnone]

/-! ## Main correctness lemma and the fidelity theorem -/

/-- `reifyAt` reconstructs `d` from any flat lists that AGREE with `rel d n` on
    `d`'s id range `[n, (rel d n).next)`. The agreement form (rather than exact
    equality of the lists) is what lets the two children be handled uniformly:
    each child's slice is found inside the parent's lists, undisturbed by the
    other child or the root, because all ids are fresh. -/
theorem reify_correct : ∀ (d : Datum) (n : Nat) (A : List Atom) (T : List Tup) (fuel : Nat),
    size d ≤ fuel →
    (∀ k, n ≤ k → k < (rel d n).next →
        A.find? (·.id == k) = (rel d n).atoms.find? (·.id == k)) →
    (∀ k name, n ≤ k → k < (rel d n).next →
        T.find? (fun t => t.src == k && t.rel == name)
          = (rel d n).tups.find? (fun t => t.src == k && t.rel == name)) →
    reifyAt fuel A T n = some d := by
  intro d
  induction d with
  | leaf k =>
    intro n A T fuel hf hA _hT
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp only [size] at hf; omega⟩
    have hlt : n < (rel (.leaf k) n).next := rel_lt_next (.leaf k) n
    have hn := hA n (Nat.le_refl n) hlt
    have hrhs : (rel (.leaf k) n).atoms.find? (·.id == n) = some (⟨n, "leaf", k⟩ : Atom) := by
      simp only [rel]; rw [List.find?_cons_of_pos (by simp)]
    rw [hrhs] at hn
    exact reifyAt_leaf f A T n ⟨n, "leaf", k⟩ hn rfl
  | bin l r ihl ihr =>
    intro n A T fuel hf hA hT
    have hsz : 1 + size l + size r ≤ fuel := by simpa [size] using hf
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    have hbnext : (rel (.bin l r) n).next = (rel r (rel l (n + 1)).next).next := by simp only [rel]
    have hrootlt : n < (rel (.bin l r) n).next := rel_lt_next (.bin l r) n
    -- root atom lookup
    have hn : A.find? (·.id == n) = some (⟨n, "bin", 0⟩ : Atom) := by
      rw [hA n (Nat.le_refl n) hrootlt]
      have hLnone : (rel l (n + 1)).atoms.find? (·.id == n) = none := by
        apply List.find?_eq_none.mpr; intro x hx
        have := rel_atom_ge l (n + 1) x hx
        simp only [beq_iff_eq]; omega
      have hRnone : (rel r (rel l (n + 1)).next).atoms.find? (·.id == n) = none := by
        apply List.find?_eq_none.mpr; intro x hx
        have := rel_atom_ge r (rel l (n + 1)).next x hx
        have h2 := rel_lt_next l (n + 1)
        simp only [beq_iff_eq]; omega
      have hatoms : (rel (.bin l r) n).atoms
          = (rel l (n + 1)).atoms ++ (rel r (rel l (n + 1)).next).atoms
            ++ [(⟨n, "bin", 0⟩ : Atom)] := by simp only [rel]
      rw [hatoms, List.append_assoc, find?_append_left_none hLnone,
          find?_append_left_none hRnone, List.find?_cons_of_pos (by simp)]
    -- root tuple lookups
    have htl : T.find? (fun t => t.src == n && t.rel == "l")
        = some (⟨"l", n, (rel l (n + 1)).root⟩ : Tup) := by
      rw [hT n "l" (Nat.le_refl n) hrootlt]
      simp only [rel]; rw [List.find?_cons_of_pos (by simp)]
    have htr : T.find? (fun t => t.src == n && t.rel == "r")
        = some (⟨"r", n, (rel r (rel l (n + 1)).next).root⟩ : Tup) := by
      rw [hT n "r" (Nat.le_refl n) hrootlt]
      simp only [rel]
      rw [List.find?_cons_of_neg (by simp), List.find?_cons_of_pos (by simp)]
    -- recursive reconstruction of the two children
    have goalL : reifyAt f A T (n + 1) = some l := by
      apply ihl (n + 1) A T f (by omega)
      · intro k hk1 hk2
        rw [hA k (by omega) (by rw [hbnext]; have := rel_lt_next r (rel l (n + 1)).next; omega)]
        exact bin_atom_find_left l r n k hk1 hk2
      · intro k name hk1 hk2
        rw [hT k name (by omega) (by rw [hbnext]; have := rel_lt_next r (rel l (n + 1)).next; omega)]
        exact bin_tup_find_left l r n k name hk1 hk2
    have goalR : reifyAt f A T (rel l (n + 1)).next = some r := by
      apply ihr (rel l (n + 1)).next A T f (by omega)
      · intro k hk1 hk2
        have hk0 : n ≤ k := by have := rel_lt_next l (n + 1); omega
        rw [hA k hk0 (by rw [hbnext]; exact hk2)]
        exact bin_atom_find_right l r n k hk1
      · intro k name hk1 hk2
        have hk0 : n ≤ k := by have := rel_lt_next l (n + 1); omega
        rw [hT k name hk0 (by rw [hbnext]; exact hk2)]
        exact bin_tup_find_right l r n k name hk1
    -- assemble
    rw [reifyAt_bin f A T n ⟨n, "bin", 0⟩ ⟨"l", n, (rel l (n + 1)).root⟩
          ⟨"r", n, (rel r (rel l (n + 1)).next).root⟩ hn rfl htl htr]
    show (match reifyAt f A T (rel l (n + 1)).root,
                reifyAt f A T (rel r (rel l (n + 1)).next).root with
          | some dl, some dr => some (Datum.bin dl dr)
          | _, _ => none) = some (l.bin r)
    rw [rel_root l (n + 1), rel_root r (rel l (n + 1)).next, goalL, goalR]

theorem fidelity (d : Datum) : reify (relationalize d) = some d := by
  dsimp only [reify, relationalize]
  rw [rel_root d 0]
  apply reify_correct d 0 (rel d 0).atoms (rel d 0).tups (rel d 0).atoms.length
  · have := rel_len d 0; omega
  · intro k _ _; rfl
  · intro k name _ _; rfl

end SpytialFidelity
