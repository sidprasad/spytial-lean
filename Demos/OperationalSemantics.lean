import SpytialLean

open SpytialLean

/-! # Operational Semantics — Derivation Trees

A minimalistic imperative language with big-step semantics.
Derivation trees show *why* a program evaluates to a result.

Inspired by Ch 8 of "The Hitchhiker's Guide to Logical Verification".
-/

/-! ## A tiny imperative language -/

-- Variables are just strings
abbrev VarName := String

-- Expressions
inductive Expr where
  | lit (n : Int)
  | var (x : VarName)
  | add (e₁ e₂ : Expr)

-- Statements
inductive Stmt where
  | skip
  | assign (x : VarName) (e : Expr)
  | seq (s₁ s₂ : Stmt)
  | ite (cond : Expr) (thn els : Stmt)

-- State is a map from variable names to values
abbrev State := VarName → Int

def State.update (σ : State) (x : VarName) (v : Int) : State :=
  fun y => if y == x then v else σ y

/-! ## Expression evaluation (total function) -/

def evalExpr : Expr → State → Int
  | .lit n, _ => n
  | .var x, σ => σ x
  | .add e₁ e₂, σ => evalExpr e₁ σ + evalExpr e₂ σ

/-! ## Big-step semantics as an inductive predicate -/

inductive BigStep : Stmt → State → State → Prop where
  | skip {σ} : BigStep .skip σ σ
  | assign {σ x e} : BigStep (.assign x e) σ (σ.update x (evalExpr e σ))
  | seq {s₁ s₂ σ σ' σ''} : BigStep s₁ σ σ' → BigStep s₂ σ' σ'' →
      BigStep (.seq s₁ s₂) σ σ''
  | ite_true {cond thn els σ σ'} : evalExpr cond σ ≠ 0 → BigStep thn σ σ' →
      BigStep (.ite cond thn els) σ σ'
  | ite_false {cond thn els σ σ'} : evalExpr cond σ = 0 → BigStep els σ σ' →
      BigStep (.ite cond thn els) σ σ'

/-! ## A concrete program and its derivation -/

-- Program: x := 1; y := x + 2
def prog1 : Stmt :=
  .seq (.assign "x" (.lit 1))
       (.assign "y" (.add (.var "x") (.lit 2)))

def emptyState : State := fun _ => 0

-- The derivation tree for this program
def prog1_derivation : BigStep prog1 emptyState
    ((emptyState.update "x" 1).update "y" 3) :=
  .seq .assign .assign

-- Can we see the tree: seq → (assign x=1, assign y=3)?
#spytial.proof prog1_derivation
#spytial.proof.datum prog1_derivation
