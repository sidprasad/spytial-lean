import SpytialLean

open SpytialLean

/-! # Operational Semantics — Derivation Trees

Inspired by Ch 8 of "The Hitchhiker's Guide to Logical Verification". -/

abbrev VarName := String

inductive Expr where
  | lit (n : Int)
  | var (x : VarName)
  | add (e₁ e₂ : Expr)

inductive Stmt where
  | skip
  | assign (x : VarName) (e : Expr)
  | seq (s₁ s₂ : Stmt)
  | ite (cond : Expr) (thn els : Stmt)

abbrev State := VarName → Int

def State.update (σ : State) (x : VarName) (v : Int) : State :=
  fun y => if y == x then v else σ y

def evalExpr : Expr → State → Int
  | .lit n, _ => n
  | .var x, σ => σ x
  | .add e₁ e₂, σ => evalExpr e₁ σ + evalExpr e₂ σ

inductive BigStep : Stmt → State → State → Prop where
  | skip {σ} : BigStep .skip σ σ
  | assign {σ x e} : BigStep (.assign x e) σ (σ.update x (evalExpr e σ))
  | seq {s₁ s₂ σ σ' σ''} : BigStep s₁ σ σ' → BigStep s₂ σ' σ'' →
      BigStep (.seq s₁ s₂) σ σ''
  | ite_true {cond thn els σ σ'} : evalExpr cond σ ≠ 0 → BigStep thn σ σ' →
      BigStep (.ite cond thn els) σ σ'
  | ite_false {cond thn els σ σ'} : evalExpr cond σ = 0 → BigStep els σ σ' →
      BigStep (.ite cond thn els) σ σ'

-- x := 1; y := x + 2
def prog1 : Stmt :=
  .seq (.assign "x" (.lit 1))
       (.assign "y" (.add (.var "x") (.lit 2)))

def emptyState : State := fun _ => 0

def prog1_derivation : BigStep prog1 emptyState
    ((emptyState.update "x" 1).update "y" 3) :=
  .seq .assign .assign

#spytial.proof prog1_derivation
#spytial.proof.datum prog1_derivation
