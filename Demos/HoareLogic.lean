import SpytialLean

open SpytialLean

/-! # Hoare Logic Proof Trees

Hoare triples {P} S {Q} compose into proof trees.
Can we visualize the structure of a Hoare proof?

Inspired by Ch 9 of "The Hitchhiker's Guide to Logical Verification".
-/

/-! ## Reusing the language from OperationalSemantics -/

abbrev VarName' := String
abbrev State' := VarName' → Int

def State'.update (σ : State') (x : VarName') (v : Int) : State' :=
  fun y => if y == x then v else σ y

inductive Expr' where
  | lit (n : Int)
  | var (x : VarName')
  | add (e₁ e₂ : Expr')

inductive Stmt' where
  | skip
  | assign (x : VarName') (e : Expr')
  | seq (s₁ s₂ : Stmt')

def evalExpr' : Expr' → State' → Int
  | .lit n, _ => n
  | .var x, σ => σ x
  | .add e₁ e₂, σ => evalExpr' e₁ σ + evalExpr' e₂ σ

/-! ## Hoare triples as an inductive type -/

/-- A Hoare triple {P} S {Q} is valid if for all states σ,
    P σ → (S terminates in σ') → Q σ'. -/
inductive HoareTriple : (State' → Prop) → Stmt' → (State' → Prop) → Prop where
  | skip {P} : HoareTriple P .skip P
  | assign {Q x e} : HoareTriple (fun σ => Q (σ.update x (evalExpr' e σ)))
      (.assign x e) Q
  | seq {P R Q s₁ s₂} : HoareTriple P s₁ R → HoareTriple R s₂ Q →
      HoareTriple P (.seq s₁ s₂) Q
  | conseq {P P' Q Q' s} : (∀ σ, P' σ → P σ) → HoareTriple P s Q →
      (∀ σ, Q σ → Q' σ) → HoareTriple P' s Q'

/-! ## A concrete Hoare proof -/

-- Program: x := 1; y := x + 2
-- Prove: {True} x := 1; y := x + 2 {y = 3}

def hoare_proof : HoareTriple
    (fun _ => True)
    (.seq (.assign "x" (.lit 1))
          (.assign "y" (.add (.var "x") (.lit 2))))
    (fun σ => σ "y" = 3) :=
  .conseq
    (fun _ _ => by simp [State'.update, evalExpr'])
    (.seq .assign .assign)
    (fun _ h => h)

-- The proof tree: conseq → (weakening, seq → (assign, assign), strengthening)
#spytial.proof hoare_proof
#spytial.proof.datum hoare_proof
