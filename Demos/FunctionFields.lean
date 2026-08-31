import SpytialLean

open SpytialLean

/-! # Function Fields

A function field over an enumerable domain tabulates: the field keeps its name,
the owner is column 0, and each domain value becomes a column atom. -/

structure HomStruct where
  obj : Type
  hom : obj → obj → Type

structure SimpleFunctor (C D : HomStruct) where
  obj : C.obj → D.obj

inductive ThreeObj where | a | b | c
  deriving Repr

inductive TwoObj where | x | y
  deriving Repr

def threeStruct : HomStruct := { obj := ThreeObj, hom := fun _ _ => Unit }
def twoStruct : HomStruct := { obj := TwoObj, hom := fun _ _ => Unit }

def myObjMap : ThreeObj → TwoObj
  | .a => .x
  | .b => .y
  | .c => .x

def myFunctor : SimpleFunctor threeStruct twoStruct :=
  { obj := myObjMap }

#spytial myFunctor


structure Transform where
  f : Bool → Nat


-- TODO: I wonder if we can do something better about
-- the relationalization here. Like should it be , here's the body
-- of the transform with an "if" etc etc. Like an AST kind of thing?
def myTransform : Transform :=
  { f := fun b => if b then 42 else 0 }

#spytial myTransform

structure Processor where
  process : Nat → Nat

def myProcessor : Processor :=
  { process := fun n => n + 1 }

-- `Nat` is not enumerable: `process` falls back to a labeled node under a
-- binary edge.
#spytial myProcessor
