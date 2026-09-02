import SpytialLean

open SpytialLean

/-! # Function Fields

Structures with function-valued fields over enumerable domains decompose
into flat n-ary relations rather than rendering as opaque lambda blobs: the
field keeps its name, the owner is column 0, and every domain value becomes
a column atom.
-/

/-! ## Lightweight category theory structures -/

/-- A simple "objects + morphisms" container. -/
structure HomStruct where
  obj : Type
  hom : obj → obj → Type

/-- A functor between two HomStructs — `obj` is a function-valued field. -/
structure SimpleFunctor (C D : HomStruct) where
  obj : C.obj → D.obj

/-! ## Concrete instances using finite types -/

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

-- `obj` tabulates: (myFunctor, a, x), (myFunctor, b, y), (myFunctor, c, x)
#spytial myFunctor


/-! ## Simple transform example -/

structure Transform where
  f : Bool → Nat


-- TODO: I wonder if we can do something better about
-- the relationalization here. Like should it be , here's the body
-- of the transform with an "if" etc etc. Like an AST kind of thing?
def myTransform : Transform :=
  { f := fun b => if b then 42 else 0 }

-- `f` tabulates: (myTransform, false, 0), (myTransform, true, 42)
#spytial myTransform

/-! ## Non-finite function field (graceful fallback) -/

structure Processor where
  process : Nat → Nat

def myProcessor : Processor :=
  { process := fun n => n + 1 }

-- Nat is not finite — a labeled node under a binary `process` edge
#spytial myProcessor
