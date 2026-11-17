module

public import Lean

public section

namespace SpytialLean.Semantics

universe u v

/-- Worlds compatible with the assumptions at an inspection site. -/
abbrev Context (World : Type u) := World → Prop

/-- The meaning of a proposition in a world. -/
abbrev Fact (World : Type u) := World → Prop

@[expose] def Entails (context : Context World) (fact : Fact World) : Prop :=
  ∀ world, context world → fact world

/-- The semantic interpretation of retained proof types, independent of the inference engine. -/
structure ContextEvidence (World : Type u) (Root : Type v) where
  root : World → Root
  facts : List (Fact World)
  truncated : Bool := false

@[expose] def ContextEvidence.Sound (context : Context World)
    (evidence : ContextEvidence World Root) : Prop :=
  ∀ {fact}, fact ∈ evidence.facts → Entails context fact

end SpytialLean.Semantics
