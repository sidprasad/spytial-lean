module

namespace SpytialLean.CounterfactualContext

/-- Inclusion-minimal hitting sets for the conflicts added so far. Each vertex is a
    declaration index. Candidates are sorted so the same set has one representation.
    Initially the empty set hits the empty family of conflicts. -/
public structure HittingSets where
  conflicts : Array (Array Nat) := #[]
  candidates : Array (Array Nat) := #[#[]]
  limited : Bool := false

/-- A hitting set is minimal iff each of its vertices is the only hit on some edge.
    See Murakami and Uno, “Efficient Algorithms for Dualizing Large-Scale Hypergraphs”,
    Property 1 (the critical-edge condition). https://arxiv.org/abs/1102.3813 -/
private def eachVertexIsNecessary (conflicts : Array (Array Nat)) (candidate : Array Nat) : Bool :=
  candidate.all fun vertex => conflicts.any fun edge =>
    edge.contains vertex && !(edge.any fun other => other != vertex && candidate.contains other)

/-- One step of Berge's incremental transversal algorithm. Keep candidates hitting the new
    edge. Extend each remaining candidate by one vertex of the edge, retaining minimal sets.
    See Szathmáry, “An incremental algorithm for computing the transversal hypergraph”,
    Eq. (2.3). https://doi.org/10.33039/ami.2023.08.007

    The caller bounds the number retained. Once a candidate is dropped, later frontiers
    may be incomplete, but every retained set still satisfies the minimality test. -/
public def HittingSets.addConflict (sets : HittingSets) (edge : Array Nat) (limit : Nat) :
    HittingSets := Id.run do
  let conflicts := sets.conflicts.push edge
  let mut candidates := #[]
  for old in sets.candidates do
    let extensions := if edge.any old.contains then #[old]
      else edge.map fun vertex => (old.push vertex).qsort (· < ·)
    for candidate in extensions do
      if candidates.contains candidate || !eachVertexIsNecessary conflicts candidate then continue
      if candidates.size == limit then return { conflicts, candidates, limited := true }
      candidates := candidates.push candidate
  return { conflicts, candidates, limited := sets.limited }

end SpytialLean.CounterfactualContext
