import Proofs.Erdos85OneHighV2GraphLedgers

/-! Graph-side coverage of the historical 25 two-edge cubes.
The DIMACS IDs are checked separately against the native input inventory.
This lemma asserts neither cube UNSAT nor certificate verification. -/
namespace Erdos85

/-- Every constrained H1 graph chooses a neighbor of the unmatched last vertex
of block 0 in block 2, and one of the unmatched last vertex of block 1 in block 3.
Thus the 5 × 5 pairs cover the graph family. -/
theorem oneHighCube25_graph_cover
    (a : Nat) (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (hc : OneHighPureFamilyCnfConstraints a R) :
    ∃ i j : Fin 5,
      R.Adj (oneHighFamilyVertex 0 4) (oneHighFamilyVertex 2 i) ∧
      R.Adj (oneHighFamilyVertex 1 4) (oneHighFamilyVertex 3 j) := by
  have hleft := oneHighFamilyUnmatched_not_misses_farBlock a R hc
    (0 : Fin 8) (2 : Fin 8) (4 : Fin 5)
    (by simp [oneHighFamilyVertexMatched, oneHighFamilyVertex_val])
    (by decide) (by decide)
  have hright := oneHighFamilyUnmatched_not_misses_farBlock a R hc
    (1 : Fin 8) (3 : Fin 8) (4 : Fin 5)
    (by simp [oneHighFamilyVertexMatched, oneHighFamilyVertex_val])
    (by decide) (by decide)
  simp only [oneHighFamilyMissesBlock, not_forall, Classical.not_not] at hleft hright
  obtain ⟨i, hi⟩ := hleft
  obtain ⟨j, hj⟩ := hright
  exact ⟨i, j, hi, hj⟩

end Erdos85

#print axioms Erdos85.oneHighCube25_graph_cover
