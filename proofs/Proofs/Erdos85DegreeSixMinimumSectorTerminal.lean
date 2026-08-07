import Proofs.Erdos85CrossComponentPairCount

/-!
# The friendship dichotomy and far-vertex structure

At the exact even boundary the second-order defect relation records exactly
the vertex pairs with no common neighbor: any other pair has exactly one.
This is the friendship-theorem configuration with a 2-factor defect, stated
here without any component hypotheses.

Consequently, for a vertex `x` and any vertex `z` neither equal nor
defect-adjacent nor `G`-adjacent to `x`, the unique common neighbor lies in
`N(x)`: every such `z` has exactly one neighbor inside `N(x)`.  These are
the counting bricks for the degree-six minimum-sector endgame.
-/

namespace Erdos85

open SimpleGraph

/-- **Friendship dichotomy.**  Distinct vertices that are not
defect-adjacent have exactly one common neighbor: zero common neighbors is
the definition of the defect relation, two make a four-cycle. -/
theorem card_common_eq_one_of_not_defectAdj
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {x y : V} (hxy : x ≠ y)
    (hnadj : ¬ (secondOrderDefectGraph G).Adj x y) :
    (G.neighborFinset x ∩ G.neighborFinset y).card = 1 := by
  have hpos : (G.neighborFinset x ∩ G.neighborFinset y).card ≠ 0 := by
    intro h0
    apply hnadj
    rw [secondOrderDefectGraph, SimpleGraph.sup_adj]
    by_cases hadj : G.Adj x y
    · refine Or.inr ?_
      rw [triangleFreeEdgeGraph_adj, mem_triangleFreeNeighbors]
      exact ⟨hadj, h0⟩
    · refine Or.inl ?_
      rw [antipodalGraph_adj, mem_antipodalNeighbors]
      exact ⟨hxy.symm, hadj, h0⟩
  have hle : (G.neighborFinset x ∩ G.neighborFinset y).card ≤ 1 := by
    by_contra hlt
    push Not at hlt
    obtain ⟨v, hv, v', hv', hvv⟩ := Finset.one_lt_card.mp hlt
    rw [Finset.mem_inter, SimpleGraph.mem_neighborFinset,
      SimpleGraph.mem_neighborFinset] at hv hv'
    exact hfree (containsC4_of_two_common hxy hvv hv.1.symm hv.2.symm
      hv'.1.symm hv'.2.symm)
  omega

/-- **Far vertices hit each neighborhood exactly once.**  If `z` is
distinct from `x`, not defect-adjacent and not `G`-adjacent to it, then `z`
has exactly one `G`-neighbor inside `N(x)`. -/
theorem card_neighborFinset_inter_eq_one_of_far
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {x z : V} (hxz : x ≠ z)
    (hnadj : ¬ (secondOrderDefectGraph G).Adj x z)
    (hnG : ¬ G.Adj x z) :
    (G.neighborFinset z ∩ G.neighborFinset x).card = 1 := by
  rw [Finset.inter_comm]
  exact card_common_eq_one_of_not_defectAdj G hfree hxz hnadj

/-- **Neighborhood pairs share only the base.**  Two distinct `G`-neighbors
of a vertex `x` are never defect-adjacent (they share `x`), and their unique
common neighbor is `x` itself. -/
theorem common_eq_base_of_neighbors
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {x y y' : V}
    (hy : G.Adj x y) (hy' : G.Adj x y') (hne : y ≠ y') :
    G.neighborFinset y ∩ G.neighborFinset y' = {x} := by
  have hnadj : ¬ (secondOrderDefectGraph G).Adj y y' := by
    intro h
    have hzero : (G.neighborFinset y ∩ G.neighborFinset y').card = 0 := by
      rcases h with h | h
      · rw [antipodalGraph_adj, mem_antipodalNeighbors] at h
        exact h.2.2
      · rw [triangleFreeEdgeGraph_adj, mem_triangleFreeNeighbors] at h
        exact h.2
    have hxmem : x ∈ G.neighborFinset y ∩ G.neighborFinset y' := by
      rw [Finset.mem_inter, SimpleGraph.mem_neighborFinset,
        SimpleGraph.mem_neighborFinset]
      exact ⟨hy.symm, hy'.symm⟩
    rw [Finset.card_eq_zero] at hzero
    rw [hzero] at hxmem
    exact absurd hxmem (Finset.notMem_empty x)
  have hone := card_common_eq_one_of_not_defectAdj G hfree hne hnadj
  have hxmem : x ∈ G.neighborFinset y ∩ G.neighborFinset y' := by
    rw [Finset.mem_inter, SimpleGraph.mem_neighborFinset,
      SimpleGraph.mem_neighborFinset]
    exact ⟨hy.symm, hy'.symm⟩
  obtain ⟨w, hw⟩ := Finset.card_eq_one.mp hone
  rw [hw] at hxmem ⊢
  rw [Finset.mem_singleton] at hxmem
  rw [hxmem]

end Erdos85
