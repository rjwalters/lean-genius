import Proofs.Erdos85SizeTwoEigenlineCyclicPermutationExactCode
import Proofs.Erdos85SizeTwoEigenlineCyclicMatchingCounts

/-!
# Point replication in the cyclic matching design

For an exact code, source-matching incidence is exactly adjacency in the
reconstructed graph.  Consequently every allowed absolute grid point lies
in exactly `q - 2` source matchings: the matching design is a symmetric
configuration, not merely a family of almost-disjoint blocks.
-/

namespace Erdos85

noncomputable section

theorem sizeTwoCyclicSourceMatching_mem_iff_graph_adj
    (q : ℕ) [NeZero q] (a : ZMod q)
    (code : SizeTwoCyclicFullPermutationCode q a)
    (hloop : code.toReciprocalCode.Loopless)
    (source : SizeTwoCyclicMatchingSource q a)
    (v : sizeTwoCyclicExteriorCell q a) :
    v.1 ∈ sizeTwoCyclicSourceMatching code source ↔
      (sizeTwoCyclicCodeGraph q a code.toReciprocalCode).Adj
        (sizeTwoCyclicCellAt q a source.1 source.2) v := by
  constructor
  · intro hmem
    rw [sizeTwoCyclicSourceMatching_mem_iff] at hmem
    obtain ⟨r, hedge⟩ := hmem
    rw [sizeTwoCyclicCodeGraph_adj_cellAt_iff
      q a code.toReciprocalCode hloop]
    refine ⟨r, ?_⟩
    apply Subtype.ext
    apply Prod.ext
    · have h := congrArg Prod.fst hedge
      simpa [sizeTwoCyclicMatchingEdge] using h.symm
    · have h := congrArg Prod.snd hedge
      rw [sizeTwoCyclicCellAt_snd]
      calc
        v.1.2 = source.1 +
            (code.toReciprocalCode.toPermutationCode.perm
              source.1 source.2 r).1 := by
          simpa [sizeTwoCyclicMatchingEdge] using h.symm
        _ = source.1 +
            (r.1 + (code.toReciprocalCode.targetDifference
              source.1 source.2 r).1) := by
          rw [code.toReciprocalCode.target_column_eq source.1 source.2 r]
        _ = source.1 + r.1 +
            (code.toReciprocalCode.targetDifference
              source.1 source.2 r).1 := by abel
  · intro hadj
    have hmem := sizeTwoCyclicRawCell_mem_sourceMatching_of_adj
      q a code hloop (sizeTwoCyclicCellAt q a source.1 source.2) v hadj
    simpa using hmem

/-- Blocks incident with an allowed absolute point are equivalent to the
neighbors of the corresponding reconstructed-graph vertex. -/
def sizeTwoCyclicPointBlocksEquivNeighbors
    (q : ℕ) [NeZero q] (a : ZMod q)
    (code : SizeTwoCyclicExactPermutationCode q a)
    (v : sizeTwoCyclicExteriorCell q a) :
    {source : SizeTwoCyclicMatchingSource q a //
      v.1 ∈ sizeTwoCyclicSourceMatching code.toFullCode source} ≃
    {u : sizeTwoCyclicExteriorCell q a // code.graph.Adj u v} :=
  Equiv.subtypeEquiv (sizeTwoCyclicExteriorCellEquiv q a).symm (fun source => by
    simpa [SizeTwoCyclicExactPermutationCode.graph,
      SizeTwoCyclicExactPermutationCode.toReciprocalCode,
      sizeTwoCyclicCellAt] using
      (sizeTwoCyclicSourceMatching_mem_iff_graph_adj
        q a code.toFullCode code.loopless source v))

/-- Exact point replication: every allowed absolute grid point belongs to
`q - 2` source matchings. -/
theorem sizeTwoCyclicPointReplication_card_eq_sub_two
    (q : ℕ) [NeZero q] (a : ZMod q)
    (code : SizeTwoCyclicExactPermutationCode q a)
    (hq1 : (1 : ZMod q) ≠ 0)
    (v : sizeTwoCyclicExteriorCell q a) :
    Fintype.card {source : SizeTwoCyclicMatchingSource q a //
      v.1 ∈ sizeTwoCyclicSourceMatching code.toFullCode source} = q - 2 := by
  classical
  rw [Fintype.card_congr
    (sizeTwoCyclicPointBlocksEquivNeighbors q a code v)]
  letI : DecidableRel code.graph.Adj := Classical.decRel _
  calc
    Fintype.card {u : sizeTwoCyclicExteriorCell q a // code.graph.Adj u v} =
        code.graph.degree v := by
      rw [show Fintype.card {u : sizeTwoCyclicExteriorCell q a //
          code.graph.Adj u v} =
          Fintype.card {u : sizeTwoCyclicExteriorCell q a //
            u ∈ code.graph.neighborFinset v} by
        apply Fintype.card_congr
        exact Equiv.subtypeEquiv (Equiv.refl _) (fun u => by
          simp [SimpleGraph.mem_neighborFinset, code.graph.adj_comm])]
      exact Fintype.card_coe _
    _ = q - 2 := sizeTwoCyclic_degree_eq_sub_two_of_row_hit
      q a code.graph hq1 code.graph_row_hit v

end

end Erdos85

#print axioms Erdos85.sizeTwoCyclicSourceMatching_mem_iff_graph_adj
#print axioms Erdos85.sizeTwoCyclicPointReplication_card_eq_sub_two
