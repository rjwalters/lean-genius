import Proofs.Erdos85OrderFortyNineSevenHighT0CanonicalGraph

/-!
# Semantic target for the canonical H7/T0 completion CNF

This predicate states exactly the graph properties encoded by the single
canonical completion instance: the fixed high sector, the required low-low
degrees, and global C4-freeness.  Any graph in the H7/T0 stratum produces a
model of these semantics.  A checked UNSAT theorem for a concrete CNF
equivalent to this predicate therefore closes the stratum.
-/

namespace Erdos85

open SimpleGraph

structure SevenHighT0CanonicalCompletionSemantics
    (H : SimpleGraph SevenHighT0CanonicalIndex) [DecidableRel H.Adj] : Prop where
  c4Free : ¬ containsC4 SevenHighT0CanonicalIndex H
  high_high : ∀ w z : Fin 7, ¬ H.Adj (Sum.inl w) (Sum.inl z)
  high_empty : ∀ w copy : Fin 7,
    ¬ H.Adj (Sum.inl w) (Sum.inr (Sum.inl copy))
  high_singleton : ∀ (w : Fin 7) (q : Fin 7 × Fin 2),
    H.Adj (Sum.inl w) (Sum.inr (Sum.inr (Sum.inl q))) ↔ w = q.1
  high_pair : ∀ (w : Fin 7) (key : SevenHighT0PairIndex),
    H.Adj (Sum.inl w) (Sum.inr (Sum.inr (Sum.inr key))) ↔
      w = key.1.1 ∨ w = key.1.2
  low_degree : ∀ i : SevenHighT0LowIndex,
    (H.comap Sum.inr).degree i + sevenHighT0LowIndexSupportCard i = 7

noncomputable section

/-- Every actual seven-high, empty-triple graph realizes the canonical
completion semantics.  This is the graph-to-SAT semantic bridge, independent
of any particular DIMACS encoding. -/
theorem sevenHighT0CanonicalGraph_completionSemantics
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (hHigh : (orderFortyNineHighVertices G).card = 7)
    (hzero : orderFortyNineHighIncidenceCount G 3 = 0)
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 7) :
    SevenHighT0CanonicalCompletionSemantics
      (sevenHighT0CanonicalGraph G hfree hmin hHigh hzero e) := by
  refine
    { c4Free := sevenHighT0CanonicalGraph_not_containsC4
        G hfree hmin hHigh hzero e
      high_high := sevenHighT0CanonicalGraph_high_high_not_adj
        G hfree hmin hHigh hzero e
      high_empty := sevenHighT0CanonicalGraph_high_empty_not_adj
        G hfree hmin hHigh hzero e
      high_singleton := sevenHighT0CanonicalGraph_high_singleton_adj_iff
        G hfree hmin hHigh hzero e
      high_pair := sevenHighT0CanonicalGraph_high_pair_adj_iff
        G hfree hmin hHigh hzero e
      low_degree := ?_ }
  intro i
  change (sevenHighT0LowGraph G hfree hmin hHigh hzero e).degree i +
    sevenHighT0LowIndexSupportCard i = 7
  exact sevenHighT0LowGraph_degree_add_supportCard_eq_seven
    G hfree hmin hHigh hzero e i

end


end Erdos85

#print axioms Erdos85.sevenHighT0CanonicalGraph_completionSemantics
