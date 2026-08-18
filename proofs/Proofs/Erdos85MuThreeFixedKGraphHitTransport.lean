import Proofs.Erdos85MuThreeFixedKNativeContradiction
import Proofs.Erdos85MuThreeAllTfGraphTransport

/-!
# Graph-facing transport for the fixed-K certificates

This removes the raw DIMACS valuation and static C4 premise from the
fixed-grid contradiction interface.  The remaining premise is exactly the
row/column hit-count transport that a `MuThreeMixedGridCode` supplies.
-/

namespace Erdos85

open SimpleGraph

/-- A C4-free graph on the 48 occupied cells contradicts any of the nineteen
fixed-K hit tables as soon as its transported row and column counts agree
with that table. -/
theorem false_of_c4Free_mu3FixedKGraphHitCounts
    {W : Type*} [Fintype W] [DecidableEq W]
    (G : SimpleGraph W) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 W G) (e : Fin 48 ≃ W)
    (i : Fin 19)
    (hhitCounts : ∀ spec ∈ mu3GridHitSpecs (mu3FixedKGrid i),
      seqPrefixTrue
          (mu3NativeVarsRow
            (mu3NativeEdgeValOfPairRelation (mu3NormalizedGraphAdj G e))
            spec.1)
          spec.1.size = spec.2) : False :=
  false_of_mu3FixedKNativeStaticConstraints i
    (mu3NativeEdgeValOfPairRelation (mu3NormalizedGraphAdj G e))
    hhitCounts (mu3NormalizedBaseC4_of_c4Free G hfree e)

end Erdos85

#print axioms Erdos85.false_of_c4Free_mu3FixedKGraphHitCounts
