import Proofs.Erdos85FinalDyadicEndpointResidualEquitableCut

/-!
# Adjacency-operator form of the endpoint residual cut

The indicator of the residual cell is sent by the graph adjacency operator
to `r` times the indicator of the nonexceptional layer.
-/

open Finset SimpleGraph Matrix

namespace Erdos85

noncomputable section

/-- Exact adjacency image of the residual-cell indicator. -/
theorem finalDyadic_endpoint_adjMatrix_mulVec_residualIndicator
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q j r : ℕ} (hq : 8 ≤ q)
    (hqa : q = 2 * 2 ^ j) (hreg : ∀ v, G.degree v = q)
    (hcard : Fintype.card V = q * q) (S : Finset V)
    (hdiv : ∀ v, 2 ^ j ∣ (G.neighborFinset v ∩ S).card)
    (hdisp : 2 * (S.card : ℤ) - Fintype.card V = 2 * r)
    (hr : 0 < r) (hrhalf : r < 2 ^ j)
    (hsupport : (exceptionalSignedSupport G S q).card = q)
    (hemptyClique : ∀ ⦃u v⦄,
      u ∈ emptyLineCenters G S → v ∈ emptyLineCenters G S → u ≠ v →
        (secondOrderDefectGraph G).Adj u v) :
    let W := (Finset.univ : Finset V) \ (S ∪
      finalDyadicNegativeHighCutCenters G S j r)
    (G.adjMatrix ℤ).mulVec
        (fun w => if w ∈ W then (1 : ℤ) else 0) =
      (r : ℤ) • (fun v =>
        if v ∈ exceptionalSignedSupport G S q then (0 : ℤ) else 1) := by
  dsimp only
  let W := (Finset.univ : Finset V) \ (S ∪
    finalDyadicNegativeHighCutCenters G S j r)
  funext v
  rw [SimpleGraph.adjMatrix_mulVec_apply]
  have hcount :
      (∑ w ∈ G.neighborFinset v, if w ∈ W then (1 : ℤ) else 0) =
        ((G.neighborFinset v ∩ W).card : ℤ) := by
    simp
  rw [hcount]
  have hdegree := finalDyadic_endpoint_neighbor_inter_residual_card_eq_ite
    G hfree hq hqa hreg hcard S hdiv hdisp hr hrhalf
      hsupport hemptyClique v
  change (G.neighborFinset v ∩ W).card =
    if v ∈ exceptionalSignedSupport G S q then 0 else r at hdegree
  rw [hdegree]
  change ((if v ∈ exceptionalSignedSupport G S q then 0 else r : ℕ) : ℤ) =
    (r : ℤ) *
      (if v ∈ exceptionalSignedSupport G S q then (0 : ℤ) else 1)
  by_cases hv : v ∈ exceptionalSignedSupport G S q
  · rw [if_pos hv, if_pos hv]
    simp
  · rw [if_neg hv, if_neg hv]
    simp

end

end Erdos85

#print axioms Erdos85.finalDyadic_endpoint_adjMatrix_mulVec_residualIndicator
