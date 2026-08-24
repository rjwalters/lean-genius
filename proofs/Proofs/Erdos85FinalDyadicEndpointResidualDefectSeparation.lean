import Proofs.Erdos85FinalDyadicEndpointResidualEmptyGrid

/-!
# Defect separation of the endpoint residual cell

The negative-high cell is the union of the graph neighborhoods of the empty
centers.  The residual/empty-block perfect grid therefore gives one common
graph neighbor for every residual/negative-high pair.  Since second-order
defect adjacency is exactly zero common neighbors, the corresponding defect
cut is empty.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- No endpoint residual-cell vertex has a second-order defect neighbor in
the negative-high cell. -/
theorem finalDyadic_endpoint_residual_defectNeighbor_inter_negativeHigh_eq_empty
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
        (secondOrderDefectGraph G).Adj u v)
    {w : V}
    (hw : w ∈ (Finset.univ : Finset V) \ (S ∪
      finalDyadicNegativeHighCutCenters G S j r)) :
    (secondOrderDefectGraph G).neighborFinset w ∩
      finalDyadicNegativeHighCutCenters G S j r = ∅ := by
  apply Finset.card_eq_zero.mp
  by_contra hcardNe
  obtain ⟨x, hx⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hcardNe)
  have hxData := Finset.mem_inter.mp hx
  have hD : (secondOrderDefectGraph G).Adj w x :=
    ((secondOrderDefectGraph G).mem_neighborFinset w x).mp hxData.1
  obtain ⟨e, he, hxe⟩ :=
    (finalDyadic_mem_negativeHigh_iff_exists_empty_neighbor
      G hfree hq hqa hreg hcard S hdiv hdisp hr hrhalf
        hsupport hemptyClique x).mp hxData.2
  have hone :=
    finalDyadic_endpoint_residual_emptyBlock_commonNeighbor_card_eq_one
      G hfree hq hqa hreg hcard S hdiv hdisp hr hrhalf
        hsupport hemptyClique hw he hxe
  have hzero := (secondOrderDefectGraph_adj_iff_card_common_eq_zero
    G hfree hD.ne).mp hD
  rw [Finset.inter_comm] at hzero
  omega

end

end Erdos85

#print axioms
  Erdos85.finalDyadic_endpoint_residual_defectNeighbor_inter_negativeHigh_eq_empty
