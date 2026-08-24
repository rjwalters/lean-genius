import Proofs.Erdos85FinalDyadicEndpointResidualSaturation

/-!
# Separation of the endpoint residual cell from exceptional support

At endpoint saturation every residual-cell vertex spends its entire graph
degree in the complement of the exceptional signed support.  Thus the
residual cell and exceptional support have no graph edges between them.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- Every neighbor of an endpoint residual-cell vertex is nonexceptional. -/
theorem finalDyadic_endpoint_residual_neighborFinset_subset_nonexceptional
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
    G.neighborFinset w ⊆
      (Finset.univ : Finset V) \ exceptionalSignedSupport G S q := by
  let H := (Finset.univ : Finset V) \ exceptionalSignedSupport G S q
  have hinterCard : (G.neighborFinset w ∩ H).card = q :=
    finalDyadic_endpoint_residual_neighbor_inter_nonexceptional_card_eq_q
      G hfree hq hqa hreg hcard S hdiv hdisp hr hrhalf
        hsupport hemptyClique w hw
  have hneighborCard : (G.neighborFinset w).card = q := by
    rw [G.card_neighborFinset_eq_degree, hreg]
  have heq : G.neighborFinset w ∩ H = G.neighborFinset w :=
    Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by
      rw [hinterCard, hneighborCard])
  intro z hz
  have : z ∈ G.neighborFinset w ∩ H := by
    rw [heq]
    exact hz
  exact (Finset.mem_inter.mp this).2

/-- There are no graph edges from the endpoint residual cell to the
exceptional signed support. -/
theorem finalDyadic_endpoint_residual_neighborFinset_disjoint_exceptional
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
    Disjoint (G.neighborFinset w) (exceptionalSignedSupport G S q) := by
  rw [Finset.disjoint_left]
  intro z hzw hzExceptional
  have hzH := finalDyadic_endpoint_residual_neighborFinset_subset_nonexceptional
    G hfree hq hqa hreg hcard S hdiv hdisp hr hrhalf
      hsupport hemptyClique hw hzw
  exact (Finset.mem_sdiff.mp hzH).2 hzExceptional

end

end Erdos85

#print axioms
  Erdos85.finalDyadic_endpoint_residual_neighborFinset_subset_nonexceptional
#print axioms
  Erdos85.finalDyadic_endpoint_residual_neighborFinset_disjoint_exceptional
