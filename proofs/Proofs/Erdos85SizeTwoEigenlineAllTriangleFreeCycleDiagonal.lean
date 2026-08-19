import Proofs.Erdos85SizeTwoEigenlineEightEightSectorRefinement
import Proofs.Erdos85SizeTwoEigenlineTriangleFreeSector

/-!
# Lower diagonal bound for an all-triangle-free internal cycle

Node: `SIZE-TWO-EIGENLINE(q)` beneath outline F.3.

Every ambient edge of an all-triangle-free internal cycle is itself a
second-order defect edge.  Since the internal ambient graph is two-regular,
the diagonal defect quotient is therefore at least two.  At q=8 in the
`8+8` quotient `[[7-r,r],[r,7-r]]`, this forces `r ≤ 5`.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- An all-triangle-free internal cycle contributes its two ambient cycle
neighbors to the diagonal second-order defect quotient. -/
theorem binarySquare_regular_sizeTwoPart_allTriangleFree_cycleQuotient_two_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hc : c.supp.ncard = q * 2)
    [DecidableEq (G.induce c.supp).ConnectedComponent]
    (a : (G.induce c.supp).ConnectedComponent)
    (htf : ∀ x : c.supp, x ∈ a.supp →
      (triangleFreeEdgeGraph G).degree x.1 = 2) :
    2 ≤ componentQuotientMatrix
      ((secondOrderDefectGraph G).induce c.supp) (G.induce c.supp) a a := by
  classical
  let H := G.induce c.supp
  let K := (secondOrderDefectGraph G).induce c.supp
  obtain ⟨xs, hxA⟩ := a.nonempty_supp
  have hHdegree : ∀ z : c.supp, H.degree z = 2 := by
    intro z
    exact binarySquare_regular_degree_induce_defectComponent_eq_part
      G hfree hq hreg hcard c (m := 2)
        (by simpa [Nat.mul_comm] using hc) z
  have hsub : H.neighborFinset xs ⊆ componentNeighborFinset K H a xs := by
    intro y hy
    have hxy : H.Adj xs y := (H.mem_neighborFinset xs y).mp hy
    have hyA : y ∈ a.supp := by
      rw [ConnectedComponent.mem_supp_iff]
      exact (ConnectedComponent.connectedComponentMk_eq_of_adj hxy).symm.trans
        ((ConnectedComponent.mem_supp_iff a xs).mp hxA)
    have htfEdge : (triangleFreeEdgeGraph G).Adj xs.1 y.1 :=
      sizeTwo_triangleFreeEdge_of_degree_two G c hHdegree xs y hxy
        (htf xs hxA)
    rw [componentNeighborFinset, Finset.mem_filter]
    exact ⟨(K.mem_neighborFinset xs y).mpr (Or.inr htfEdge),
      (ConnectedComponent.mem_supp_iff a y).mp hyA⟩
  obtain ⟨_hHdegree', _hKdegree, _hcommZ⟩ :=
    binarySquare_regular_sizeTwoPart_commuting_regular_blocks
      G hfree hq hreg hcard c hc
  have hcommReal : K.adjMatrix ℝ * H.adjMatrix ℝ =
      H.adjMatrix ℝ * K.adjMatrix ℝ := by
    have hglobal := adjMatrix_comm_secondOrderDefect_of_regular_field
      (K := ℝ) G hfree hreg
    exact (induce_component_adjMatrix_comm_of_comm
      G (secondOrderDefectGraph G) hglobal c).symm
  rw [componentQuotientMatrix_apply_eq K H 2 hHdegree hcommReal a a hxA]
  calc
    2 = (H.neighborFinset xs).card := by
      rw [H.card_neighborFinset_eq_degree, hHdegree]
    _ ≤ (componentNeighborFinset K H a xs).card := Finset.card_le_card hsub

/-- In the q=8 `8+8` quotient, an all-triangle-free internal cycle forces
the off-diagonal parameter to be at most five. -/
theorem binarySquare_regular_sizeTwoPart_eight_eightEight_allTriangleFree_parameter_le_five
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (hreg : ∀ x, G.degree x = 8)
    (hcard : Fintype.card V = 8 * 8)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hc : c.supp.ncard = 8 * 2)
    [DecidableEq (G.induce c.supp).ConnectedComponent]
    (a : (G.induce c.supp).ConnectedComponent) (r : ℕ)
    (hdiag : componentQuotientMatrix
      ((secondOrderDefectGraph G).induce c.supp) (G.induce c.supp) a a = 7 - r)
    (htf : ∀ x : c.supp, x ∈ a.supp →
      (triangleFreeEdgeGraph G).degree x.1 = 2) :
    r ≤ 5 := by
  have htwo :=
    binarySquare_regular_sizeTwoPart_allTriangleFree_cycleQuotient_two_le
      G hfree (by omega) hreg hcard c hc a htf
  rw [hdiag] at htwo
  omega

end


end Erdos85

#print axioms Erdos85.binarySquare_regular_sizeTwoPart_allTriangleFree_cycleQuotient_two_le
#print axioms Erdos85.binarySquare_regular_sizeTwoPart_eight_eightEight_allTriangleFree_parameter_le_five
