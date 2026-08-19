import Proofs.Erdos85SizeTwoEigenlineAllTriangleCycleDiagonal
import Proofs.Erdos85SizeTwoEigenlineTriangleFreeSector

/-!
# Rigidity of the short cycle in the q=8 six-plus-ten stratum

Node: `SIZE-TWO-EIGENLINE(8)` beneath outline F.3.

The six-cycle is wholly triangle-free, so both of its ambient cycle neighbors
are second-order defect neighbors.  Its exact diagonal defect quotient is two.
Consequently these are all of its defect neighbors within the six-cycle: on
that component, defect adjacency and ambient cycle adjacency coincide.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- In the q=8 `6+10` stratum, second-order defect adjacency restricted to
the six-cycle is exactly its ambient cycle adjacency. -/
theorem binarySquare_regular_sizeTwoPart_eight_sixTen_shortCycle_defectAdj_iff
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
    [DecidableEq (G.induce c.supp).ConnectedComponent]
    (hc : c.supp.ncard = 8 * 2)
    (s : V → ℤ)
    (hs_in : ∀ x ∈ c.supp, s x = -1 ∨ s x = 1)
    (hs_out : ∀ x ∉ c.supp, s x = 0)
    (hA_in : ∀ x ∈ c.supp,
      ∑ y ∈ G.neighborFinset x, s y = -2 * s x)
    (a b : (G.induce c.supp).ConnectedComponent)
    (ha : a.supp.ncard = 6) (hb : b.supp.ncard = 10)
    (x y : c.supp) (hx : x ∈ a.supp) (hy : y ∈ a.supp) :
    ((secondOrderDefectGraph G).induce c.supp).Adj x y ↔
      (G.induce c.supp).Adj x y := by
  classical
  let H := G.induce c.supp
  let K := (secondOrderDefectGraph G).induce c.supp
  have hHdegree : ∀ z : c.supp, H.degree z = 2 := by
    intro z
    exact binarySquare_regular_degree_induce_defectComponent_eq_part
      G hfree (by omega) hreg hcard c (m := 2)
        (by simpa [Nat.mul_comm] using hc) z
  have htf : ∀ z : c.supp, z ∈ a.supp →
      (triangleFreeEdgeGraph G).degree z.1 = 2 :=
    binarySquare_regular_sizeTwoPart_eight_sixTen_shortCycle_allTriangleFree
      G hfree hreg hcard c hc s hs_in hs_out hA_in a b ha hb
  have hcycleSubset : H.neighborFinset x ⊆ componentNeighborFinset K H a x := by
    intro z hz
    have hxz : H.Adj x z := (H.mem_neighborFinset x z).mp hz
    have hzmem : z ∈ a.supp := by
      rw [ConnectedComponent.mem_supp_iff]
      exact (ConnectedComponent.connectedComponentMk_eq_of_adj hxz).symm.trans
        ((ConnectedComponent.mem_supp_iff a x).mp hx)
    have htfEdge : (triangleFreeEdgeGraph G).Adj x.1 z.1 :=
      sizeTwo_triangleFreeEdge_of_degree_two G c hHdegree x z hxz (htf x hx)
    have hK : K.Adj x z := Or.inr htfEdge
    rw [componentNeighborFinset, Finset.mem_filter]
    exact ⟨(K.mem_neighborFinset x z).mpr hK,
      (ConnectedComponent.mem_supp_iff a z).mp hzmem⟩
  have hcommReal : K.adjMatrix ℝ * H.adjMatrix ℝ =
      H.adjMatrix ℝ * K.adjMatrix ℝ := by
    have hglobal := adjMatrix_comm_secondOrderDefect_of_regular_field
      (K := ℝ) G hfree hreg
    exact (induce_component_adjMatrix_comm_of_comm
      G (secondOrderDefectGraph G) hglobal c).symm
  have hKcard : (componentNeighborFinset K H a x).card = 2 := by
    have hquot := binarySquare_regular_sizeTwoPart_eight_sixTen_cycleQuotient
      G hfree hreg hcard c hc s hs_in hs_out hA_in a b ha hb
    rw [← componentQuotientMatrix_apply_eq K H 2 hHdegree hcommReal a a hx]
    exact hquot.1
  have hHcard : (H.neighborFinset x).card = 2 := by
    rw [H.card_neighborFinset_eq_degree, hHdegree]
  have heq : H.neighborFinset x = componentNeighborFinset K H a x :=
    Finset.eq_of_subset_of_card_le hcycleSubset (by omega)
  constructor
  · intro hxy
    have hymem : y ∈ componentNeighborFinset K H a x := by
      rw [componentNeighborFinset, Finset.mem_filter]
      exact ⟨(K.mem_neighborFinset x y).mpr hxy,
        (ConnectedComponent.mem_supp_iff a y).mp hy⟩
    rw [← heq] at hymem
    exact (H.mem_neighborFinset x y).mp hymem
  · intro hxy
    exact Or.inr (sizeTwo_triangleFreeEdge_of_degree_two
      G c hHdegree x y hxy (htf x hx))

end

end Erdos85

#print axioms Erdos85.binarySquare_regular_sizeTwoPart_eight_sixTen_shortCycle_defectAdj_iff
