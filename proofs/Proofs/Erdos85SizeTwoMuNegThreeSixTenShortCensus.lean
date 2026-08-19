import Proofs.Erdos85SizeTwoMuNegThreeInternalCycleReduction
import Proofs.Erdos85SizeTwoEigenlineSixTenShortCycleRigidity

/-! # The short-cycle census in the `mu=-3` six-plus-ten stratum -/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- In a `6+10` internal-cycle split arising from the filtered size-two
equation, every short-cycle vertex has exactly two triangle-free incident
edges and exactly three rooted triangles. On the short cycle, defect
adjacency is exactly ambient cycle adjacency. -/
theorem orderSixtyFour_sizeTwo_sixTen_shortCycle_census_of_filtered
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
    (hs_out : ∀ x, x ∉ c.supp → s x = 0)
    (hs_in : ∀ x, x ∈ c.supp → s x = -1 ∨ s x = 1)
    (hH : ∀ z ∈ c.supp, ∑ y ∈ (G.neighborFinset z).filter
      (fun y ↦ (secondOrderDefectGraph G).connectedComponentMk y = c),
        s y = -2 * s z)
    (a b : (G.induce c.supp).ConnectedComponent)
    (ha : a.supp.ncard = 6) (hb : b.supp.ncard = 10) :
    (∀ x : c.supp, x ∈ a.supp →
      (triangleFreeEdgeGraph G).degree x.1 = 2 ∧
        (G.induce (G.neighborSet x.1)).edgeFinset.card = 3) ∧
    ∀ x y : c.supp, x ∈ a.supp → y ∈ a.supp →
      (((secondOrderDefectGraph G).induce c.supp).Adj x y ↔
        (G.induce c.supp).Adj x y) := by
  have hA := sizeTwo_internal_full_sum_of_filtered G c s hs_out hH
  have htf : ∀ x : c.supp, x ∈ a.supp →
      (triangleFreeEdgeGraph G).degree x.1 = 2 :=
    binarySquare_regular_sizeTwoPart_eight_sixTen_shortCycle_allTriangleFree
      G hfree hreg hcard c hc s hs_in hs_out hA a b ha hb
  refine ⟨?_, ?_⟩
  · intro x hx
    refine ⟨htf x hx, ?_⟩
    have hid := card_triangleFreeNeighbors_add_two_mul_localEdges G hfree x.1
    have htfcard : (triangleFreeNeighbors G x.1).card = 2 := by
      calc
        _ = (triangleFreeEdgeGraph G).degree x.1 := by
          rw [← (triangleFreeEdgeGraph G).card_neighborFinset_eq_degree,
            triangleFreeEdgeGraph_neighborFinset]
        _ = 2 := htf x hx
    rw [htfcard, hreg x.1] at hid
    omega
  · intro x y hx hy
    exact binarySquare_regular_sizeTwoPart_eight_sixTen_shortCycle_defectAdj_iff
      G hfree hreg hcard c hc s hs_in hs_out hA a b ha hb x y hx hy

end

end Erdos85

#print axioms Erdos85.orderSixtyFour_sizeTwo_sixTen_shortCycle_census_of_filtered
