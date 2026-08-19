import Proofs.Erdos85TriangleFreeSecondOrderIntersection
import Proofs.Erdos85SizeTwoEigenlineDisconnectedEightReduction

/-! # Internal-cycle reduction at `mu = -3` -/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- The filtered internal equation extends to the full ambient adjacency
sum because the signed vector vanishes off the distinguished component. -/
theorem sizeTwo_internal_full_sum_of_filtered
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (c : (secondOrderDefectGraph G).ConnectedComponent) (s : V → ℤ)
    (hs_out : ∀ x, x ∉ c.supp → s x = 0)
    (hH : ∀ z ∈ c.supp, ∑ y ∈ (G.neighborFinset z).filter
      (fun y ↦ (secondOrderDefectGraph G).connectedComponentMk y = c),
        s y = -2 * s z) :
    ∀ z ∈ c.supp, ∑ y ∈ G.neighborFinset z, s y = -2 * s z := by
  intro z hz
  rw [← hH z hz]
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro y hy hynot
  apply hs_out y
  intro hyc
  apply hynot
  exact Finset.mem_filter.mpr ⟨hy,
    (ConnectedComponent.mem_supp_iff c y).mp hyc⟩

/-- If the internal ambient two-factor at `mu=-3` is disconnected, any two
distinct cycles have one of the exact `6+10`, `10+6`, or `8+8` defect
quotients. Thus the generic disconnected q=8 reduction applies beyond the
`q-5` eigenline branch. -/
theorem orderSixtyFour_sizeTwo_muNegThree_disconnected_cycleQuotient_reduction
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
    (a b : (G.induce c.supp).ConnectedComponent) (hab : a ≠ b) :
    (a.supp.ncard = 6 ∧ b.supp.ncard = 10 ∧
      componentQuotientMatrix
          ((secondOrderDefectGraph G).induce c.supp) (G.induce c.supp) a a = 2 ∧
      componentQuotientMatrix
          ((secondOrderDefectGraph G).induce c.supp) (G.induce c.supp) a b = 5 ∧
      componentQuotientMatrix
          ((secondOrderDefectGraph G).induce c.supp) (G.induce c.supp) b a = 3 ∧
      componentQuotientMatrix
          ((secondOrderDefectGraph G).induce c.supp) (G.induce c.supp) b b = 4) ∨
    (a.supp.ncard = 10 ∧ b.supp.ncard = 6 ∧
      componentQuotientMatrix
          ((secondOrderDefectGraph G).induce c.supp) (G.induce c.supp) a a = 4 ∧
      componentQuotientMatrix
          ((secondOrderDefectGraph G).induce c.supp) (G.induce c.supp) a b = 3 ∧
      componentQuotientMatrix
          ((secondOrderDefectGraph G).induce c.supp) (G.induce c.supp) b a = 5 ∧
      componentQuotientMatrix
          ((secondOrderDefectGraph G).induce c.supp) (G.induce c.supp) b b = 2) ∨
    (a.supp.ncard = 8 ∧ b.supp.ncard = 8 ∧
      ∃ r : ℕ, 2 ≤ r ∧ r ≤ 7 ∧
        componentQuotientMatrix
            ((secondOrderDefectGraph G).induce c.supp) (G.induce c.supp) a a = 7 - r ∧
        componentQuotientMatrix
            ((secondOrderDefectGraph G).induce c.supp) (G.induce c.supp) a b = r ∧
        componentQuotientMatrix
            ((secondOrderDefectGraph G).induce c.supp) (G.induce c.supp) b a = r ∧
        componentQuotientMatrix
            ((secondOrderDefectGraph G).induce c.supp) (G.induce c.supp) b b = 7 - r) := by
  have hA := sizeTwo_internal_full_sum_of_filtered G c s hs_out hH
  exact binarySquare_regular_sizeTwoPart_eight_disconnected_cycleQuotient_reduction
    G hfree hreg hcard c hc s hs_in hs_out hA a b hab

end

end Erdos85

#print axioms Erdos85.sizeTwo_internal_full_sum_of_filtered
#print axioms Erdos85.orderSixtyFour_sizeTwo_muNegThree_disconnected_cycleQuotient_reduction
