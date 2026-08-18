import Proofs.Erdos85SignedRegularEigenvalueRange
import Proofs.Erdos85BinarySquareBipartiteSizeTwoAlternatingExclusion

/-!
# The size-two joint eigenvalue `-7` is impossible at order 64

At the negative endpoint of a seven-regular defect component, a signed
eigenvector reverses sign on every defect edge and therefore supplies a
bipartition.  The uniform bipartite size-two exclusion then gives the desired
contradiction.
-/

open SimpleGraph Matrix

namespace Erdos85

noncomputable section

theorem orderSixtyFour_sizeTwoPart_signedJointEigenvector_muNegativeSeven_false
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
    (hother : ∀ c' : (secondOrderDefectGraph G).ConnectedComponent,
      c' ≠ c → c'.supp.ncard ≠ 8)
    (s : V → ℤ)
    (hs_in : ∀ x, x ∈ c.supp → s x = -1 ∨ s x = 1)
    (hDs : ∀ x, x ∈ c.supp →
      ∑ y ∈ (secondOrderDefectGraph G).neighborFinset x, s y = -7 * s x) :
    False := by
  let D := secondOrderDefectGraph G
  have hDreg : ∀ x, D.degree x = 7 := by
    intro x
    have h := secondOrderDefectGraph_degree_eq_excess_add_two G hfree hreg
      (show Fintype.card V = 8 * (8 - 1) + 3 + (8 - 3) by omega) x
    change D.degree x = (8 - 3) + 2 at h
    omega
  have hclosed : ∀ x y, x ∈ c.supp → D.Adj x y → y ∈ c.supp := by
    intro x y hx hxy
    rw [ConnectedComponent.mem_supp_iff] at hx ⊢
    rw [← hx]
    exact (ConnectedComponent.connectedComponentMk_eq_of_adj hxy).symm
  obtain ⟨col, hbip⟩ := exists_boolColor_of_signed_negativeDegree_eigenvector_on
    D c.supp hclosed 7 hDreg s hs_in (fun x hx => by simpa using hDs x hx)
  exact binarySquare_regular_sizeTwoPart_bipartite_false
    G hfree (by omega) hreg hcard c hc hother col
      (fun x y hx hy hxy => hbip x y hx hy hxy)

end

end Erdos85

#print axioms Erdos85.orderSixtyFour_sizeTwoPart_signedJointEigenvector_muNegativeSeven_false
