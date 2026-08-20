import Proofs.Erdos85SizeTwoSignedJointNegativeReduction
import Proofs.Erdos85MuNegSevenCompanionFreeKill

/-!
# Regular three-negative-case splitter for size-two signed joints

Completes editor repair item (4) of squad msg 13926: the per-theorem
audit found one further vacuous theorem beyond the three verified —
`orderSixtyFour_sevenComponents_sizeTwo_signedJoint_false_of_three_negative_cases`,
whose `μ = -7` callback ran through the seven-component exclusion.  This
regular counterpart discharges `μ = -7` with the companion-free
all-opposite eigenline kill instead; the underlying four-way splitter
was already regular.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

theorem orderSixtyFour_regular_sizeTwo_signedJoint_false_of_three_negative_cases
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hreg : ∀ x, G.degree x = 8)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hc : c.supp.ncard = 16)
    (s : Fin 64 → ℤ) (mu : ℤ)
    (hs_out : ∀ x, x ∉ c.supp → s x = 0)
    (hs_in : ∀ x, x ∈ c.supp → s x = -1 ∨ s x = 1)
    (hH : ∀ z ∈ c.supp, ∑ y ∈ (G.neighborFinset z).filter
      (fun y ↦ (secondOrderDefectGraph G).connectedComponentMk y = c),
        s y = -2 * s z)
    (hD : ∀ z, z ∈ c.supp →
      ∑ y ∈ (secondOrderDefectGraph G).neighborFinset z, s y = mu * s z)
    (x : Fin 64) (hx : x ∈ c.supp)
    (hnegFive : mu = -5 → False)
    (hnegThree : mu = -3 → False)
    (hnegOne : mu = -1 → False) : False := by
  apply orderSixtyFour_sizeTwo_signedJoint_false_of_negative_cases
    G hfree hreg (by norm_num) c (by simpa using hc) s mu hs_out hs_in
      hH hD x hx
  · intro hmu
    subst mu
    exact binarySquare_regular_allOpposite_defectEigenline_false
      G hfree (by omega) (by omega) hreg (by simp) c s hs_in (by
        intro z hz
        have h := hD z hz
        rw [h]
        norm_num)
  · exact hnegFive
  · exact hnegThree
  · exact hnegOne

end

end Erdos85

#print axioms Erdos85.orderSixtyFour_regular_sizeTwo_signedJoint_false_of_three_negative_cases
