import Proofs.Erdos85SizeTwoMuNegOneSixTenExclusion

/-! # Final disconnected reduction at `mu=-1` -/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- After excluding the unequal `6+10` split, any two distinct internal
cycles in the `mu=-1` component have size eight and the symmetric `r`-quotient. -/
theorem orderSixtyFour_sizeTwo_muNegOne_distinctCycles_eightEight
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
    (hD : ∀ z, z ∈ c.supp →
      ∑ y ∈ (secondOrderDefectGraph G).neighborFinset z,
        s y = (-1 : ℤ) * s z)
    (a b : (G.induce c.supp).ConnectedComponent) (hab : a ≠ b) :
    a.supp.ncard = 8 ∧ b.supp.ncard = 8 ∧
      ∃ r : ℕ, 2 ≤ r ∧ r ≤ 7 ∧
        componentQuotientMatrix
            ((secondOrderDefectGraph G).induce c.supp) (G.induce c.supp) a a = 7 - r ∧
        componentQuotientMatrix
            ((secondOrderDefectGraph G).induce c.supp) (G.induce c.supp) a b = r ∧
        componentQuotientMatrix
            ((secondOrderDefectGraph G).induce c.supp) (G.induce c.supp) b a = r ∧
        componentQuotientMatrix
            ((secondOrderDefectGraph G).induce c.supp) (G.induce c.supp) b b = 7 - r := by
  rcases orderSixtyFour_sizeTwo_muNegThree_disconnected_cycleQuotient_reduction
      G hfree hreg hcard c hc s hs_out hs_in hH a b hab with h610 | h106 | h88
  · exact False.elim <| orderSixtyFour_sizeTwo_muNegOne_sixTen_false
      G hfree hreg hcard c hc s hs_out hs_in hH hD a b h610.1 h610.2.1
  · exact False.elim <| orderSixtyFour_sizeTwo_muNegOne_sixTen_false
      G hfree hreg hcard c hc s hs_out hs_in hH hD b a h106.2.1 h106.1
  · exact h88

end

end Erdos85

#print axioms Erdos85.orderSixtyFour_sizeTwo_muNegOne_distinctCycles_eightEight
