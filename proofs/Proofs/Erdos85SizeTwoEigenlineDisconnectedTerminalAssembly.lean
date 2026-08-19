import Proofs.Erdos85SizeTwoEigenlineDisconnectedEightReduction
import Proofs.Erdos85SizeTwoEigenlineSixTenTerminalAssembly
import Proofs.Erdos85SizeTwoEigenlineEightEightTerminalAssembly

/-!
# Terminal assembly for a disconnected order-64 size-two component

Node: `SIZE-TWO-EIGENLINE(8)` beneath outline F.3.

The internal ambient two-factor has only the unordered cycle-size patterns
`6+10` and `8+8`.  This theorem removes the irrelevant orientation of the
`6+10` pair and exposes one callback for each stratum.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- A disconnected size-two component is impossible once the oriented
`6+10` and symmetric `8+8` quotient packages have graph-facing terminals. -/
theorem binarySquare_regular_sizeTwoPart_eight_disconnected_false_of_terminals
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
    (a b : (G.induce c.supp).ConnectedComponent) (hab : a ≠ b)
    (hSixTen : ∀ (x y : (G.induce c.supp).ConnectedComponent), x ≠ y →
      (x.supp.ncard = 6 ∧ y.supp.ncard = 10 ∧
        componentQuotientMatrix
            ((secondOrderDefectGraph G).induce c.supp) (G.induce c.supp) x x = 2 ∧
        componentQuotientMatrix
            ((secondOrderDefectGraph G).induce c.supp) (G.induce c.supp) x y = 5 ∧
        componentQuotientMatrix
            ((secondOrderDefectGraph G).induce c.supp) (G.induce c.supp) y x = 3 ∧
        componentQuotientMatrix
            ((secondOrderDefectGraph G).induce c.supp) (G.induce c.supp) y y = 4) →
      False)
    (hEightEight :
      (a.supp.ncard = 8 ∧ b.supp.ncard = 8 ∧
        ∃ r : ℕ, 2 ≤ r ∧ r ≤ 7 ∧
          componentQuotientMatrix
              ((secondOrderDefectGraph G).induce c.supp) (G.induce c.supp) a a = 7 - r ∧
          componentQuotientMatrix
              ((secondOrderDefectGraph G).induce c.supp) (G.induce c.supp) a b = r ∧
          componentQuotientMatrix
              ((secondOrderDefectGraph G).induce c.supp) (G.induce c.supp) b a = r ∧
          componentQuotientMatrix
              ((secondOrderDefectGraph G).induce c.supp) (G.induce c.supp) b b = 7 - r) →
      False) :
    False := by
  rcases binarySquare_regular_sizeTwoPart_eight_disconnected_cycleQuotient_reduction
      G hfree hreg hcard c hc s hs_in hs_out hA_in a b hab with
    h610 | h106 | h88
  · exact hSixTen a b hab h610
  · rcases h106 with ⟨ha10, hb6, haa4, hab3, hba5, hbb2⟩
    exact hSixTen b a hab.symm ⟨hb6, ha10, hbb2, hba5, hab3, haa4⟩
  · exact hEightEight h88

end

end Erdos85

#print axioms Erdos85.binarySquare_regular_sizeTwoPart_eight_disconnected_false_of_terminals
