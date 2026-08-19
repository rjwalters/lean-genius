import Proofs.Erdos85SizeTwoEigenlineSixTenCycleQuotient
import Proofs.Erdos85SizeTwoEigenlineEightEightCycleQuotient

/-!
# Exhaustive quotient reduction for disconnected q=8 size-two eigenlines

Node: `SIZE-TWO-EIGENLINE(8)` beneath outline F.3.

For any two distinct internal ambient cycles, parity and total order leave
only the ordered sizes `6+10`, `10+6`, or `8+8`.  This theorem packages the
corresponding exact quotient classifications into a single graph-facing
interface for the remaining disconnected spectral/sector argument.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

theorem binarySquare_regular_sizeTwoPart_eight_disconnected_cycleQuotient_reduction
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
  rcases binarySquare_regular_sizeTwoPart_eight_internalCycle_pair_sizes
      G hfree hreg hcard c hc s hs_in hs_out hA_in a b hab with
    habSizes | habSizes | habSizes
  · left
    rcases habSizes with ⟨ha, hb⟩
    exact ⟨ha, hb,
      binarySquare_regular_sizeTwoPart_eight_sixTen_cycleQuotient
        G hfree hreg hcard c hc s hs_in hs_out hA_in a b ha hb⟩
  · right; left
    rcases habSizes with ⟨ha, hb⟩
    obtain ⟨hbb, hba, hab', haa⟩ :=
      binarySquare_regular_sizeTwoPart_eight_sixTen_cycleQuotient
        G hfree hreg hcard c hc s hs_in hs_out hA_in b a hb ha
    exact ⟨ha, hb, haa, hab', hba, hbb⟩
  · right; right
    rcases habSizes with ⟨ha, hb⟩
    exact ⟨ha, hb,
      binarySquare_regular_sizeTwoPart_eight_eightEight_cycleQuotient
        G hfree hreg hcard c hc s hs_in hs_out hA_in a b ha hb hab⟩

end

end Erdos85

#print axioms Erdos85.binarySquare_regular_sizeTwoPart_eight_disconnected_cycleQuotient_reduction
