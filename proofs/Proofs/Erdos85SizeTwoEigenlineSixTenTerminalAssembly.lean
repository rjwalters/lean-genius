import Proofs.Erdos85SizeTwoEigenlineSixTenSectorCases

/-!
# Exhaustive terminal assembly for the `6+10` stratum

Node: `SIZE-TWO-EIGENLINE(8)` beneath outline F.3.

The structural sector split has exactly two leaves: the short C6 is always
all-triangle-free, while the long C10 is either all-triangle (mixed branch)
or all-triangle-free.  This capstone exposes one graph-facing terminal socket
for each checked owner certificate.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- Supplying contradictions for the mixed and both-all-triangle-free
terminal packages closes the entire `6+10` stratum. -/
theorem binarySquare_regular_sizeTwoPart_eight_sixTen_false_of_terminals
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
    (hMixed :
      (∀ x : c.supp, x ∈ a.supp →
        (triangleFreeEdgeGraph G).degree x.1 = 2) →
      (∀ x : c.supp, x ∈ b.supp →
        (triangleFreeEdgeGraph G).degree x.1 = 0) → False)
    (hBothAllTf :
      (∀ x : c.supp, x ∈ a.supp →
        (triangleFreeEdgeGraph G).degree x.1 = 2) →
      (∀ x : c.supp, x ∈ b.supp →
        (triangleFreeEdgeGraph G).degree x.1 = 2) → False) :
    False := by
  obtain ⟨hshort, hlong | hlong⟩ :=
    binarySquare_regular_sizeTwoPart_eight_sixTen_sector_cases
      G hfree hreg hcard c hc s hs_in hs_out hA_in a b ha hb
  · exact hMixed hshort hlong
  · exact hBothAllTf hshort hlong

end

end Erdos85

#print axioms Erdos85.binarySquare_regular_sizeTwoPart_eight_sixTen_false_of_terminals
