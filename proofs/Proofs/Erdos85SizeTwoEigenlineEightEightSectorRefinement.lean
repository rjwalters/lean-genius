import Proofs.Erdos85SizeTwoEigenlineAllTriangleCycleDiagonal
import Proofs.Erdos85SizeTwoEigenlineEightEightCycleQuotient

/-!
# Sector refinement for the q=8 eight-plus-eight cycle stratum

Node: `SIZE-TWO-EIGENLINE(8)` beneath outline F.3.

The one-parameter defect quotient of two internal eight-cycles is
`[[7-r,r],[r,7-r]]`.  On either cycle, the all-triangle sector has diagonal
entry at most three, so it forces `4 ≤ r`.  Thus a parameter below four
forces both cycles into the all-triangle-free sector.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- In the q=8 `8+8` stratum, each internal cycle is triangle-free or the
off-diagonal quotient parameter is at least four. -/
theorem binarySquare_regular_sizeTwoPart_eight_eightEight_sectorRefinement
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
    (ha : a.supp.ncard = 8) (hb : b.supp.ncard = 8) (hab : a ≠ b) :
    ∃ r : ℕ, 2 ≤ r ∧ r ≤ 7 ∧
      componentQuotientMatrix
          ((secondOrderDefectGraph G).induce c.supp) (G.induce c.supp) a a = 7 - r ∧
      componentQuotientMatrix
          ((secondOrderDefectGraph G).induce c.supp) (G.induce c.supp) a b = r ∧
      componentQuotientMatrix
          ((secondOrderDefectGraph G).induce c.supp) (G.induce c.supp) b a = r ∧
      componentQuotientMatrix
          ((secondOrderDefectGraph G).induce c.supp) (G.induce c.supp) b b = 7 - r ∧
      ((∀ x : c.supp, x ∈ a.supp →
          (triangleFreeEdgeGraph G).degree x.1 = 2) ∨ 4 ≤ r) ∧
      ((∀ x : c.supp, x ∈ b.supp →
          (triangleFreeEdgeGraph G).degree x.1 = 2) ∨ 4 ≤ r) := by
  obtain ⟨r, hr2, hr7, haa, habq, hbaq, hbb⟩ :=
    binarySquare_regular_sizeTwoPart_eight_eightEight_cycleQuotient
      G hfree hreg hcard c hc s hs_in hs_out hA_in a b ha hb hab
  have sector (d : (G.induce c.supp).ConnectedComponent)
      (hd : d.supp.ncard = 8)
      (hdd : componentQuotientMatrix
          ((secondOrderDefectGraph G).induce c.supp) (G.induce c.supp) d d = 7 - r) :
      (∀ x : c.supp, x ∈ d.supp →
          (triangleFreeEdgeGraph G).degree x.1 = 2) ∨ 4 ≤ r := by
    rcases binarySquare_regular_sizeTwoPart_internalCycle_sector_dichotomy
      G hfree (by omega) (by decide) hreg hcard c hc d with hall | htf
    · right
      have hle :=
        binarySquare_regular_sizeTwoPart_allTriangle_cycleQuotient_diagonal_le
          G hfree (by omega) hreg hcard c hc d (by omega) hall
      rw [hdd, hd] at hle
      omega
    · exact Or.inl htf
  exact ⟨r, hr2, hr7, haa, habq, hbaq, hbb,
    sector a ha haa, sector b hb hbb⟩

end

end Erdos85

#print axioms Erdos85.binarySquare_regular_sizeTwoPart_eight_eightEight_sectorRefinement
