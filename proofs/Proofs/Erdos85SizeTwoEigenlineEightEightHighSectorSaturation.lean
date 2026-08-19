import Proofs.Erdos85SizeTwoEigenlineEightEightSectorTrichotomy

/-!
# Local saturation in the high eight-plus-eight sector

Node: `SIZE-TWO-EIGENLINE(8)` beneath outline F.3.

When the quotient parameter is at least six, both internal eight-cycles are
all-triangle.  This wrapper also turns the four quotient entries into exact
per-vertex defect-neighbour counts: every vertex has `7-r` neighbours in its
own cycle and `r` in the other cycle, where `r` is six or seven.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- The high `8+8` sector is locally saturated by a parameter `r ∈ {6,7}`.
Both cycles are all-triangle, and every row of either diagonal/cross defect
block has the corresponding exact quotient weight. -/
theorem binarySquare_regular_sizeTwoPart_eight_eightEight_highSector_localSaturation
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
    (ha : a.supp.ncard = 8) (hb : b.supp.ncard = 8) (hab : a ≠ b)
    (hrHigh : ∀ r : ℕ,
      componentQuotientMatrix
          ((secondOrderDefectGraph G).induce c.supp) (G.induce c.supp) a b = r →
      6 ≤ r) :
    ∃ r : ℕ, 6 ≤ r ∧ r ≤ 7 ∧
      (∀ x : c.supp, x ∈ a.supp →
        (triangleFreeEdgeGraph G).degree x.1 = 0) ∧
      (∀ x : c.supp, x ∈ b.supp →
        (triangleFreeEdgeGraph G).degree x.1 = 0) ∧
      (∀ x : c.supp, x ∈ a.supp →
        (componentNeighborFinset
          ((secondOrderDefectGraph G).induce c.supp) (G.induce c.supp) a x).card =
            7 - r) ∧
      (∀ x : c.supp, x ∈ a.supp →
        (componentNeighborFinset
          ((secondOrderDefectGraph G).induce c.supp) (G.induce c.supp) b x).card =
            r) ∧
      (∀ x : c.supp, x ∈ b.supp →
        (componentNeighborFinset
          ((secondOrderDefectGraph G).induce c.supp) (G.induce c.supp) a x).card =
            r) ∧
      (∀ x : c.supp, x ∈ b.supp →
        (componentNeighborFinset
          ((secondOrderDefectGraph G).induce c.supp) (G.induce c.supp) b x).card =
            7 - r) := by
  classical
  let H := G.induce c.supp
  let K := (secondOrderDefectGraph G).induce c.supp
  obtain ⟨r, _hr2, hr7, haa, habq, hbaq, hbb, hsector⟩ :=
    binarySquare_regular_sizeTwoPart_eight_eightEight_sectorTrichotomy
      G hfree hreg hcard c hc s hs_in hs_out hA_in a b ha hb hab
  have hr6 : 6 ≤ r := hrHigh r habq
  have hallA : ∀ x : c.supp, x ∈ a.supp →
      (triangleFreeEdgeGraph G).degree x.1 = 0 := by
    rcases hsector with hlow | hmid | hhigh
    · omega
    · omega
    · exact hhigh.2.1
  have hallB : ∀ x : c.supp, x ∈ b.supp →
      (triangleFreeEdgeGraph G).degree x.1 = 0 := by
    rcases hsector with hlow | hmid | hhigh
    · omega
    · omega
    · exact hhigh.2.2
  have hHdegree : ∀ z : c.supp, H.degree z = 2 := by
    intro z
    exact binarySquare_regular_degree_induce_defectComponent_eq_part
      G hfree (by omega) hreg hcard c (m := 2)
        (by simpa [Nat.mul_comm] using hc) z
  have hcomm : K.adjMatrix ℝ * H.adjMatrix ℝ =
      H.adjMatrix ℝ * K.adjMatrix ℝ := by
    have hglobal := adjMatrix_comm_secondOrderDefect_of_regular_field
      (K := ℝ) G hfree hreg
    exact (induce_component_adjMatrix_comm_of_comm G
      (secondOrderDefectGraph G) hglobal c).symm
  have hlocal (d e : H.ConnectedComponent) (x : c.supp) (hx : x ∈ d.supp) :
      (componentNeighborFinset K H e x).card =
        componentQuotientMatrix K H d e := by
    rw [componentQuotientMatrix_apply_eq K H 2 hHdegree hcomm d e hx]
  refine ⟨r, hr6, hr7, hallA, hallB, ?_, ?_, ?_, ?_⟩
  · intro x hx
    rw [hlocal a a x hx]
    exact haa
  · intro x hx
    rw [hlocal a b x hx]
    exact habq
  · intro x hx
    rw [hlocal b a x hx]
    exact hbaq
  · intro x hx
    rw [hlocal b b x hx]
    exact hbb

end

end Erdos85

#print axioms Erdos85.binarySquare_regular_sizeTwoPart_eight_eightEight_highSector_localSaturation
