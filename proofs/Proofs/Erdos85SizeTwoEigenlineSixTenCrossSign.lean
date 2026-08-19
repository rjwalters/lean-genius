import Proofs.Erdos85SizeTwoEigenlineSixTenShortCycleRigidity

/-!
# Cross-sign rigidity in the q=8 six-plus-ten stratum

Node: `SIZE-TWO-EIGENLINE(8)` beneath outline F.3.

Every vertex of a size-two component has exactly two opposite-sign defect
neighbors.  On the forced all-triangle-free six-cycle, its two ambient cycle
neighbors are precisely its two internal defect neighbors, and alternation
makes both opposite-sign.  They therefore exhaust the global opposite-sign
defect neighborhood: every defect edge from the six-cycle to the ten-cycle
preserves the eigenline sign.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

theorem binarySquare_regular_sizeTwoPart_eight_sixTen_cross_defect_preserves_sign
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
    (hDs : ∀ x, ∑ y ∈ (secondOrderDefectGraph G).neighborFinset x, s y =
      3 * s x)
    (a b : (G.induce c.supp).ConnectedComponent)
    (ha : a.supp.ncard = 6) (hb : b.supp.ncard = 10)
    (x y : c.supp) (hx : x ∈ a.supp) (hy : y ∈ b.supp)
    (hxy : ((secondOrderDefectGraph G).induce c.supp).Adj x y) :
    s y.1 = s x.1 := by
  classical
  let H := G.induce c.supp
  let D := secondOrderDefectGraph G
  let internalVals : Finset V := (H.neighborFinset x).image Subtype.val
  let opposite : Finset V := (D.neighborFinset x.1).filter fun z => s z = -s x.1
  have hHdegree : ∀ z : c.supp, H.degree z = 2 := by
    intro z
    exact binarySquare_regular_degree_induce_defectComponent_eq_part
      G hfree (by omega) hreg hcard c (m := 2)
        (by simpa [Nat.mul_comm] using hc) z
  have hinterCard : internalVals.card = 2 := by
    rw [Finset.card_image_of_injective _ Subtype.val_injective]
    exact H.card_neighborFinset_eq_degree x |>.trans (hHdegree x)
  have hoppCard : opposite.card = 2 := by
    simpa [opposite, D] using
      (sameSide_defect_degree G hfree (q := 8) (by omega) hreg hcard c s
        hs_in hDs x.2).2
  have hinterSub : internalVals ⊆ opposite := by
    intro z hz
    simp only [internalVals, Finset.mem_image] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    have hHw : H.Adj x w := (H.mem_neighborFinset x w).mp hw
    have hKw :=
      (binarySquare_regular_sizeTwoPart_eight_sixTen_shortCycle_defectAdj_iff
        G hfree hreg hcard c hc s hs_in hs_out hA_in a b ha hb
          x w hx ((a.mem_supp_congr_adj hHw).mp hx)).2 hHw
    have hflip : s w.1 = -s x.1 := by
      have hwComp : w.1 ∈ componentNeighborFinset G D c x.1 := by
        rw [componentNeighborFinset, Finset.mem_filter]
        exact ⟨(G.mem_neighborFinset _ _).mpr hHw, w.2⟩
      exact (internal_alternation G hfree (by omega) hreg hcard c hc s
        hs_in hs_out hA_in x.2).2 w.1 hwComp
    simp only [opposite, Finset.mem_filter]
    exact ⟨(D.mem_neighborFinset x.1 w.1).mpr hKw, hflip⟩
  have hinterEq : internalVals = opposite :=
    Finset.eq_of_subset_of_card_le hinterSub (by omega)
  by_contra hsign
  have hySign : s y.1 = -s x.1 := by
    rcases hs_in y.1 y.2 with hyNeg | hyPos <;>
      rcases hs_in x.1 x.2 with hxNeg | hxPos <;> simp_all
  have hyOpp : y.1 ∈ opposite := by
    simp only [opposite, Finset.mem_filter]
    exact ⟨(D.mem_neighborFinset x.1 y.1).mpr hxy, hySign⟩
  rw [← hinterEq] at hyOpp
  simp only [internalVals, Finset.mem_image] at hyOpp
  obtain ⟨w, hw, hwy⟩ := hyOpp
  have hwa : w ∈ a.supp := (a.mem_supp_congr_adj
    ((H.mem_neighborFinset x w).mp hw).symm).mpr hx
  have hwy' : w = y := Subtype.ext hwy
  have hya : y ∈ a.supp := by simpa [hwy'] using hwa
  have hab : a = b :=
    ((ConnectedComponent.mem_supp_iff a y).mp hya).symm.trans
      ((ConnectedComponent.mem_supp_iff b y).mp hy)
  rw [hab] at ha
  omega

/-- At every vertex of the ten-cycle, the three quotient-prescribed defect
neighbors in the six-cycle are all same-sign. -/
theorem binarySquare_regular_sizeTwoPart_eight_sixTen_longVertex_three_sameSign_cross
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
    (hDs : ∀ x, ∑ y ∈ (secondOrderDefectGraph G).neighborFinset x, s y =
      3 * s x)
    (a b : (G.induce c.supp).ConnectedComponent)
    (ha : a.supp.ncard = 6) (hb : b.supp.ncard = 10)
    (y : c.supp) (hy : y ∈ b.supp) :
    ((componentNeighborFinset
        ((secondOrderDefectGraph G).induce c.supp) (G.induce c.supp) a y).filter
      fun x => s x.1 = s y.1).card = 3 := by
  classical
  let H := G.induce c.supp
  let K := (secondOrderDefectGraph G).induce c.supp
  have hHdegree : ∀ z : c.supp, H.degree z = 2 := by
    intro z
    exact binarySquare_regular_degree_induce_defectComponent_eq_part
      G hfree (by omega) hreg hcard c (m := 2)
        (by simpa [Nat.mul_comm] using hc) z
  have hcommReal : K.adjMatrix ℝ * H.adjMatrix ℝ =
      H.adjMatrix ℝ * K.adjMatrix ℝ := by
    have hglobal := adjMatrix_comm_secondOrderDefect_of_regular_field
      (K := ℝ) G hfree hreg
    exact (induce_component_adjMatrix_comm_of_comm
      G (secondOrderDefectGraph G) hglobal c).symm
  have hcrossCard : (componentNeighborFinset K H a y).card = 3 := by
    rw [← componentQuotientMatrix_apply_eq K H 2 hHdegree hcommReal b a hy]
    exact (binarySquare_regular_sizeTwoPart_eight_sixTen_cycleQuotient
      G hfree hreg hcard c hc s hs_in hs_out hA_in a b ha hb).2.2.1
  have hall : ∀ x ∈ componentNeighborFinset K H a y, s x.1 = s y.1 := by
    intro x hx
    have hxmem : x ∈ a.supp := by
      exact (ConnectedComponent.mem_supp_iff a x).mpr
        (Finset.mem_filter.mp hx).2
    have hxy : K.Adj x y := by
      exact (K.mem_neighborFinset y x).mp (Finset.mem_filter.mp hx).1 |>.symm
    exact (binarySquare_regular_sizeTwoPart_eight_sixTen_cross_defect_preserves_sign
      G hfree hreg hcard c hc s hs_in hs_out hA_in hDs a b ha hb
        x y hxmem hy hxy).symm
  rw [Finset.filter_eq_self.mpr hall, hcrossCard]

end

end Erdos85

#print axioms Erdos85.binarySquare_regular_sizeTwoPart_eight_sixTen_cross_defect_preserves_sign
#print axioms Erdos85.binarySquare_regular_sizeTwoPart_eight_sixTen_longVertex_three_sameSign_cross
