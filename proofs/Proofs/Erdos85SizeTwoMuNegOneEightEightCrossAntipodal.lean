import Proofs.Erdos85SizeTwoMuNegThreeEightEightCrossAntipodal
import Proofs.Erdos85SizeTwoMuNegOneEightEightReduction

/-! # Cross-component defect edges are antipodal in the `mu=-1` stratum -/

open Finset SimpleGraph Matrix

namespace Erdos85

noncomputable section

set_option maxHeartbeats 800000 in
/-- In the `mu=-1` C8+C8 stratum, the cross quotient `r` is the exact
cross-antipodal degree in both directions. -/
theorem orderSixtyFour_sizeTwo_muNegOne_eightEight_crossAntipodal_degree
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
    ∃ r : ℕ, 2 ≤ r ∧ r ≤ 7 ∧
      (∀ x : c.supp, x ∈ a.supp →
        ((((Finset.univ : Finset c.supp).filter fun y ↦ y ∈ b.supp).filter
          fun y ↦ (antipodalGraph G).Adj x.1 y.1).card = r)) ∧
      (∀ y : c.supp, y ∈ b.supp →
        ((((Finset.univ : Finset c.supp).filter fun x ↦ x ∈ a.supp).filter
          fun x ↦ (antipodalGraph G).Adj y.1 x.1).card = r)) := by
  classical
  let Hc := G.induce c.supp
  let K := (secondOrderDefectGraph G).induce c.supp
  obtain ⟨_ha8, _hb8, r, hr2, hr7, _haa, habq, hbaq, _hbb⟩ :=
    orderSixtyFour_sizeTwo_muNegOne_distinctCycles_eightEight
      G hfree hreg hcard c hc s hs_out hs_in hH hD a b hab
  have hHdegree : ∀ z : c.supp, Hc.degree z = 2 := by
    intro z
    exact binarySquare_regular_degree_induce_defectComponent_eq_part
      G hfree (by omega) hreg hcard c (m := 2)
        (by simpa [Nat.mul_comm] using hc) z
  have hcommReal : K.adjMatrix ℝ * Hc.adjMatrix ℝ =
      Hc.adjMatrix ℝ * K.adjMatrix ℝ := by
    have hglobal := adjMatrix_comm_secondOrderDefect_of_regular_field
      (K := ℝ) G hfree hreg
    exact (induce_component_adjMatrix_comm_of_comm G
      (secondOrderDefectGraph G) hglobal c).symm
  refine ⟨r, hr2, hr7, ?_, ?_⟩
  · intro x hxa
    have hq : (componentNeighborFinset K Hc b x).card = r := by
      rw [← componentQuotientMatrix_apply_eq K Hc 2 hHdegree hcommReal
        a b hxa]
      exact habq
    rw [← hq]
    congr 1
    ext y
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      componentNeighborFinset, SimpleGraph.mem_neighborFinset]
    constructor
    · rintro ⟨hyb, hanti⟩
      exact ⟨(secondOrderDefect_cross_internalComponents_iff_antipodal
        G c a b hab x y hxa hyb).2 hanti, hyb⟩
    · rintro ⟨hK, hyb⟩
      exact ⟨hyb, (secondOrderDefect_cross_internalComponents_iff_antipodal
        G c a b hab x y hxa hyb).1 hK⟩
  · intro y hyb
    have hq : (componentNeighborFinset K Hc a y).card = r := by
      rw [← componentQuotientMatrix_apply_eq K Hc 2 hHdegree hcommReal
        b a hyb]
      exact hbaq
    rw [← hq]
    congr 1
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      componentNeighborFinset, SimpleGraph.mem_neighborFinset]
    constructor
    · rintro ⟨hxa, hanti⟩
      have hanti' : (antipodalGraph G).Adj x.1 y.1 := hanti.symm
      exact ⟨(secondOrderDefect_cross_internalComponents_iff_antipodal
        G c a b hab x y hxa hyb).2 hanti' |>.symm, hxa⟩
    · rintro ⟨hK, hxa⟩
      have hK' : K.Adj x y := hK.symm
      have hanti' := (secondOrderDefect_cross_internalComponents_iff_antipodal
        G c a b hab x y hxa hyb).1 hK'
      exact ⟨hxa, hanti'.symm⟩

end


end Erdos85

#print axioms Erdos85.orderSixtyFour_sizeTwo_muNegOne_eightEight_crossAntipodal_degree
