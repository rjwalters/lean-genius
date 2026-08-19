import Proofs.Erdos85SizeTwoEigenlineAllTriangleFreeCrossSign
import Proofs.Erdos85AntipodalCycleReservoir

/-!
# Sign separation in the low eight-plus-eight sector

Node: `SIZE-TWO-EIGENLINE(8)` beneath outline F.3.

On an all-triangle-free internal cycle, its two ambient neighbors exhaust
the two opposite-sign defect neighbors.  Consequently every defect edge
which is not an internal ambient edge preserves the eigenline sign.  In
particular every antipodal edge incident with the cycle preserves sign.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- After an all-triangle-free internal cycle exhausts the opposite-sign
defect degree, every nonambient defect edge at that cycle preserves sign. -/
theorem binarySquare_regular_sizeTwoPart_allTriangleFree_nonambient_defect_preserves_sign
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 5 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hc : c.supp.ncard = q * 2)
    [DecidableEq (G.induce c.supp).ConnectedComponent]
    (s : V → ℤ)
    (hs_in : ∀ x ∈ c.supp, s x = -1 ∨ s x = 1)
    (hs_out : ∀ x ∉ c.supp, s x = 0)
    (hA_in : ∀ x ∈ c.supp,
      ∑ y ∈ G.neighborFinset x, s y = -2 * s x)
    (hDs : ∀ x, ∑ y ∈ (secondOrderDefectGraph G).neighborFinset x, s y =
      ((q : ℤ) - 5) * s x)
    (a : (G.induce c.supp).ConnectedComponent)
    (htf : ∀ z : c.supp, z ∈ a.supp →
      (triangleFreeEdgeGraph G).degree z.1 = 2)
    (x y : c.supp) (hx : x ∈ a.supp)
    (hxy : ((secondOrderDefectGraph G).induce c.supp).Adj x y)
    (hnotAmbient : ¬ (G.induce c.supp).Adj x y) :
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
      (sameSide_defect_degree G hfree hq hreg hcard c s hs_in hDs x.2).2
  have hinterSub : internalVals ⊆ opposite := by
    intro z hz
    simp only [internalVals, Finset.mem_image] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    have hHw : H.Adj x w := (H.mem_neighborFinset x w).mp hw
    have htfEdge : (triangleFreeEdgeGraph G).Adj x.1 w.1 :=
      sizeTwo_triangleFreeEdge_of_degree_two G c hHdegree x w hHw (htf x hx)
    have hKw : D.Adj x.1 w.1 := Or.inr htfEdge
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
  have hwy' : w = y := Subtype.ext hwy
  exact hnotAmbient (by
    simpa [H, hwy'] using (H.mem_neighborFinset x w).mp hw)

/-- Every antipodal edge incident with an all-triangle-free internal cycle
preserves the size-two eigenline sign. -/
theorem binarySquare_regular_sizeTwoPart_allTriangleFree_antipodal_preserves_sign
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 5 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hc : c.supp.ncard = q * 2)
    [DecidableEq (G.induce c.supp).ConnectedComponent]
    (s : V → ℤ)
    (hs_in : ∀ x ∈ c.supp, s x = -1 ∨ s x = 1)
    (hs_out : ∀ x ∉ c.supp, s x = 0)
    (hA_in : ∀ x ∈ c.supp,
      ∑ y ∈ G.neighborFinset x, s y = -2 * s x)
    (hDs : ∀ x, ∑ y ∈ (secondOrderDefectGraph G).neighborFinset x, s y =
      ((q : ℤ) - 5) * s x)
    (a : (G.induce c.supp).ConnectedComponent)
    (htf : ∀ z : c.supp, z ∈ a.supp →
      (triangleFreeEdgeGraph G).degree z.1 = 2)
    (x y : c.supp) (hx : x ∈ a.supp)
    (hxy : (antipodalGraph G).Adj x.1 y.1) :
    s y.1 = s x.1 := by
  apply binarySquare_regular_sizeTwoPart_allTriangleFree_nonambient_defect_preserves_sign
    G hfree hq hreg hcard c hc s hs_in hs_out hA_in hDs a htf x y hx
  · change (antipodalGraph G ⊔ triangleFreeEdgeGraph G).Adj x.1 y.1
    exact Or.inl hxy
  · exact fun hG =>
      ((mem_antipodalNeighbors G x.1 y.1).mp hxy).2.1 hG

/-- At an all-triangle-free vertex of the order-64 size-two component, the
five antipodal neighbors all remain in that defect component and in the
same eigenline sign class. -/
theorem binarySquare_regular_sizeTwoPart_eight_allTriangleFree_antipodal_degree_five_sign_support
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
    [DecidableEq (G.induce c.supp).ConnectedComponent]
    (s : V → ℤ)
    (hs_in : ∀ x ∈ c.supp, s x = -1 ∨ s x = 1)
    (hs_out : ∀ x ∉ c.supp, s x = 0)
    (hA_in : ∀ x ∈ c.supp,
      ∑ y ∈ G.neighborFinset x, s y = -2 * s x)
    (hDs : ∀ x, ∑ y ∈ (secondOrderDefectGraph G).neighborFinset x, s y =
      3 * s x)
    (a : (G.induce c.supp).ConnectedComponent)
    (htf : ∀ z : c.supp, z ∈ a.supp →
      (triangleFreeEdgeGraph G).degree z.1 = 2)
    (x : c.supp) (hx : x ∈ a.supp) :
    (antipodalGraph G).degree x.1 = 5 ∧
      ∀ y, (antipodalGraph G).Adj x.1 y →
        y ∈ c.supp ∧ s y = s x.1 := by
  constructor
  · have hcard64 : Fintype.card V = 64 := by norm_num at hcard ⊢; exact hcard
    have hdegree := antipodalGraph_degree_eq_excess_add_two_sub_triangleFree
      G hfree (d := 8) (e := 5) (by omega) hreg hcard64 x.1
    have hcardTf : (triangleFreeNeighbors G x.1).card =
        (triangleFreeEdgeGraph G).degree x.1 := by
      rw [← (triangleFreeEdgeGraph G).card_neighborFinset_eq_degree,
        triangleFreeEdgeGraph_neighborFinset]
    rw [hdegree, hcardTf, htf x hx]
  · intro y hxy
    have hD : (secondOrderDefectGraph G).Adj x.1 y := by
      change (antipodalGraph G ⊔ triangleFreeEdgeGraph G).Adj x.1 y
      exact Or.inl hxy
    have hyc : y ∈ c.supp := (c.mem_supp_congr_adj hD).mp x.2
    refine ⟨hyc, ?_⟩
    exact binarySquare_regular_sizeTwoPart_allTriangleFree_antipodal_preserves_sign
      G hfree (by omega) hreg hcard c hc s hs_in hs_out hA_in hDs a htf
        x ⟨y, hyc⟩ hx hxy

end

end Erdos85

#print axioms Erdos85.binarySquare_regular_sizeTwoPart_allTriangleFree_nonambient_defect_preserves_sign
#print axioms Erdos85.binarySquare_regular_sizeTwoPart_allTriangleFree_antipodal_preserves_sign
#print axioms Erdos85.binarySquare_regular_sizeTwoPart_eight_allTriangleFree_antipodal_degree_five_sign_support
