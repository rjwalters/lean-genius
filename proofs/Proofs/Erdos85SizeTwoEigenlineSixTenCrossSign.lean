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

/-- The four defect neighbors of a long-cycle vertex inside the long cycle
split into exactly two same-sign and two opposite-sign vertices. -/
theorem binarySquare_regular_sizeTwoPart_eight_sixTen_longDiagonal_signSplit
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
    (((componentNeighborFinset
        ((secondOrderDefectGraph G).induce c.supp) (G.induce c.supp) b y).filter
      fun z => s z.1 = s y.1).card = 2) ∧
    (((componentNeighborFinset
        ((secondOrderDefectGraph G).induce c.supp) (G.induce c.supp) b y).filter
      fun z => s z.1 = -s y.1).card = 2) := by
  classical
  let H := G.induce c.supp
  let D := secondOrderDefectGraph G
  let K := D.induce c.supp
  let A := componentNeighborFinset K H a y
  let B := componentNeighborFinset K H b y
  have hab : a ≠ b := by
    intro h
    rw [h] at ha
    omega
  have hHdegree : ∀ z : c.supp, H.degree z = 2 := by
    intro z
    exact binarySquare_regular_degree_induce_defectComponent_eq_part
      G hfree (by omega) hreg hcard c (m := 2)
        (by simpa [Nat.mul_comm] using hc) z
  have hcommReal : K.adjMatrix ℝ * H.adjMatrix ℝ =
      H.adjMatrix ℝ * K.adjMatrix ℝ := by
    have hglobal := adjMatrix_comm_secondOrderDefect_of_regular_field
      (K := ℝ) G hfree hreg
    exact (induce_component_adjMatrix_comm_of_comm G D hglobal c).symm
  obtain ⟨hAA, hAB, hBA, hBB⟩ :=
    binarySquare_regular_sizeTwoPart_eight_sixTen_cycleQuotient
      G hfree hreg hcard c hc s hs_in hs_out hA_in a b ha hb
  have hAcard : A.card = 3 := by
    rw [← componentQuotientMatrix_apply_eq K H 2 hHdegree hcommReal b a hy]
    exact hBA
  have hBcard : B.card = 4 := by
    rw [← componentQuotientMatrix_apply_eq K H 2 hHdegree hcommReal b b hy]
    exact hBB
  have hAdisjB : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro z hzA hzB
    have hza := (Finset.mem_filter.mp hzA).2
    have hzb := (Finset.mem_filter.mp hzB).2
    exact hab (hza.symm.trans hzb)
  have hUnionSub : A ∪ B ⊆ K.neighborFinset y := by
    intro z hz
    rcases Finset.mem_union.mp hz with hz | hz <;>
      exact (Finset.mem_filter.mp hz).1
  have hKcard : (K.neighborFinset y).card = 7 := by
    rw [K.card_neighborFinset_eq_degree, degree_induce_connectedComponent_supp]
    exact defect_degree G hfree (by omega) hreg hcard y.1
  have hUnion : A ∪ B = K.neighborFinset y := by
    apply Finset.eq_of_subset_of_card_le hUnionSub
    rw [Finset.card_union_of_disjoint hAdisjB, hAcard, hBcard, hKcard]
  let KVals : Finset V := (K.neighborFinset y).image Subtype.val
  have hKValsSub : KVals ⊆ D.neighborFinset y.1 := by
    intro z hz
    simp only [KVals, Finset.mem_image] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    exact (D.mem_neighborFinset y.1 w.1).mpr
      ((K.mem_neighborFinset y w).mp hw)
  have hKValsCard : KVals.card = 7 := by
    rw [Finset.card_image_of_injective _ Subtype.val_injective, hKcard]
  have hDcard : (D.neighborFinset y.1).card = 7 := by
    rw [D.card_neighborFinset_eq_degree]
    exact defect_degree G hfree (by omega) hreg hcard y.1
  have hKValsEq : KVals = D.neighborFinset y.1 :=
    Finset.eq_of_subset_of_card_le hKValsSub (by omega)
  have hKsame : ((K.neighborFinset y).filter fun z => s z.1 = s y.1).card = 5 := by
    have himage : (((K.neighborFinset y).filter fun z => s z.1 = s y.1).image
        Subtype.val) = (D.neighborFinset y.1).filter fun z => s z = s y.1 := by
      ext z
      constructor
      · simp only [Finset.mem_image, Finset.mem_filter]
        rintro ⟨w, ⟨hw, hsign⟩, rfl⟩
        have hwKV : w.1 ∈ KVals := by
          exact Finset.mem_image.mpr ⟨w, hw, rfl⟩
        exact ⟨hKValsSub hwKV, hsign⟩
      · intro hz
        have hzD := (Finset.mem_filter.mp hz).1
        have hzSign := (Finset.mem_filter.mp hz).2
        rw [← hKValsEq] at hzD
        simp only [KVals, Finset.mem_image] at hzD
        obtain ⟨w, hw, rfl⟩ := hzD
        exact Finset.mem_image.mpr
          ⟨w, Finset.mem_filter.mpr ⟨hw, hzSign⟩, rfl⟩
    rw [← Finset.card_image_of_injective _ Subtype.val_injective, himage]
    simpa [D] using
      (sameSide_defect_degree G hfree (q := 8) (by omega) hreg hcard c s
        hs_in hDs y.2).1
  have hAsame : (A.filter fun z => s z.1 = s y.1).card = 3 := by
    simpa [A, K, H] using
      binarySquare_regular_sizeTwoPart_eight_sixTen_longVertex_three_sameSign_cross
        G hfree hreg hcard c hc s hs_in hs_out hA_in hDs a b ha hb y hy
  have hBsame : (B.filter fun z => s z.1 = s y.1).card = 2 := by
    have hsplit :
        (A.filter fun z => s z.1 = s y.1).card +
          (B.filter fun z => s z.1 = s y.1).card = 5 := by
      rw [← Finset.card_union_of_disjoint
        (hAdisjB.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _))]
      rw [← Finset.filter_union, hUnion, hKsame]
    omega
  have hsignUnion :
      (B.filter fun z => s z.1 = s y.1) ∪
        (B.filter fun z => s z.1 = -s y.1) = B := by
    ext z
    simp only [Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (⟨hz, _⟩ | ⟨hz, _⟩) <;> exact hz
    · intro hz
      rcases hs_in z.1 z.2 with hzNeg | hzPos <;>
        rcases hs_in y.1 y.2 with hyNeg | hyPos <;> simp_all
  have hsignDisj : Disjoint
      (B.filter fun z => s z.1 = s y.1)
      (B.filter fun z => s z.1 = -s y.1) := by
    rw [Finset.disjoint_left]
    intro z hzSame hzOpp
    have hsame := (Finset.mem_filter.mp hzSame).2
    have hopp := (Finset.mem_filter.mp hzOpp).2
    rcases hs_in y.1 y.2 with hyNeg | hyPos <;> simp_all
  have hBopp : (B.filter fun z => s z.1 = -s y.1).card = 2 := by
    have := Finset.card_union_of_disjoint hsignDisj
    rw [hsignUnion, hBsame, hBcard] at this
    omega
  exact ⟨by simpa [B, K, H] using hBsame,
    by simpa [B, K, H] using hBopp⟩

end

end Erdos85

#print axioms Erdos85.binarySquare_regular_sizeTwoPart_eight_sixTen_cross_defect_preserves_sign
#print axioms Erdos85.binarySquare_regular_sizeTwoPart_eight_sixTen_longVertex_three_sameSign_cross
#print axioms Erdos85.binarySquare_regular_sizeTwoPart_eight_sixTen_longDiagonal_signSplit
