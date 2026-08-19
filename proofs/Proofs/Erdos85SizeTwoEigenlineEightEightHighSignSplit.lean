import Proofs.Erdos85SizeTwoEigenlineEightEightHighParameterSix

/-!
# Exact sign split in the high eight-plus-eight sector

Node: `SIZE-TWO-EIGENLINE(8)` beneath outline F.3.

At the forced high parameter `r=6`, each vertex has one diagonal and six
cross defect neighbours.  The opposite alternating eight-cycle contains
only four vertices of the same sign, while the global ledger requires five
same-sign defect neighbours.  Hence the diagonal neighbour is same-sign and
the cross block splits `4+2` by sign.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

set_option maxHeartbeats 800000

/-- On the first cycle of a coordinated `8+8` component with cross quotient
six, the diagonal defect row has sign split `1+0` and the cross row has split
`4+2` (same/opposite). -/
theorem binarySquare_regular_sizeTwoPart_eight_eightEight_parameterSix_firstCycle_signSplit
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
    (ha : a.supp.ncard = 8) (hb : b.supp.ncard = 8) (hab : a ≠ b)
    (u v : ZMod 8 → c.supp)
    (huinj : Function.Injective u) (hvinj : Function.Injective v)
    (hurange : Set.range u = a.supp) (hvrange : Set.range v = b.supp)
    (hu : ∀ z, (G.induce c.supp).neighborFinset (u z) =
      {u (z - 1), u (z + 1)})
    (hv : ∀ z, (G.induce c.supp).neighborFinset (v z) =
      {v (z - 1), v (z + 1)})
    (hab6 : componentQuotientMatrix
      ((secondOrderDefectGraph G).induce c.supp) (G.induce c.supp) a b = 6) :
    ∀ i : ZMod 8,
      (((componentNeighborFinset
          ((secondOrderDefectGraph G).induce c.supp) (G.induce c.supp) a (u i)).filter
        fun z => s z.1 = s (u i).1).card = 1) ∧
      (((componentNeighborFinset
          ((secondOrderDefectGraph G).induce c.supp) (G.induce c.supp) a (u i)).filter
        fun z => s z.1 = -s (u i).1).card = 0) ∧
      (((componentNeighborFinset
          ((secondOrderDefectGraph G).induce c.supp) (G.induce c.supp) b (u i)).filter
        fun z => s z.1 = s (u i).1).card = 4) ∧
      (((componentNeighborFinset
          ((secondOrderDefectGraph G).induce c.supp) (G.induce c.supp) b (u i)).filter
        fun z => s z.1 = -s (u i).1).card = 2) := by
  classical
  let H := G.induce c.supp
  let D := secondOrderDefectGraph G
  let K := D.induce c.supp
  have hHdegree : ∀ z : c.supp, H.degree z = 2 := by
    intro z
    exact binarySquare_regular_degree_induce_defectComponent_eq_part
      G hfree (by omega) hreg hcard c (m := 2)
        (by simpa [Nat.mul_comm] using hc) z
  have hcomm : K.adjMatrix ℝ * H.adjMatrix ℝ =
      H.adjMatrix ℝ * K.adjMatrix ℝ := by
    have hglobal := adjMatrix_comm_secondOrderDefect_of_regular_field
      (K := ℝ) G hfree hreg
    exact (induce_component_adjMatrix_comm_of_comm G D hglobal c).symm
  -- Recover the diagonal quotient from the row sum at the fixed parameter.
  obtain ⟨r, _hr2, _hr7, haa, habq, _hbaq', _hbb'⟩ :=
    binarySquare_regular_sizeTwoPart_eight_eightEight_cycleQuotient
      G hfree hreg hcard c hc s hs_in hs_out hA_in a b ha hb hab
  have hr : r = 6 := by omega
  have haa1 : componentQuotientMatrix K H a a = 1 := by
    simpa [K, H, hr] using haa
  intro i
  let x : c.supp := u i
  let A := componentNeighborFinset K H a x
  let B := componentNeighborFinset K H b x
  have hxA : x ∈ a.supp := by
    rw [← hurange]
    exact ⟨i, rfl⟩
  have hAcard : A.card = 1 := by
    rw [← componentQuotientMatrix_apply_eq K H 2 hHdegree hcomm a a hxA]
    exact haa1
  have hBcard : B.card = 6 := by
    rw [← componentQuotientMatrix_apply_eq K H 2 hHdegree hcomm a b hxA]
    simpa [K, H] using hab6
  have hAdisjB : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro z hzA hzB
    have hza := (Finset.mem_filter.mp hzA).2
    have hzb := (Finset.mem_filter.mp hzB).2
    exact hab (hza.symm.trans hzb)
  have hUnionSub : A ∪ B ⊆ K.neighborFinset x := by
    intro z hz
    rcases Finset.mem_union.mp hz with hz | hz <;>
      exact (Finset.mem_filter.mp hz).1
  have hKcard : (K.neighborFinset x).card = 7 := by
    rw [K.card_neighborFinset_eq_degree, degree_induce_connectedComponent_supp]
    exact defect_degree G hfree (by omega) hreg hcard x.1
  have hUnion : A ∪ B = K.neighborFinset x := by
    apply Finset.eq_of_subset_of_card_le hUnionSub
    rw [Finset.card_union_of_disjoint hAdisjB, hAcard, hBcard, hKcard]
  let KVals : Finset V := (K.neighborFinset x).image Subtype.val
  have hKValsSub : KVals ⊆ D.neighborFinset x.1 := by
    intro z hz
    simp only [KVals, Finset.mem_image] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    exact (D.mem_neighborFinset x.1 w.1).mpr
      ((K.mem_neighborFinset x w).mp hw)
  have hKValsEq : KVals = D.neighborFinset x.1 := by
    apply Finset.eq_of_subset_of_card_le hKValsSub
    rw [Finset.card_image_of_injective _ Subtype.val_injective, hKcard,
      D.card_neighborFinset_eq_degree]
    have hd := defect_degree G hfree (by omega) hreg hcard x.1
    change D.degree x.1 = 7 at hd
    omega
  have hKsame : ((K.neighborFinset x).filter fun z => s z.1 = s x.1).card = 5 := by
    have himage : (((K.neighborFinset x).filter fun z => s z.1 = s x.1).image
        Subtype.val) = (D.neighborFinset x.1).filter fun z => s z = s x.1 := by
      ext z
      constructor
      · simp only [Finset.mem_image, Finset.mem_filter]
        rintro ⟨w, ⟨hw, hsign⟩, rfl⟩
        exact ⟨hKValsSub (Finset.mem_image.mpr ⟨w, hw, rfl⟩), hsign⟩
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
        hs_in hDs x.2).1
  have hsplit :
      (A.filter fun z => s z.1 = s x.1).card +
        (B.filter fun z => s z.1 = s x.1).card = 5 := by
    rw [← Finset.card_union_of_disjoint
      (hAdisjB.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _))]
    rw [← Finset.filter_union, hUnion, hKsame]
  have hvflip : ∀ j : ZMod 8, s (v (j + 1)).1 = -s (v j).1 := by
    intro j
    have hH : H.Adj (v j) (v (j + 1)) := by
      rw [← H.mem_neighborFinset, hv]
      simp
    have hmem : (v (j + 1)).1 ∈ componentNeighborFinset G D c (v j).1 := by
      rw [componentNeighborFinset, Finset.mem_filter]
      exact ⟨(G.mem_neighborFinset _ _).mpr hH, (v (j + 1)).2⟩
    exact (internal_alternation G hfree (by omega) hreg hcard c hc s
      hs_in hs_out hA_in (v j).2).2 _ hmem
  obtain ⟨hvSame, hvOpp⟩ := zmodEight_alternating_sign_filter_cards
    (fun j => s (v j).1) (fun j => hs_in _ (v j).2) hvflip
  let S : Finset c.supp := (Finset.univ.image v).filter fun z => s z.1 = s x.1
  have hBsubS : B.filter (fun z => s z.1 = s x.1) ⊆ S := by
    intro z hz
    have hzB := (Finset.mem_filter.mp hz).1
    have hzSign := (Finset.mem_filter.mp hz).2
    have hzb : z ∈ b.supp := (Finset.mem_filter.mp hzB).2
    rw [← hvrange] at hzb
    obtain ⟨j, rfl⟩ := hzb
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩, hzSign⟩
  have hScard : S.card = 4 := by
    have hfilterImage : S =
        ((Finset.univ : Finset (ZMod 8)).filter
          fun j => s (v j).1 = s x.1).image v := by
      ext z
      simp only [S, Finset.mem_filter, Finset.mem_image, Finset.mem_univ,
        true_and]
      constructor
      · rintro ⟨⟨j, _, rfl⟩, hj⟩
        exact ⟨j, hj, rfl⟩
      · rintro ⟨j, hj, rfl⟩
        exact ⟨⟨j, rfl⟩, hj⟩
    rw [hfilterImage, Finset.card_image_of_injective _ hvinj]
    rcases hs_in x.1 x.2 with hxNeg | hxPos <;>
      rcases hs_in (v 0).1 (v 0).2 with hvNeg | hvPos <;>
      simp_all
  have hBsameLe : (B.filter fun z => s z.1 = s x.1).card ≤ 4 := by
    rw [← hScard]
    exact Finset.card_le_card hBsubS
  have hAsameLe : (A.filter fun z => s z.1 = s x.1).card ≤ 1 := by
    calc
      (A.filter fun z => s z.1 = s x.1).card ≤ A.card :=
        Finset.card_le_card (Finset.filter_subset _ _)
      _ = 1 := hAcard
  have hAsame : (A.filter fun z => s z.1 = s x.1).card = 1 := by omega
  have hBsame : (B.filter fun z => s z.1 = s x.1).card = 4 := by omega
  have signPartition (T : Finset c.supp) :
      (T.filter fun z => s z.1 = s x.1) ∪
        (T.filter fun z => s z.1 = -s x.1) = T := by
    ext z
    simp only [Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (⟨hz, _⟩ | ⟨hz, _⟩) <;> exact hz
    · intro hz
      rcases hs_in z.1 z.2 with hzNeg | hzPos <;>
        rcases hs_in x.1 x.2 with hxNeg | hxPos <;> simp_all
  have signDisjoint (T : Finset c.supp) : Disjoint
      (T.filter fun z => s z.1 = s x.1)
      (T.filter fun z => s z.1 = -s x.1) := by
    rw [Finset.disjoint_left]
    intro z hzSame hzOpp
    have hsame := (Finset.mem_filter.mp hzSame).2
    have hopp := (Finset.mem_filter.mp hzOpp).2
    rcases hs_in x.1 x.2 with hxNeg | hxPos <;> simp_all
  have hAopp : (A.filter fun z => s z.1 = -s x.1).card = 0 := by
    have h := Finset.card_union_of_disjoint (signDisjoint A)
    rw [signPartition A, hAsame, hAcard] at h
    omega
  have hBopp : (B.filter fun z => s z.1 = -s x.1).card = 2 := by
    have h := Finset.card_union_of_disjoint (signDisjoint B)
    rw [signPartition B, hBsame, hBcard] at h
    omega
  exact ⟨by simpa [A, K, H, x] using hAsame,
    by simpa [A, K, H, x] using hAopp,
    by simpa [B, K, H, x] using hBsame,
    by simpa [B, K, H, x] using hBopp⟩

end

end Erdos85

#print axioms Erdos85.binarySquare_regular_sizeTwoPart_eight_eightEight_parameterSix_firstCycle_signSplit
