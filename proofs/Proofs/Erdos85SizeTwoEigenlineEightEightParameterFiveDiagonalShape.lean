import Proofs.Erdos85SizeTwoEigenlineEightEightMiddleSignSplit
import Proofs.Erdos85SizeTwoEigenlineEightEightHighAntipodalMatching
import Proofs.Erdos85ZModEightMixedSelfIntertwinerExclusion

/-! # The parameter-five diagonal shape in the 8+8 stratum -/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

set_option maxHeartbeats 800000

/-- At cross parameter five, every row on the first C8 has at least one
same-sign diagonal defect neighbor.  The global same-sign defect budget is
five, while the opposite C8 contains only four vertices of either sign. -/
theorem binarySquare_regular_sizeTwoPart_eight_eightEight_parameterFive_firstCycle_diagonalSame_pos
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
    (_huinj : Function.Injective u) (hvinj : Function.Injective v)
    (hurange : Set.range u = a.supp) (hvrange : Set.range v = b.supp)
    (_hu : ∀ z, (G.induce c.supp).neighborFinset (u z) =
      {u (z - 1), u (z + 1)})
    (hv : ∀ z, (G.induce c.supp).neighborFinset (v z) =
      {v (z - 1), v (z + 1)})
    (hab5 : componentQuotientMatrix
      ((secondOrderDefectGraph G).induce c.supp) (G.induce c.supp) a b = 5) :
    ∀ i : ZMod 8, 0 <
      ((componentNeighborFinset
          ((secondOrderDefectGraph G).induce c.supp) (G.induce c.supp) a (u i)).filter
        fun z => s z.1 = s (u i).1).card := by
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
  obtain ⟨r, _hr2, _hr7, haa, habq, _hbaq, _hbb⟩ :=
    binarySquare_regular_sizeTwoPart_eight_eightEight_cycleQuotient
      G hfree hreg hcard c hc s hs_in hs_out hA_in a b ha hb hab
  have hr : r = 5 := by omega
  have haa2 : componentQuotientMatrix K H a a = 2 := by
    simpa [K, H, hr] using haa
  intro i
  let x : c.supp := u i
  let A := componentNeighborFinset K H a x
  let B := componentNeighborFinset K H b x
  have hxA : x ∈ a.supp := by
    rw [← hurange]
    exact ⟨i, rfl⟩
  have hAcard : A.card = 2 := by
    rw [← componentQuotientMatrix_apply_eq K H 2 hHdegree hcomm a a hxA]
    exact haa2
  have hBcard : B.card = 5 := by
    rw [← componentQuotientMatrix_apply_eq K H 2 hHdegree hcomm a b hxA]
    simpa [K, H] using hab5
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
  have hKsame :
      ((K.neighborFinset x).filter fun z => s z.1 = s x.1).card = 5 := by
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
  let S : Finset c.supp :=
    (Finset.univ.image v).filter fun z => s z.1 = s x.1
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
  change 0 < (A.filter fun z => s z.1 = s x.1).card
  omega

/-- In an all-triangle first shore at parameter five, diagonal defect
adjacency is exactly the same-parity offset pair `{±2}`. -/
theorem binarySquare_regular_sizeTwoPart_eight_eightEight_parameterFive_firstCycle_defectAdj_iff_offset_two_six
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
    (hab5 : componentQuotientMatrix
      ((secondOrderDefectGraph G).induce c.supp) (G.induce c.supp) a b = 5)
    (haall : ∀ z : c.supp, z ∈ a.supp →
      (triangleFreeEdgeGraph G).degree z.1 = 0) :
    ∀ i j : ZMod 8,
      ((secondOrderDefectGraph G).induce c.supp).Adj (u i) (u j) ↔
        j - i = 2 ∨ j - i = 6 := by
  classical
  let H := G.induce c.supp
  let K := (secondOrderDefectGraph G).induce c.supp
  let M : Matrix (ZMod 8) (ZMod 8) ℤ :=
    fun i j => K.adjMatrix ℤ (u i) (u j)
  obtain ⟨hHdegree, _hKdegree, hcommHK⟩ :=
    binarySquare_regular_sizeTwoPart_commuting_regular_blocks
      G hfree (by omega) hreg hcard c hc
  have hcomm : K.adjMatrix ℤ * H.adjMatrix ℤ =
      H.adjMatrix ℤ * K.adjMatrix ℤ := by
    simpa [K, H] using hcommHK.symm
  have hcommReal : K.adjMatrix ℝ * H.adjMatrix ℝ =
      H.adjMatrix ℝ * K.adjMatrix ℝ := by
    have hglobal := adjMatrix_comm_secondOrderDefect_of_regular_field
      (K := ℝ) G hfree hreg
    exact (induce_component_adjMatrix_comm_of_comm G
      (secondOrderDefectGraph G) hglobal c).symm
  have hupair : ∀ z, u (z - 1) ≠ u (z + 1) := fun z =>
    huinj.ne (zmod_sub_one_ne_add_one_of_three_le (by omega) z)
  have hinter : ∀ i j,
      M (i - 1) j + M (i + 1) j = M i (j + 1) + M i (j - 1) := by
    simpa only [M] using entry_cycleIntertwine_of_adjMatrix_comm
      K H u u (1 : ZMod 8) (1 : ZMod 8) hcomm hu hu hupair hupair
  have hdiag : ∀ z, M z z = 0 := by
    intro z
    simp [M, SimpleGraph.adjMatrix_apply]
  have hsymm : ∀ i j, M i j = M j i := by
    intro i j
    by_cases hij : K.Adj (u i) (u j)
    · have hji : K.Adj (u j) (u i) := (K.adj_comm _ _).mp hij
      simp [M, SimpleGraph.adjMatrix_apply, hij, hji]
    · have hji : ¬K.Adj (u j) (u i) := by
        intro h
        exact hij ((K.adj_comm _ _).mp h)
      simp [M, SimpleGraph.adjMatrix_apply, hij, hji]
  have hbinary : ∀ i j, M i j = 0 ∨ M i j = 1 := by
    intro i j
    simp only [M, SimpleGraph.adjMatrix_apply]
    split <;> simp
  obtain ⟨r, _hr2, _hr7, haa, habq, _hbaq, _hbb⟩ :=
    binarySquare_regular_sizeTwoPart_eight_eightEight_cycleQuotient
      G hfree hreg hcard c hc s hs_in hs_out hA_in a b ha hb hab
  have hr : r = 5 := by omega
  have haa2 : componentQuotientMatrix K H a a = 2 := by
    simpa [K, H, hr] using haa
  have hua : ∀ i, u i ∈ a.supp := by
    intro i
    rw [← hurange]
    exact ⟨i, rfl⟩
  have hrowSupportCard : ∀ i,
      ((Finset.univ : Finset (ZMod 8)).filter fun j => M i j = 1).card = 2 := by
    intro i
    let T := (Finset.univ : Finset (ZMod 8)).filter fun j => M i j = 1
    let A := componentNeighborFinset K H a (u i)
    have himage : T.image u = A := by
      ext z
      constructor
      · simp only [Finset.mem_image, T, Finset.mem_filter, Finset.mem_univ,
          true_and]
        rintro ⟨j, hm, rfl⟩
        have hadj : K.Adj (u i) (u j) := by
          simpa [M, SimpleGraph.adjMatrix_apply] using hm
        exact Finset.mem_filter.mpr
          ⟨(K.mem_neighborFinset _ _).mpr hadj, hua j⟩
      · intro hz
        have hzA := Finset.mem_filter.mp hz
        have hza : z ∈ a.supp :=
          (ConnectedComponent.mem_supp_iff a z).mpr hzA.2
        rw [← hurange] at hza
        obtain ⟨j, rfl⟩ := hza
        refine Finset.mem_image.mpr ⟨j, ?_, rfl⟩
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ j,
          by simpa [M, SimpleGraph.adjMatrix_apply] using
            (K.mem_neighborFinset _ _).mp hzA.1⟩
    have hAcard : A.card = 2 := by
      rw [← componentQuotientMatrix_apply_eq K H 2 hHdegree hcommReal a a (hua i)]
      exact haa2
    rw [← Finset.card_image_of_injective T huinj, himage, hAcard]
  have hrow : ∀ i, ∑ j, M i j = 2 := by
    intro i
    calc
      ∑ j, M i j = ∑ j, if M i j = 1 then (1 : ℤ) else 0 := by
        apply Finset.sum_congr rfl
        intro j _
        rcases hbinary i j with hz | ho
        · simp [hz]
        · simp [ho]
      _ =
          (((Finset.univ : Finset (ZMod 8)).filter fun j => M i j = 1).card : ℤ) := by
        simpa only using
          (Finset.sum_boole (R := ℤ) (fun j : ZMod 8 => M i j = 1) Finset.univ)
      _ = 2 := by exact_mod_cast hrowSupportCard i
  have huflip : ∀ i : ZMod 8, s (u (i + 1)).1 = -s (u i).1 := by
    intro i
    have hH : H.Adj (u i) (u (i + 1)) := by
      rw [← H.mem_neighborFinset, hu]
      simp
    have hmem : (u (i + 1)).1 ∈ componentNeighborFinset G
        (secondOrderDefectGraph G) c (u i).1 := by
      rw [componentNeighborFinset, Finset.mem_filter]
      exact ⟨(G.mem_neighborFinset _ _).mpr hH, (u (i + 1)).2⟩
    exact (internal_alternation G hfree (by omega) hreg hcard c hc s
      hs_in hs_out hA_in (u i).2).2 _ hmem
  have hsignEven := zmodEight_alternating_sign_eq_iff_evenOffset
    (fun i => s (u i).1) (fun i => hs_in _ (u i).2) huflip
  have hposGraph :=
    binarySquare_regular_sizeTwoPart_eight_eightEight_parameterFive_firstCycle_diagonalSame_pos
      G hfree hreg hcard c hc s hs_in hs_out hA_in hDs a b ha hb hab
        u v huinj hvinj hurange hvrange hu hv hab5
  have hdegreePos : ∀ i, 0 <
      ((Finset.univ : Finset (ZMod 8)).filter fun j =>
        ZModEightEvenOffset (j - i) ∧ M i j = 1).card := by
    intro i
    let T := (Finset.univ : Finset (ZMod 8)).filter fun j =>
      ZModEightEvenOffset (j - i) ∧ M i j = 1
    let A := (componentNeighborFinset K H a (u i)).filter
      fun z => s z.1 = s (u i).1
    have himage : T.image u = A := by
      ext z
      constructor
      · simp only [Finset.mem_image, T, Finset.mem_filter, Finset.mem_univ,
          true_and]
        rintro ⟨j, ⟨heven, hm⟩, rfl⟩
        have hadj : K.Adj (u i) (u j) := by
          simpa [M, SimpleGraph.adjMatrix_apply] using hm
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_filter.mpr
            ⟨(K.mem_neighborFinset _ _).mpr hadj, hua j⟩,
            (hsignEven i j).mpr heven⟩
      · intro hz
        have hzA := (Finset.mem_filter.mp hz).1
        have hzSign := (Finset.mem_filter.mp hz).2
        have hza : z ∈ a.supp :=
          (ConnectedComponent.mem_supp_iff a z).mpr (Finset.mem_filter.mp hzA).2
        rw [← hurange] at hza
        obtain ⟨j, rfl⟩ := hza
        have hadj := (K.mem_neighborFinset _ _).mp (Finset.mem_filter.mp hzA).1
        refine Finset.mem_image.mpr ⟨j, ?_, rfl⟩
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ j,
          (hsignEven i j).mp hzSign,
          by simpa [M, SimpleGraph.adjMatrix_apply, hadj]⟩
    rw [← Finset.card_image_of_injective T huinj, himage]
    simpa [A, K, H] using hposGraph i
  have hdegreeLe : ∀ i,
      ((Finset.univ : Finset (ZMod 8)).filter fun j =>
        ZModEightEvenOffset (j - i) ∧ M i j = 1).card ≤ 2 := by
    intro i
    calc
      ((Finset.univ : Finset (ZMod 8)).filter fun j =>
        ZModEightEvenOffset (j - i) ∧ M i j = 1).card ≤
          ((Finset.univ : Finset (ZMod 8)).filter fun j => M i j = 1).card :=
        Finset.card_le_card (by
          intro j hj
          exact Finset.mem_filter.mpr
            ⟨Finset.mem_univ j, (Finset.mem_filter.mp hj).2.2⟩)
      _ = 2 := hrowSupportCard i
  have havoidM : ∀ i, M i (i - 1) = 0 ∧ M i (i + 1) = 0 := by
    intro i
    have noD (j : ZMod 8) (hHadj : H.Adj (u i) (u j)) : ¬K.Adj (u i) (u j) := by
      intro hK
      rcases hK with hanti | htf
      · exact ((mem_antipodalNeighbors G (u i).1 (u j).1).mp hanti).2.1 hHadj
      · have hmem : (u j).1 ∈ (triangleFreeEdgeGraph G).neighborFinset (u i).1 :=
          ((triangleFreeEdgeGraph G).mem_neighborFinset _ _).mpr htf
        have hpos := Finset.card_pos.mpr ⟨(u j).1, hmem⟩
        rw [(triangleFreeEdgeGraph G).card_neighborFinset_eq_degree,
          haall (u i) (hua i)] at hpos
        omega
    constructor
    · have hHadj : H.Adj (u i) (u (i - 1)) := by
        rw [← H.mem_neighborFinset, hu]
        simp
      have hn := noD (i - 1) hHadj
      simp [M, SimpleGraph.adjMatrix_apply, hn]
    · have hHadj : H.Adj (u i) (u (i + 1)) := by
        rw [← H.mem_neighborFinset, hu]
        simp
      have hn := noD (i + 1) hHadj
      simp [M, SimpleGraph.adjMatrix_apply, hn]
  let d := ((Finset.univ : Finset (ZMod 8)).filter fun j =>
    ZModEightEvenOffset (j - 0) ∧ M 0 j = 1).card
  have hdegreeEq : ∀ i,
      ((Finset.univ : Finset (ZMod 8)).filter fun j =>
        ZModEightEvenOffset (j - i) ∧ M i j = 1).card = d := by
    intro i
    exact zmodEight_selfIntertwiner_sameParity_card_eq M hdiag hinter i 0
  have hdpos : 0 < d := by simpa [d] using hdegreePos 0
  have hdle : d ≤ 2 := by simpa [d] using hdegreeLe 0
  have hd2 : d = 2 := by
    by_contra hne
    have hd1 : d = 1 := by omega
    have hdegree1 : ∀ i,
        ((Finset.univ : Finset (ZMod 8)).filter fun j =>
          ZModEightEvenOffset (j - i) ∧ M i j = 1).card = 1 := by
      intro i
      rw [hdegreeEq, hd1]
    exact zmodEight_selfIntertwiner_sameParity_degreeOne_impossible
      M hdiag hsymm hinter hbinary hrow hdegree1 havoidM
  have hdegree2 : ∀ i,
      ((Finset.univ : Finset (ZMod 8)).filter fun j =>
        ZModEightEvenOffset (j - i) ∧ M i j = 1).card = 2 := by
    intro i
    rw [hdegreeEq, hd2]
  have hoff := zmodEight_selfIntertwiner_sameParity_degreeTwo_offset_two_six
    M hdiag hsymm hinter hdegree2
  intro i j
  have hEvenSupportEq :
      ((Finset.univ : Finset (ZMod 8)).filter fun z =>
        ZModEightEvenOffset (z - i) ∧ M i z = 1) =
      ((Finset.univ : Finset (ZMod 8)).filter fun z => M i z = 1) := by
    apply Finset.eq_of_subset_of_card_le
    · intro z hz
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_univ z, (Finset.mem_filter.mp hz).2.2⟩
    · rw [hdegree2, hrowSupportCard]
  constructor
  · intro hij
    change K.Adj (u i) (u j) at hij
    have hm : M i j = 1 := by
      simp [M, SimpleGraph.adjMatrix_apply, hij]
    have hjmem : j ∈ ((Finset.univ : Finset (ZMod 8)).filter fun z =>
        ZModEightEvenOffset (z - i) ∧ M i z = 1) := by
      rw [hEvenSupportEq]
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ j, hm⟩
    have heven := (Finset.mem_filter.mp hjmem).2.1
    exact (hoff i j heven).mp hm
  · intro hoffset
    have heven : ZModEightEvenOffset (j - i) := by
      rcases hoffset with h2 | h6
      · exact Or.inr (Or.inl h2)
      · exact Or.inr (Or.inr (Or.inr h6))
    have hm : M i j = 1 := (hoff i j heven).mpr hoffset
    change K.Adj (u i) (u j)
    simpa [M, SimpleGraph.adjMatrix_apply] using hm

end

end Erdos85

#print axioms Erdos85.binarySquare_regular_sizeTwoPart_eight_eightEight_parameterFive_firstCycle_diagonalSame_pos
#print axioms Erdos85.binarySquare_regular_sizeTwoPart_eight_eightEight_parameterFive_firstCycle_defectAdj_iff_offset_two_six
