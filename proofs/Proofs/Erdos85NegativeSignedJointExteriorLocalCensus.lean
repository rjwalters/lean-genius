import Proofs.Erdos85NegativeSignedJointDefectNeighborCensus
import Proofs.Erdos85NegativeSignedJointConnectedCoordinates
import Proofs.Erdos85SixteenCycleInternalCommonPairs
import Proofs.Erdos85NegativeSignedJointOutsidePairEncoding

/-! # Local exterior degree census for connected negative signed joints -/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

set_option maxRecDepth 100000 in
private theorem sixteenCycleOffsetTwo_row_card :
    ∀ i : Fin 16,
      ((Finset.univ : Finset (Fin 16)).filter
        fun j ↦ sixteenCycleOffsetTwo i j).card = 2 := by
  native_decide

/-- In the connected `C16` branch the exterior-pair graph has the indicated
same-sign and opposite-sign degree at every supported vertex. -/
theorem orderSixtyFour_negativeSignedJoint_exteriorLocalCensus
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hreg : ∀ x, G.degree x = 8)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    [DecidableEq (G.induce c.supp).ConnectedComponent]
    (hc : c.supp.ncard = 16)
    (hconn : (G.induce c.supp).Connected)
    (s : Fin 64 → ℤ) (mu : ℤ)
    (hs_out : ∀ x, x ∉ c.supp → s x = 0)
    (hs_in : ∀ x, x ∈ c.supp → s x = -1 ∨ s x = 1)
    (hH : ∀ z ∈ c.supp, ∑ y ∈ (G.neighborFinset z).filter
      (fun y ↦ (secondOrderDefectGraph G).connectedComponentMk y = c),
        s y = -2 * s z)
    (hD : ∀ z, z ∈ c.supp →
      ∑ y ∈ (secondOrderDefectGraph G).neighborFinset z, s y = mu * s z) :
    ∀ x : c.supp,
      let Rs := ((exteriorPairGraph G c.supp).neighborFinset x).filter
        fun y ↦ s y.1 = s x.1
      let Ro := ((exteriorPairGraph G c.supp).neighborFinset x).filter
        fun y ↦ s y.1 ≠ s x.1
      (mu = -1 → Rs.card = 2 ∧ Ro.card = 4) ∧
      (mu = -3 → Rs.card = 3 ∧ Ro.card = 3) ∧
      (mu = -5 → Rs.card = 4 ∧ Ro.card = 2) := by
  classical
  let H := G.induce c.supp
  let D := secondOrderDefectGraph G
  let R := exteriorPairGraph G c.supp
  obtain ⟨coord⟩ := exists_negativeSignedJointConnectedCoordinates
    G hfree hreg c hc hconn s hs_out hs_in hH
  have hsign (x : c.supp) : s x.1 = -1 ∨ s x.1 = 1 := hs_in x.1 x.2
  have hfiber (eps : ℤ) (heps : eps = 1 ∨ eps = -1) :
      ((Finset.univ : Finset c.supp).filter fun y ↦ s y.1 = eps).card = 8 := by
    rcases heps with rfl | rfl
    · change _ = (Finset.univ : Finset (Fin 8)).card
      apply Finset.card_bij
        (fun y hy ↦ coord.model.row ⟨y, (Finset.mem_filter.mp hy).2⟩)
      · intro y hy
        exact Finset.mem_univ _
      · intro y _ z _ hyz
        exact congrArg (fun p ↦ p.1) (coord.model.row.injective hyz)
      · intro i _
        let p := coord.model.row.symm i
        exact ⟨p.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, p.2⟩,
          coord.model.row.apply_symm_apply i⟩
    · change _ = (Finset.univ : Finset (Fin 8)).card
      apply Finset.card_bij
        (fun y hy ↦ coord.model.column ⟨y, (Finset.mem_filter.mp hy).2⟩)
      · intro y hy
        exact Finset.mem_univ _
      · intro y _ z _ hyz
        exact congrArg (fun n ↦ n.1) (coord.model.column.injective hyz)
      · intro i _
        let n := coord.model.column.symm i
        exact ⟨n.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, n.2⟩,
          coord.model.column.apply_symm_apply i⟩
  intro x
  let S := (Finset.univ : Finset c.supp).filter
    fun y ↦ y ≠ x ∧ s y.1 = s x.1
  let DS := (Finset.univ : Finset c.supp).filter fun y ↦
    D.Adj x.1 y.1 ∧ s y.1 = s x.1
  let RS := (R.neighborFinset x).filter fun y ↦ s y.1 = s x.1
  let RO := (R.neighborFinset x).filter fun y ↦ s y.1 ≠ s x.1
  let Q := (Finset.univ : Finset c.supp).filter fun y ↦
    y ≠ x ∧ ∃ z : c.supp, H.Adj x z ∧ H.Adj y z
  have hScard : S.card = 7 := by
    have hf : ((Finset.univ : Finset c.supp).filter
        fun y ↦ s y.1 = s x.1).card = 8 := by
      rcases hsign x with hs | hs
      · simpa [hs] using hfiber (-1) (Or.inr rfl)
      · simpa [hs] using hfiber 1 (Or.inl rfl)
    have hxmem : x ∈ (Finset.univ : Finset c.supp).filter
        fun y ↦ s y.1 = s x.1 := by simp
    have hSeq : S = ((Finset.univ : Finset c.supp).filter
        fun y ↦ s y.1 = s x.1).erase x := by
      ext y
      simp [S, and_comm]
    rw [hSeq, Finset.card_erase_of_mem hxmem, hf]
  have hQcard : Q.card = 2 := by
    let i := coord.label.toEquiv x
    rw [← sixteenCycleOffsetTwo_row_card i]
    apply Finset.card_bij (fun y _ ↦ coord.label.toEquiv y)
    · intro y hy
      have h := (Finset.mem_filter.mp hy).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        (sixteenCycleLabeling_internalCommon_iff_offsetTwo H coord.label
          i (coord.label.toEquiv y) (fun hiy ↦ h.1
            (coord.label.toEquiv.injective hiy.symm))).mp (by
              rcases h.2 with ⟨z, hxz, hyz⟩
              exact ⟨z, by simpa [i] using hxz, by simpa using hyz⟩)⟩
    · intro y _ z _ hyz
      exact coord.label.toEquiv.injective hyz
    · intro j hj
      let y := coord.label.toEquiv.symm j
      have hoff := (Finset.mem_filter.mp hj).2
      have hij : i ≠ j := by
        intro hij
        subst j
        simp [sixteenCycleOffsetTwo] at hoff
      have hcommon := (sixteenCycleLabeling_internalCommon_iff_offsetTwo
        H coord.label i j hij).mpr hoff
      refine ⟨y, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩,
        coord.label.toEquiv.apply_symm_apply j⟩
      · intro hyx
        apply hij
        simpa [i, y] using (congrArg coord.label.toEquiv hyx).symm
      · rcases hcommon with ⟨z, hxz, hyz⟩
        exact ⟨z, by simpa [i, y] using hxz, by simpa [y] using hyz⟩
  have hQsame : ∀ y, y ∈ Q → s y.1 = s x.1 := by
    intro y hy
    rcases (Finset.mem_filter.mp hy).2.2 with ⟨z, hxz, hyz⟩
    have hdeg : ∀ w : c.supp, H.degree w = 2 := by
      intro w
      exact binarySquare_regular_degree_induce_defectComponent_eq_part
        G hfree (by omega) hreg (by norm_num) c (m := 2) (by simpa using hc) w
    have hA_in : ∀ w ∈ c.supp,
        ∑ v ∈ G.neighborFinset w, s v = -2 * s w := by
      intro w hw
      rw [← hH w hw]
      symm
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro v hv hvout
      have hvc : v ∉ c.supp := by
        intro hvin
        apply hvout
        exact Finset.mem_filter.mpr ⟨hv,
          (ConnectedComponent.mem_supp_iff c v).mp hvin⟩
      simp [hs_out v hvc]
    have hneighborSum : ∀ w, ∑ v ∈ H.neighborFinset w, s v.1 = -2 * s w.1 := by
      intro w
      rw [← SimpleGraph.adjMatrix_mulVec_apply]
      rw [← adjMatrix_mulVec_eq_induce_mulVec_of_support_int G c.supp s hs_out w]
      rw [SimpleGraph.adjMatrix_mulVec_apply]
      exact hA_in w.1 w.2
    have hflip : ∀ {u v : c.supp}, H.Adj u v → s u.1 = -s v.1 := by
      intro u v huv
      exact signedFlip_of_degree_two_neighborSum H hdeg (fun w ↦ s w.1)
        hsign hneighborSum huv
    rw [hflip hxz, hflip hyz]
  have hpart : S = DS ∪ (RS ∪ Q) := by
    ext y
    simp only [S, DS, RS, Q, Finset.mem_union, Finset.mem_filter,
      Finset.mem_univ, true_and, D, R]
    constructor
    · rintro ⟨hyx, hsy⟩
      by_cases hdy : (secondOrderDefectGraph G).Adj x.1 y.1
      · exact Or.inl ⟨hdy, hsy⟩
      by_cases hqy : ∃ z : c.supp, G.Adj x.1 z.1 ∧ G.Adj y.1 z.1
      · exact Or.inr (Or.inr ⟨hyx, by simpa [H] using hqy⟩)
      · exact Or.inr (Or.inl ⟨(R.mem_neighborFinset x y).mpr
          ((exteriorPairGraph_adj_iff_not_defect_and_no_internal_common
            G hfree c x y).mpr ⟨hyx.symm, hdy, hqy⟩), hsy⟩)
    · rintro (⟨_, hsy⟩ | ⟨⟨hyR, hsy⟩ | hq⟩)
      · exact ⟨by rintro rfl; simp at *, hsy⟩
      · exact ⟨((exteriorPairGraph_adj_iff_not_defect_and_no_internal_common
          G hfree c x y).mp ((R.mem_neighborFinset x y).mp hyR)).1.symm,
          hsy⟩
      · exact ⟨hq.1, hQsame y (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hq⟩)⟩
  have hdisjD : Disjoint DS (RS ∪ Q) := by
    rw [Finset.disjoint_left]
    intro y hyD hyRQ
    have hd := (Finset.mem_filter.mp hyD).2.1
    rcases Finset.mem_union.mp hyRQ with hyR | hyQ
    · exact ((exteriorPairGraph_adj_iff_not_defect_and_no_internal_common
        G hfree c x y).mp ((R.mem_neighborFinset x y).mp
          (Finset.mem_filter.mp hyR).1)).2.1 hd
    · rcases (Finset.mem_filter.mp hyQ).2.2 with ⟨z, hxz, hyz⟩
      have hne : x.1 ≠ y.1 := by
        intro hxy
        apply D.loopless.irrefl x.1
        simpa [hxy] using hd
      have hzero := (secondOrderDefectGraph_adj_iff_card_common_eq_zero G hfree
        hne).mp hd
      have hzmem : z.1 ∈ G.neighborFinset x.1 ∩ G.neighborFinset y.1 := by
        rw [Finset.mem_inter, mem_neighborFinset, mem_neighborFinset]
        exact ⟨by simpa [H] using hxz, by simpa [H] using hyz⟩
      rw [Finset.card_eq_zero.mp hzero] at hzmem
      exact Finset.notMem_empty _ hzmem
  have hdisjRQ : Disjoint RS Q := by
    rw [Finset.disjoint_left]
    intro y hyR hyQ
    have hr := (exteriorPairGraph_adj_iff_not_defect_and_no_internal_common
      G hfree c x y).mp ((R.mem_neighborFinset x y).mp
        (Finset.mem_filter.mp hyR).1)
    exact hr.2.2 ((Finset.mem_filter.mp hyQ).2.2)
  have hcount : DS.card + RS.card + Q.card = S.card := by
    rw [hpart, Finset.card_union_of_disjoint hdisjD,
      Finset.card_union_of_disjoint hdisjRQ]
    omega
  have hdef := orderSixtyFour_sizeTwo_negative_defectNeighborCensus
    G hfree hreg (by norm_num) c (by simpa using hc) s mu hs_out hs_in hH hD x.1 x.2
  dsimp only at hdef
  have hRdeg : R.degree x = 6 := by
    obtain ⟨_, _, _, _, _, hregular, _, _, _, _⟩ :=
      orderSixtyFour_regular_sizeSixteen_outsidePair_feasibility G hfree hreg c hc
    exact hregular x
  have hsplit : RS.card + RO.card = 6 := by
    rw [← hRdeg]
    change _ = (R.neighborFinset x).card
    simpa [RS, RO] using (R.neighborFinset x).card_filter_add_card_filter_not
      (fun y ↦ s y.1 = s x.1)
  have hclosed : ∀ y, D.Adj x.1 y → y ∈ c.supp := by
    intro y hxy
    rw [ConnectedComponent.mem_supp_iff]
    rw [← (ConnectedComponent.mem_supp_iff c x.1).mp x.2]
    exact (ConnectedComponent.connectedComponentMk_eq_of_adj hxy).symm
  have hDScard (eps : ℤ) (heps : s x.1 = eps) : DS.card =
      ((D.neighborFinset x.1).filter fun y ↦ s y = eps).card := by
    apply Finset.card_bij (fun y _ ↦ y.1)
    · intro y hy
      have hy' := (Finset.mem_filter.mp hy).2
      exact Finset.mem_filter.mpr ⟨(D.mem_neighborFinset x.1 y.1).mpr hy'.1,
        by simpa [heps] using hy'.2⟩
    · intro y _ z _ hyz
      exact Subtype.ext hyz
    · intro y hy
      have hy' := Finset.mem_filter.mp hy
      let ys : c.supp := ⟨y, hclosed y ((D.mem_neighborFinset x.1 y).mp hy'.1)⟩
      refine ⟨ys, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩, rfl⟩
      · exact (D.mem_neighborFinset x.1 y).mp hy'.1
      · simpa [heps] using hy'.2
  change (mu = -1 → RS.card = 2 ∧ RO.card = 4) ∧
    (mu = -3 → RS.card = 3 ∧ RO.card = 3) ∧
    (mu = -5 → RS.card = 4 ∧ RO.card = 2)
  rcases hsign x with hs | hs
  · have hDS : DS.card =
        ((D.neighborFinset x.1).filter fun y ↦ s y = -1).card :=
      hDScard (-1) hs
    constructor
    · intro hm
      have hd := (hdef.1 hm).2 hs
      have hdsn : DS.card = 3 := hDS.trans (by simpa [D] using hd.1)
      rw [hdsn, hQcard, hScard] at hcount
      omega
    constructor
    · intro hm
      have hd := (hdef.2.1 hm).2 hs
      have hdsn : DS.card = 2 := hDS.trans (by simpa [D] using hd.1)
      rw [hdsn, hQcard, hScard] at hcount
      omega
    · intro hm
      have hd := (hdef.2.2 hm).2 hs
      have hdsn : DS.card = 1 := hDS.trans (by simpa [D] using hd.1)
      rw [hdsn, hQcard, hScard] at hcount
      omega
  · have hDS : DS.card =
        ((D.neighborFinset x.1).filter fun y ↦ s y = 1).card :=
      hDScard 1 hs
    constructor
    · intro hm
      have hd := (hdef.1 hm).1 hs
      have hdsn : DS.card = 3 := hDS.trans (by simpa [D] using hd.1)
      rw [hdsn, hQcard, hScard] at hcount
      omega
    constructor
    · intro hm
      have hd := (hdef.2.1 hm).1 hs
      have hdsn : DS.card = 2 := hDS.trans (by simpa [D] using hd.1)
      rw [hdsn, hQcard, hScard] at hcount
      omega
    · intro hm
      have hd := (hdef.2.2 hm).1 hs
      have hdsn : DS.card = 1 := hDS.trans (by simpa [D] using hd.1)
      rw [hdsn, hQcard, hScard] at hcount
      omega

end

end Erdos85

#print axioms Erdos85.orderSixtyFour_negativeSignedJoint_exteriorLocalCensus
