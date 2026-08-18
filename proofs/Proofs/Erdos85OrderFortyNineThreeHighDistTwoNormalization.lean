import Proofs.Erdos85OrderFortyNineDistTwoPinning
import Proofs.Erdos85OrderFortyNineHighNeighborhoodNormalization
import Proofs.Erdos85OrderFortyNineThreeHighMatchingTransport

/-! # Full geometry normalization in the three-high distance-two case -/

namespace Erdos85

open SimpleGraph

noncomputable section

theorem exists_orderFortyNine_threeHighDistTwo_geometryLabeling
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49)
    {v1 v2 v3 sStar : V}
    (hv1 : G.degree v1 = 8) (hv2 : G.degree v2 = 8)
    (hv3 : G.degree v3 = 8) (hsLow : G.degree sStar = 7)
    (h12 : v1 ≠ v2) (h13 : v1 ≠ v3) (h23 : v2 ≠ v3)
    (hs1 : G.Adj sStar v1) (hs2 : G.Adj sStar v2)
    (hs3 : G.Adj sStar v3)
    (hHigh : orderFortyNineHighVertices G = {v1, v2, v3}) :
    ∃ E : V ≃ Fin 49,
      let H := orderFortyNineRelabeledGraph G E
      E v1 = 0 ∧ E v2 = 1 ∧ E v3 = 2 ∧
      H.neighborFinset 0 =
          Finset.univ.image orderFortyNineDistTwoFirstTarget ∧
      H.neighborFinset 1 =
          Finset.univ.image orderFortyNineDistTwoSecondTarget ∧
      H.neighborFinset 2 =
          Finset.univ.image orderFortyNineDistTwoThirdTarget ∧
      OrderFortyNineGraphPinnedMatchingRealized H
        [3, 4, 5, 6, 7, 8, 9, 10]
        [(3, 4), (5, 6), (7, 8), (9, 10)] ∧
      OrderFortyNineGraphPinnedMatchingRealized H
        [3, 11, 14, 15, 16, 17, 18, 19]
        [(3, 11), (14, 15), (16, 17), (18, 19)] ∧
      OrderFortyNineGraphPinnedMatchingRealized H
        [3, 12, 20, 21, 22, 23, 24, 25]
        [(3, 12), (20, 21), (22, 23), (24, 25)] ∧
      OrderFortyNineThreeHighDistTwoRootEmptyGraphRealized H := by
  obtain ⟨t, x2, x3, l3, hN, htdeg, hx2deg, hx3deg, hl3deg,
      ht1, hx2v2, hx3v3, htnot, hx23, hl3not, _hl3Branch⟩ :=
    orderFortyNineDistTwo_exists_exact_pinned_neighborhood
      G hfree hmin hcard hv1 hv2 hv3 hsLow h12 h13 h23
      hs1 hs2 hs3 hHigh
  have hst : G.Adj sStar t := by
    rw [← G.mem_neighborFinset, hN]
    simp
  have hsx2 : G.Adj sStar x2 := by
    rw [← G.mem_neighborFinset, hN]
    simp
  have hsx3 : G.Adj sStar x3 := by
    rw [← G.mem_neighborFinset, hN]
    simp
  have hsl3 : G.Adj sStar l3 := by
    rw [← G.mem_neighborFinset, hN]
    simp
  have hl3facts : l3 ≠ v1 ∧ l3 ≠ v2 ∧ l3 ≠ v3 ∧ l3 ≠ t ∧
      l3 ≠ x2 ∧ l3 ≠ x3 := by
    simpa using hl3not
  have hl3t : l3 ≠ t := hl3facts.2.2.2.1
  have hl3x2 : l3 ≠ x2 := hl3facts.2.2.2.2.1
  have hl3x3 : l3 ≠ x3 := hl3facts.2.2.2.2.2
  have hl3v1 : ¬ G.Adj l3 v1 := by
    intro hl
    have hu := orderFortyNine_existsUnique_local_partner_of_high
      G hfree hmin hcard hv1 hs1
    exact hl3t (hu.unique ⟨hsl3, hl.symm⟩ ⟨hst, ht1⟩)
  have hl3v2 : ¬ G.Adj l3 v2 := by
    intro hl
    have hu := orderFortyNine_existsUnique_local_partner_of_high
      G hfree hmin hcard hv2 hs2
    exact hl3x2 (hu.unique ⟨hsl3, hl.symm⟩ ⟨hsx2, hx2v2⟩)
  have hl3v3 : ¬ G.Adj l3 v3 := by
    intro hl
    have hu := orderFortyNine_existsUnique_local_partner_of_high
      G hfree hmin hcard hv3 hs3
    exact hl3x3 (hu.unique ⟨hsl3, hl.symm⟩ ⟨hsx3, hx3v3⟩)
  let A := G.neighborFinset v1
  let B := G.neighborFinset v2
  let C := G.neighborFinset v3
  have hrA : sStar ∈ A := by simpa [A, G.adj_comm] using hs1
  have hrB : sStar ∈ B := by simpa [B, G.adj_comm] using hs2
  have hrC : sStar ∈ C := by simpa [C, G.adj_comm] using hs3
  obtain ⟨eA, hrootA, hcanA⟩ :=
    exists_orderFortyNine_highNeighborhood_rooted_matching
      G hfree hmin hcard hv1 hs1
  obtain ⟨eB, hrootB, hcanB⟩ :=
    exists_orderFortyNine_highNeighborhood_rooted_matching
      G hfree hmin hcard hv2 hs2
  obtain ⟨eC, hrootC, hcanC⟩ :=
    exists_orderFortyNine_highNeighborhood_rooted_matching
      G hfree hmin hcard hv3 hs3
  let toA : {x : V // x ∈ A} ≃ {x : V // x ∈ G.neighborSet v1} :=
    Equiv.subtypeEquiv (Equiv.refl V) (fun x => by simp [A])
  let toB : {x : V // x ∈ B} ≃ {x : V // x ∈ G.neighborSet v2} :=
    Equiv.subtypeEquiv (Equiv.refl V) (fun x => by simp [B])
  let toC : {x : V // x ∈ C} ≃ {x : V // x ∈ G.neighborSet v3} :=
    Equiv.subtypeEquiv (Equiv.refl V) (fun x => by simp [C])
  let eA' := toA.trans eA
  let eB' := toB.trans eB
  let eC' := toC.trans eC
  have hrootA' : eA' ⟨sStar, hrA⟩ = 0 := by
    simpa [eA', toA] using hrootA
  have hrootB' : eB' ⟨sStar, hrB⟩ = 0 := by
    simpa [eB', toB] using hrootB
  have hrootC' : eC' ⟨sStar, hrC⟩ = 0 := by
    simpa [eC', toC] using hrootC
  have hAB : A ∩ B = {sStar} := by
    exact orderFortyNineDistTwo_common_highPair_eq_singleton
      G hfree hmin hcard hv1 hv2 h12 hs1 hs2
  have hAC : A ∩ C = {sStar} := by
    exact orderFortyNineDistTwo_common_highPair_eq_singleton
      G hfree hmin hcard hv1 hv3 h13 hs1 hs3
  have hBC : B ∩ C = {sStar} := by
    exact orderFortyNineDistTwo_common_highPair_eq_singleton
      G hfree hmin hcard hv2 hv3 h23 hs2 hs3
  let extra : Fin 4 → V := ![v1, v2, v3, l3]
  have hextra : Function.Injective extra := by
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [extra, h12, h13, h23, Ne.symm h12, Ne.symm h13,
        Ne.symm h23, hl3facts.1, hl3facts.2.1, hl3facts.2.2.1,
        hl3facts.2.2.2.1, hl3facts.2.2.2.2.1,
        hl3facts.2.2.2.2.2, Ne.symm hl3facts.1,
        Ne.symm hl3facts.2.1, Ne.symm hl3facts.2.2.1]
  have hnot12 := orderFortyNine_not_adj_degreeEight_degreeEight
    G hfree hmin hcard hv1 hv2
  have hnot13 := orderFortyNine_not_adj_degreeEight_degreeEight
    G hfree hmin hcard hv1 hv3
  have hnot23 := orderFortyNine_not_adj_degreeEight_degreeEight
    G hfree hmin hcard hv2 hv3
  have houtside : ∀ (z : V),
      ¬ G.Adj z v1 → ¬ G.Adj z v2 → ¬ G.Adj z v3 →
      ∀ j, z ≠ threeRootedWedgeSource A B C eA' eB' eC' j := by
    intro z hz1 hz2 hz3 j
    rcases j with j | j
    · intro heq
      have hm : (eA'.symm j).1 ∈ G.neighborFinset v1 := by
        simpa [A] using (eA'.symm j).2
      have hadj : G.Adj v1 (eA'.symm j).1 :=
        (G.mem_neighborFinset v1 _).mp hm
      apply hz1
      simpa [threeRootedWedgeSource, G.adj_comm, heq] using hadj
    · rcases j with j | j
      · intro heq
        have hm : (eB'.symm j.succ).1 ∈ G.neighborFinset v2 := by
          simpa [B] using (eB'.symm j.succ).2
        have hadj : G.Adj v2 (eB'.symm j.succ).1 :=
          (G.mem_neighborFinset v2 _).mp hm
        apply hz2
        simpa [threeRootedWedgeSource, G.adj_comm, heq] using hadj
      · intro heq
        have hm : (eC'.symm j.succ).1 ∈ G.neighborFinset v3 := by
          simpa [C] using (eC'.symm j.succ).2
        have hadj : G.Adj v3 (eC'.symm j.succ).1 :=
          (G.mem_neighborFinset v3 _).mp hm
        apply hz3
        simpa [threeRootedWedgeSource, G.adj_comm, heq] using hadj
  have hcross : ∀ i j,
      extra i ≠ threeRootedWedgeSource A B C eA' eB' eC' j := by
    intro i
    fin_cases i
    · apply houtside v1
      · exact G.loopless.irrefl v1
      · exact hnot12
      · exact hnot13
    · apply houtside v2
      · simpa [G.adj_comm] using hnot12
      · exact G.loopless.irrefl v2
      · exact hnot23
    · apply houtside v3
      · simpa [G.adj_comm] using hnot13
      · simpa [G.adj_comm] using hnot23
      · exact G.loopless.irrefl v3
    · exact houtside l3 hl3v1 hl3v2 hl3v3
  obtain ⟨E, hExtra, hroot, hWedge⟩ :=
    exists_orderFortyNine_equiv_of_threeRootedWedge_with_extra
      hcard A B C hrA hrB hrC hAB hAC hBC eA' eB' eC'
      hrootA' hrootB' hrootC' extra hextra hcross
  have hmapA : ∀ i, E (eA.symm i).1 =
      orderFortyNineDistTwoFirstTarget i := by
    intro i
    simpa [threeRootedWedgeSource, orderFortyNineDistTwoWedgeTarget,
      eA', toA]
      using hWedge (Sum.inl i)
  have hmapB : ∀ i, E (eB.symm i).1 =
      orderFortyNineDistTwoSecondTarget i := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · have hs : eB.symm 0 =
          ⟨sStar, by simpa using hs2.symm⟩ := by
        apply eB.injective
        simp [hrootB]
      simp [hs, hroot, orderFortyNineDistTwoSecondTarget]
    · simpa [threeRootedWedgeSource, orderFortyNineDistTwoWedgeTarget,
        eB', toB]
        using hWedge (Sum.inr (Sum.inl j))
  have hmapC : ∀ i, E (eC.symm i).1 =
      orderFortyNineDistTwoThirdTarget i := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · have hs : eC.symm 0 =
          ⟨sStar, by simpa using hs3.symm⟩ := by
        apply eC.injective
        simp [hrootC]
      simp [hs, hroot, orderFortyNineDistTwoThirdTarget]
    · simpa [threeRootedWedgeSource, orderFortyNineDistTwoWedgeTarget,
        eC', toC]
        using hWedge (Sum.inr (Sum.inr j))
  have hmatchA :=
    orderFortyNineGraphPinnedMatchingRealized_of_localNormalization
      G eA E orderFortyNineDistTwoFirstTarget
      [3, 4, 5, 6, 7, 8, 9, 10]
      [(3, 4), (5, 6), (7, 8), (9, 10)]
      hcanA hmapA orderFortyNineDistTwoFirstTarget_standard
  have hmatchB :=
    orderFortyNineGraphPinnedMatchingRealized_of_localNormalization
      G eB E orderFortyNineDistTwoSecondTarget
      [3, 11, 14, 15, 16, 17, 18, 19]
      [(3, 11), (14, 15), (16, 17), (18, 19)]
      hcanB hmapB orderFortyNineDistTwoSecondTarget_standard
  have hmatchC :=
    orderFortyNineGraphPinnedMatchingRealized_of_localNormalization
      G eC E orderFortyNineDistTwoThirdTarget
      [3, 12, 20, 21, 22, 23, 24, 25]
      [(3, 12), (20, 21), (22, 23), (24, 25)]
      hcanC hmapC orderFortyNineDistTwoThirdTarget_standard
  have hcoord_of_mate
      (v p : V) (hsv : G.Adj sStar v)
      (hvp : G.Adj v p) (hsp : G.Adj sStar p)
      (e : {x : V // x ∈ G.neighborSet v} ≃ Fin 8)
      (hrootE : e ⟨sStar, by simpa using hsv.symm⟩ = 0)
      (hcan : ∀ x y,
        decide ((G.induce (G.neighborSet v)).Adj x y) =
          decide (e y = oneHighStandardMate (e x))) :
      e ⟨p, by simpa using hvp⟩ = 1 := by
    let rootLocal : {x : V // x ∈ G.neighborSet v} :=
      ⟨sStar, by simpa using hsv.symm⟩
    let pLocal : {x : V // x ∈ G.neighborSet v} :=
      ⟨p, by simpa using hvp⟩
    have hc := hcan rootLocal pLocal
    have ht : decide ((G.induce (G.neighborSet v)).Adj
        rootLocal pLocal) = true := by
      simp [SimpleGraph.induce_adj, rootLocal, pLocal, hsp]
    rw [hc] at ht
    have heq := of_decide_eq_true ht
    have hmate : oneHighStandardMate (0 : Fin 8) = 1 := by decide
    simpa [rootLocal, pLocal, hrootE, hmate] using heq
  have hEt : E t = 4 := by
    have htcoord := hcoord_of_mate v1 t hs1 ht1 hst eA hrootA hcanA
    have hm := hmapA (eA ⟨t, by simpa using ht1⟩)
    have hs : eA.symm 1 = ⟨t, by simpa using ht1⟩ := by
      apply eA.injective
      simpa using htcoord.symm
    simpa [htcoord, hs, orderFortyNineDistTwoFirstTarget] using hm
  have hEx2 : E x2 = 11 := by
    have hxcoord := hcoord_of_mate v2 x2 hs2 hx2v2 hsx2
      eB hrootB hcanB
    have hm := hmapB (eB ⟨x2, by simpa using hx2v2⟩)
    have hs : eB.symm 1 = ⟨x2, by simpa using hx2v2⟩ := by
      apply eB.injective
      simpa using hxcoord.symm
    simpa [hxcoord, hs, orderFortyNineDistTwoSecondTarget] using hm
  have hEx3 : E x3 = 12 := by
    have hxcoord := hcoord_of_mate v3 x3 hs3 hx3v3 hsx3
      eC hrootC hcanC
    have hm := hmapC (eC ⟨x3, by simpa using hx3v3⟩)
    have hs : eC.symm 1 = ⟨x3, by simpa using hx3v3⟩ := by
      apply eC.injective
      simpa using hxcoord.symm
    simpa [hxcoord, hs, orderFortyNineDistTwoThirdTarget] using hm
  have hEv1 : E v1 = 0 := by
    simpa [extra, orderFortyNineDistTwoExtraTarget] using hExtra 0
  have hEv2 : E v2 = 1 := by
    simpa [extra, orderFortyNineDistTwoExtraTarget] using hExtra 1
  have hEv3 : E v3 = 2 := by
    simpa [extra, orderFortyNineDistTwoExtraTarget] using hExtra 2
  have hEl3 : E l3 = 13 := by
    simpa [extra, orderFortyNineDistTwoExtraTarget] using hExtra 3
  have hneighborA :=
    orderFortyNineRelabeledGraph_neighborFinset_eq_targetImage
      G eA E orderFortyNineDistTwoFirstTarget hmapA
  have hneighborB :=
    orderFortyNineRelabeledGraph_neighborFinset_eq_targetImage
      G eB E orderFortyNineDistTwoSecondTarget hmapB
  have hneighborC :=
    orderFortyNineRelabeledGraph_neighborFinset_eq_targetImage
      G eC E orderFortyNineDistTwoThirdTarget hmapC
  refine ⟨E, hEv1, hEv2, hEv3, ?_, ?_, ?_,
    hmatchA, hmatchB, hmatchC, ?_⟩
  · rw [hEv1] at hneighborA
    exact hneighborA
  · rw [hEv2] at hneighborB
    exact hneighborB
  · rw [hEv3] at hneighborC
    exact hneighborC
  exact orderFortyNineThreeHighDistTwoRootEmptyGraphRealized_of_pinned
    G E hN hroot hEv1 hEv2 hEv3 hEt hEx2 hEx3 hEl3

end

end Erdos85
