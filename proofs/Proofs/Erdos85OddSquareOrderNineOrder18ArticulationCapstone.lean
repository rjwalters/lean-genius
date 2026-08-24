import Proofs.Erdos85OddSquareOrderNineOrder18NonsymmetricElimination

/-!
# The complete order-eighteen articulation capstone

This module combines the symmetric spike reduction with the six
nonsymmetric `(1,2,3)` high-boundary permutations and then removes the
orientation of the `(18,59)` articulation witness.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- A nonsymmetric order-eighteen shore has equality in the sharp cut
bound.  Its 60-point ordinary complement therefore has the explicit
`(6,7)` profile with exactly 48 upper points. -/
theorem orderNine_order18_nonsymmetric_explicit_complement_of_boundary
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) (hcard : Fintype.card V = 81)
    (hminus hmiddle hplus : V)
    (hminusMiddle : hminus ≠ hmiddle)
    (hminusPlus : hminus ≠ hplus)
    (hmiddlePlus : hmiddle ≠ hplus)
    (S : Finset V)
    (hSsub : S ⊆ (Finset.univ : Finset V) \
      {hminus, hmiddle, hplus})
    (hScard : S.card = 18)
    (hbetaMinus : (G.neighborFinset hminus ∩ S).card = 1)
    (hbetaMiddle : (G.neighborFinset hmiddle ∩ S).card = 2)
    (hbetaPlus : (G.neighborFinset hplus ∩ S).card = 3)
    (hboundary : (∑ x ∈ S,
      ((secondOrderDefectGraph G).neighborFinset x ∩
        (Finset.univ \ S)).card) = 2)
    (hdegOrd : ∀ x ∉ ({hminus, hmiddle, hplus} : Finset V),
      G.degree x = 9)
    (hdegHigh : ∀ h ∈ ({hminus, hmiddle, hplus} : Finset V),
      G.degree h = 10)
    (hhighIndependent : ∀ h ∈
      ({hminus, hmiddle, hplus} : Finset V),
      Disjoint (G.neighborFinset h) {hminus, hmiddle, hplus})
    (hdefectHighIsolated : ∀ h ∈
      ({hminus, hmiddle, hplus} : Finset V),
      (secondOrderDefectGraph G).neighborFinset h = ∅) :
    orderNineOrdinaryExplicitPartition G hminus hmiddle hplus
      (((Finset.univ : Finset V) \ {hminus, hmiddle, hplus}) \ S) 6 48 := by
  classical
  let H : Finset V := {hminus, hmiddle, hplus}
  let O := (Finset.univ : Finset V) \ H
  let R := O \ S
  have hHcard : H.card = 3 := by
    simp [H, hminusMiddle, hminusPlus, hmiddlePlus]
  have hOcard : O.card = 78 := by
    dsimp [O]
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ H),
      Finset.card_univ, hcard, hHcard]
  have hRcard : R.card = 60 := by
    dsimp [R]
    rw [Finset.card_sdiff_of_subset (by simpa [O, H] using hSsub),
      hOcard, hScard]
  have hRH : Disjoint R H := by
    rw [Finset.disjoint_left]
    intro x hxR hxH
    exact (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hxR).1).2 hxH
  have hcompBoundary := ordinary_complement_boundary_sum_eq
    (secondOrderDefectGraph G) H S (by simpa [H] using hSsub)
      (by simpa [H] using hdefectHighIsolated)
  have hRboundary : (∑ x ∈ R,
      ((secondOrderDefectGraph G).neighborFinset x ∩
        (Finset.univ \ R)).card) = 2 := by
    simpa [R, O, H] using hcompBoundary.trans hboundary
  have hbminus := orderNine_high_neighbor_ordinary_compl_card
    G H S hminus (hdegHigh hminus (by simp [H]))
      (hhighIndependent hminus (by simp [H]))
  have hbmiddle := orderNine_high_neighbor_ordinary_compl_card
    G H S hmiddle (hdegHigh hmiddle (by simp [H]))
      (hhighIndependent hmiddle (by simp [H]))
  have hbplus := orderNine_high_neighbor_ordinary_compl_card
    G H S hplus (hdegHigh hplus (by simp [H]))
      (hhighIndependent hplus (by simp [H]))
  have hbminusR : (G.neighborFinset hminus ∩ R).card = 9 := by
    simpa [R, O, H, hbetaMinus] using hbminus
  have hbmiddleR : (G.neighborFinset hmiddle ∩ R).card = 8 := by
    simpa [R, O, H, hbetaMiddle] using hbmiddle
  have hbplusR : (G.neighborFinset hplus ∩ R).card = 7 := by
    simpa [R, O, H, hbetaPlus] using hbplus
  have hsharp := orderNineOrdinarySharpPartition_of_boundary
    G hfree hcard hminus hmiddle hplus hminusMiddle hminusPlus hmiddlePlus
      R hRH hdegOrd hdegHigh 2 hRboundary (by
        norm_num [orderNineNearRegularCutLower, orderNineBalancedSquareSum,
          hRcard, hbminusR, hbmiddleR, hbplusR])
  apply orderNineOrdinaryExplicitPartition_of_sharp
    G hminus hmiddle hplus hminusMiddle hminusPlus hmiddlePlus
      R 6 48 hRH hdegOrd hsharp
  · rw [hRcard, hbminusR, hbmiddleR, hbplusR]
  · norm_num

set_option maxHeartbeats 800000 in
/-- Every oriented order-eighteen FullType articulation is impossible:
the symmetric beta assignment is handled by the spike capstone, and each
of the six `(1,2,3)` permutations by the equality-complement capstone. -/
theorem false_of_orderNine_order18_oriented_articulation_output
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ z : V, 9 ≤ G.degree z)
    (hcover : ∀ {u v}, G.Adj u v → G.degree u = 9 ∨ G.degree v = 9)
    (hcard : Fintype.card V = 81)
    (hp : SquareOrderNonregularSectorProfile G 9)
    (hhigh : (squareOrderHighVertices G 9).card = 3)
    (hc2 : squareOrderNineHighIncidenceHistogram G 2 = 0)
    (hc3 : squareOrderNineHighIncidenceHistogram G 3 = 1)
    (hc4 : squareOrderNineHighIncidenceHistogram G 4 = 0)
    (h₁ h₂ h₃ : V) (h₁₂ : h₁ ≠ h₂) (h₁₃ : h₁ ≠ h₃) (h₂₃ : h₂ ≠ h₃)
    (hH : squareOrderHighVertices G 9 = {h₁, h₂, h₃})
    (owner : V) (howner : owner ∈ squareOrderNineLowIncidenceBin G 3)
    (S T : Finset V)
    (hunion : S ∪ T = ((Finset.univ : Finset V) \
      squareOrderHighVertices G 9).erase owner)
    (hdisj : Disjoint S T)
    (hScard : S.card = 18) (hTcard : T.card = 59)
    (hfull : orderNineArticulationSmallShoreFullType G
      ((secondOrderDefectGraph G).neighborFinset owner ∩
        squareOrderNineLowIncidenceBin G 0) h₁ h₂ h₃ S)
    (hSclosed : ∀ x ∈ S, (secondOrderDefectGraph G).neighborFinset x ∩
      ((Finset.univ : Finset V) \
        squareOrderHighVertices G 9).erase owner ⊆ S)
    (hTclosed : ∀ x ∈ T, (secondOrderDefectGraph G).neighborFinset x ∩
      ((Finset.univ : Finset V) \
        squareOrderHighVertices G 9).erase owner ⊆ T)
    (hSboundary : (∑ x ∈ S,
      ((secondOrderDefectGraph G).neighborFinset x ∩
        (Finset.univ \ S)).card) =
      (((secondOrderDefectGraph G).neighborFinset owner ∩
        squareOrderNineLowIncidenceBin G 0) ∩ S).card)
    (hdegOrd : ∀ x ∉ ({h₁, h₂, h₃} : Finset V), G.degree x = 9)
    (hdegHigh : ∀ h ∈ ({h₁, h₂, h₃} : Finset V), G.degree h = 10)
    (hhighIndependent : ∀ h ∈ ({h₁, h₂, h₃} : Finset V),
      Disjoint (G.neighborFinset h) ({h₁, h₂, h₃} : Finset V))
    (hdefectHighIsolated : ∀ h ∈ ({h₁, h₂, h₃} : Finset V),
      (secondOrderDefectGraph G).neighborFinset h = ∅) : False := by
  classical
  let H : Finset V := {h₁, h₂, h₃}
  let O := (Finset.univ : Finset V) \ H
  let R := O \ S
  let E := (secondOrderDefectGraph G).neighborFinset owner ∩
    squareOrderNineLowIncidenceBin G 0
  let K := G.neighborFinset owner ∩ squareOrderNineLowIncidenceBin G 1
  have hSsub : S ⊆ O := by
    intro x hxS
    have hxU : x ∈ ((Finset.univ : Finset V) \
        squareOrderHighVertices G 9).erase owner := by
      rw [← hunion]
      exact Finset.mem_union_left T hxS
    simpa [O, H, hH] using (Finset.mem_erase.mp hxU).2
  have hownerS : owner ∉ S := by
    intro ho
    have : owner ∈ ((Finset.univ : Finset V) \
        squareOrderHighVertices G 9).erase owner := by
      rw [← hunion]
      exact Finset.mem_union_left T ho
    exact (Finset.notMem_erase owner _ this)
  have hownerH : owner ∉ H := by
    have ho := (Finset.mem_filter.mp howner).1
    simpa [H, hH] using (Finset.mem_sdiff.mp ho).2
  have hownerHighSet : G.neighborFinset owner ∩
      squareOrderHighVertices G 9 = squareOrderHighVertices G 9 := by
    apply Finset.eq_of_subset_of_card_le Finset.inter_subset_right
    have hk3 := (Finset.mem_filter.mp howner).2
    change (G.neighborFinset owner ∩ squareOrderHighVertices G 9).card = 3 at hk3
    rw [hhigh, hk3]
  have hownerAdj : ∀ h ∈ H, G.Adj owner h := by
    intro h hh
    have hhHigh : h ∈ squareOrderHighVertices G 9 := by simpa [H, hH] using hh
    have hhN : h ∈ G.neighborFinset owner := by
      have : h ∈ G.neighborFinset owner ∩ squareOrderHighVertices G 9 := by
        rw [hownerHighSet]
        exact hhHigh
      exact (Finset.mem_inter.mp this).1
    exact (G.mem_neighborFinset owner h).mp hhN
  have hKcard : K.card = 3 := by
    simpa [K] using
      squareOrderNine_threeHigh_secondProfile_binThree_original_binOne_neighbors
        G hfree hmin hcard hp hhigh hc2 hc3 hc4 howner
  have hKowner : K ⊆ G.neighborFinset owner := Finset.inter_subset_left
  have hKroot : ∀ p ∈ K, ∃ h ∈ H, G.Adj h p := by
    intro p hp
    have hpB1 := (Finset.mem_inter.mp hp).2
    have hk := (Finset.mem_filter.mp hpB1).2
    change (G.neighborFinset p ∩ squareOrderHighVertices G 9).card = 1 at hk
    obtain ⟨h, hh⟩ := Finset.card_pos.mp (by rw [hk]; omega)
    exact ⟨h, by simpa [H, hH] using (Finset.mem_inter.mp hh).2,
      (G.adj_comm p h).mp ((G.mem_neighborFinset p h).mp
        (Finset.mem_inter.mp hh).1)⟩
  have hownerDefect : ((secondOrderDefectGraph G).neighborFinset owner ∩
      S).card = 2 := by
    have hEinfo := squareOrderNine_threeHigh_secondProfile_owner_defect_neighbors
      G hfree hmin hcover hcard hp hhigh hc2 hc3 hc4 howner
    dsimp only at hEinfo
    have hDE : (secondOrderDefectGraph G).neighborFinset owner = E := by
      simpa [E] using hEinfo.2.1
    rw [hDE]
    exact hfull.2.1 hScard
  have hboundaryTwo : (∑ x ∈ S,
      ((secondOrderDefectGraph G).neighborFinset x ∩
        (Finset.univ \ S)).card) = 2 :=
    hSboundary.trans (hfull.2.1 hScard)
  have hkillNonsym (a b c : V)
      (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
      (hset : ({a, b, c} : Finset V) = H)
      (hba : (G.neighborFinset a ∩ S).card = 1)
      (hbb : (G.neighborFinset b ∩ S).card = 2)
      (hbc' : (G.neighborFinset c ∩ S).card = 3) : False := by
    have hset' : ({a, b, c} : Finset V) = {h₁, h₂, h₃} := by
      simpa [H] using hset
    have hdegOrd' : ∀ x ∉ ({a, b, c} : Finset V), G.degree x = 9 := by
      intro x hx
      apply hdegOrd x
      rw [← hset']
      exact hx
    have hdegHigh' : ∀ h ∈ ({a, b, c} : Finset V), G.degree h = 10 := by
      intro h hh
      apply hdegHigh h
      rw [← hset']
      exact hh
    have hhighIndependent' : ∀ h ∈ ({a, b, c} : Finset V),
        Disjoint (G.neighborFinset h) {a, b, c} := by
      intro h hh
      have hi := hhighIndependent h (by rw [← hset']; exact hh)
      rwa [hset']
    have hdefectHighIsolated' : ∀ h ∈ ({a, b, c} : Finset V),
        (secondOrderDefectGraph G).neighborFinset h = ∅ := by
      intro h hh
      exact hdefectHighIsolated h (by rw [← hset']; exact hh)
    have hpart := orderNine_order18_nonsymmetric_explicit_complement_of_boundary
      G hfree hcard a b c hab hac hbc S
        (by simpa [hset] using hSsub) hScard hba hbb hbc' hboundaryTwo
        hdegOrd' hdegHigh' hhighIndependent' hdefectHighIsolated'
    have hunionSR : S ∪ R = (Finset.univ : Finset V) \ {a, b, c} := by
      have := Finset.union_sdiff_of_subset hSsub
      simpa [R, O, hset] using this
    exact false_of_orderNine_order18_nonsymmetric_explicit_complement
      G hfree a b c hab hac hbc S R hunionSR
        Finset.disjoint_sdiff hScard
        hdegOrd' hdegHigh' hhighIndependent' hdefectHighIsolated' hba hbb hbc'
        (by simpa [R, O, hset] using hpart) owner hownerS
        (by simpa [hset] using hownerH)
        (hownerAdj a (by rw [← hset]; simp))
        (hownerAdj c (by rw [← hset]; simp)) hownerDefect K hKcard
        hKowner (by simpa [hset] using hKroot)
  have hbeta := hfull.1
  unfold orderNineArticulationSmallShoreBetaType at hbeta
  rcases hbeta with ⟨hs, hb⟩ | h27 | h34
  · rcases hb with hsym | h123 | h132 | h213 | h231 | h312 | h321
    · exact false_of_orderNine_order18_symmetric_oriented_articulation_output
        G hfree hmin hcover hcard hp hhigh hc2 hc3 hc4
          h₁ h₂ h₃ h₁₂ h₁₃ h₂₃ hH owner howner S T hunion hdisj
          hScard hTcard hfull hSclosed hTclosed hSboundary
          hdegOrd hdegHigh hhighIndependent
          (by intro h hh; simp only [Finset.mem_insert, Finset.mem_singleton] at hh;
              rcases hh with rfl | rfl | rfl
              · exact hsym.1
              · exact hsym.2.1
              · exact hsym.2.2)
          hdefectHighIsolated
    · exact hkillNonsym h₁ h₂ h₃ h₁₂ h₁₃ h₂₃ rfl h123.1 h123.2.1 h123.2.2
    · exact hkillNonsym h₁ h₃ h₂ h₁₃ h₁₂ h₂₃.symm
        (by ext x; simp only [Finset.mem_insert, Finset.mem_singleton, H]; aesop)
        h132.1 h132.2.2 h132.2.1
    · exact hkillNonsym h₂ h₁ h₃ h₁₂.symm h₂₃ h₁₃
        (by ext x; simp only [Finset.mem_insert, Finset.mem_singleton, H]; aesop)
        h213.2.1 h213.1 h213.2.2
    · exact hkillNonsym h₃ h₁ h₂ h₁₃.symm h₂₃.symm h₁₂
        (by ext x; simp only [Finset.mem_insert, Finset.mem_singleton, H]; aesop)
        h231.2.2 h231.1 h231.2.1
    · exact hkillNonsym h₂ h₃ h₁ h₂₃ h₁₂.symm h₁₃.symm
        (by ext x; simp only [Finset.mem_insert, Finset.mem_singleton, H]; aesop)
        h312.2.1 h312.2.2 h312.1
    · exact hkillNonsym h₃ h₂ h₁ h₂₃.symm h₁₃.symm h₁₂.symm
        (by ext x; simp only [Finset.mem_insert, Finset.mem_singleton, H]; aesop)
        h321.2.2 h321.2.1 h321.1
  · omega
  · omega

/-- The unordered `(18,59)` branch returned by the articulation classifier
is impossible, by orienting the FullType shore as the order-eighteen side. -/
theorem false_of_orderNine_order18_unordered_articulation_output
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ z : V, 9 ≤ G.degree z)
    (hcover : ∀ {u v}, G.Adj u v → G.degree u = 9 ∨ G.degree v = 9)
    (hcard : Fintype.card V = 81)
    (hp : SquareOrderNonregularSectorProfile G 9)
    (hhigh : (squareOrderHighVertices G 9).card = 3)
    (hc2 : squareOrderNineHighIncidenceHistogram G 2 = 0)
    (hc3 : squareOrderNineHighIncidenceHistogram G 3 = 1)
    (hc4 : squareOrderNineHighIncidenceHistogram G 4 = 0)
    (h₁ h₂ h₃ : V) (h₁₂ : h₁ ≠ h₂) (h₁₃ : h₁ ≠ h₃) (h₂₃ : h₂ ≠ h₃)
    (hH : squareOrderHighVertices G 9 = {h₁, h₂, h₃})
    (owner : V) (howner : owner ∈ squareOrderNineLowIncidenceBin G 3)
    (S T : Finset V)
    (hunion : S ∪ T = ((Finset.univ : Finset V) \
      squareOrderHighVertices G 9).erase owner)
    (hdisj : Disjoint S T)
    (horders : (S.card = 18 ∧ T.card = 59) ∨
      (S.card = 59 ∧ T.card = 18))
    (hfull : orderNineArticulationSmallShoreFullType G
        ((secondOrderDefectGraph G).neighborFinset owner ∩
          squareOrderNineLowIncidenceBin G 0) h₁ h₂ h₃ S ∨
      orderNineArticulationSmallShoreFullType G
        ((secondOrderDefectGraph G).neighborFinset owner ∩
          squareOrderNineLowIncidenceBin G 0) h₁ h₂ h₃ T)
    (hSclosed : ∀ x ∈ S, (secondOrderDefectGraph G).neighborFinset x ∩
      ((Finset.univ : Finset V) \
        squareOrderHighVertices G 9).erase owner ⊆ S)
    (hTclosed : ∀ x ∈ T, (secondOrderDefectGraph G).neighborFinset x ∩
      ((Finset.univ : Finset V) \
        squareOrderHighVertices G 9).erase owner ⊆ T)
    (hSboundary : (∑ x ∈ S,
      ((secondOrderDefectGraph G).neighborFinset x ∩
        (Finset.univ \ S)).card) =
      (((secondOrderDefectGraph G).neighborFinset owner ∩
        squareOrderNineLowIncidenceBin G 0) ∩ S).card)
    (hTboundary : (∑ x ∈ T,
      ((secondOrderDefectGraph G).neighborFinset x ∩
        (Finset.univ \ T)).card) =
      (((secondOrderDefectGraph G).neighborFinset owner ∩
        squareOrderNineLowIncidenceBin G 0) ∩ T).card)
    (hdegOrd : ∀ x ∉ ({h₁, h₂, h₃} : Finset V), G.degree x = 9)
    (hdegHigh : ∀ h ∈ ({h₁, h₂, h₃} : Finset V), G.degree h = 10)
    (hhighIndependent : ∀ h ∈ ({h₁, h₂, h₃} : Finset V),
      Disjoint (G.neighborFinset h) ({h₁, h₂, h₃} : Finset V))
    (hdefectHighIsolated : ∀ h ∈ ({h₁, h₂, h₃} : Finset V),
      (secondOrderDefectGraph G).neighborFinset h = ∅) : False := by
  rcases horders with hST | hTS
  · rcases hfull with hfullS | hfullT
    · exact false_of_orderNine_order18_oriented_articulation_output
        G hfree hmin hcover hcard hp hhigh hc2 hc3 hc4
          h₁ h₂ h₃ h₁₂ h₁₃ h₂₃ hH owner howner S T hunion hdisj
          hST.1 hST.2 hfullS hSclosed hTclosed hSboundary
          hdegOrd hdegHigh hhighIndependent hdefectHighIsolated
    · have hbad := hfullT.1
      unfold orderNineArticulationSmallShoreBetaType at hbad
      omega
  · rcases hfull with hfullS | hfullT
    · have hbad := hfullS.1
      unfold orderNineArticulationSmallShoreBetaType at hbad
      omega
    · exact false_of_orderNine_order18_oriented_articulation_output
        G hfree hmin hcover hcard hp hhigh hc2 hc3 hc4
          h₁ h₂ h₃ h₁₂ h₁₃ h₂₃ hH owner howner T S
          (by simpa [Finset.union_comm] using hunion) hdisj.symm
          hTS.2 hTS.1 hfullT hTclosed hSclosed hTboundary
          hdegOrd hdegHigh hhighIndependent hdefectHighIsolated

#print axioms Erdos85.orderNine_order18_nonsymmetric_explicit_complement_of_boundary
#print axioms Erdos85.false_of_orderNine_order18_oriented_articulation_output
#print axioms Erdos85.false_of_orderNine_order18_unordered_articulation_output

end

end Erdos85
