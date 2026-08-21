import Proofs.Erdos85OddSquareOrderNineThreeHighTriangleCensus

/-! # The bin-one defect core in the second q = 9 three-high profile

Node: B.3 / GAP B-CLASSIFY.  In the `(50,27,0,1,0)` profile the bin-one
vertices form a 2-regular defect core.  Moreover, every core edge incident
to an original bin-three/bin-one pair is forced to be antipodal.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- In the `(50,27,0,1,0)` profile, every bin-one vertex has exactly five
bin-zero and two bin-one defect neighbors, and no bin-three defect neighbor. -/
theorem squareOrderNine_threeHigh_secondProfile_binOne_defect_neighbors
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
    (hc4 : squareOrderNineHighIncidenceHistogram G 4 = 0)
    {x : V} (hx : x ∈ squareOrderNineLowIncidenceBin G 1) :
    let D := secondOrderDefectGraph G
    let B := squareOrderNineLowIncidenceBin G
    (D.neighborFinset x ∩ B 0).card = 5 ∧
      (D.neighborFinset x ∩ B 1).card = 2 ∧
      (D.neighborFinset x ∩ B 2).card = 0 ∧
      (D.neighborFinset x ∩ B 3).card = 0 := by
  classical
  dsimp only
  let D := secondOrderDefectGraph G
  let B := squareOrderNineLowIncidenceBin G
  have hB2 : B 2 = ∅ := by
    rw [← Finset.card_eq_zero,
      squareOrderNine_lowIncidenceBin_card_eq_histogram_of_ne_zero
        G hp (i := 2) (by omega), hc2]
  have hB4 : B 4 = ∅ := by
    rw [← Finset.card_eq_zero,
      squareOrderNine_lowIncidenceBin_card_eq_histogram_of_ne_zero
        G hp (i := 4) (by omega), hc4]
  have hpnt := squareOrderNine_lowIncidenceBin_pointwise_ledger
    G hfree hmin hcover hcard hx
  dsimp only at hpnt
  rw [hhigh] at hpnt
  change D.degree x = 8 - 1 ∧
    (∑ y ∈ D.neighborFinset x, squareOrderHighIncidenceCount G 9 y) =
      3 - 1 at hpnt
  norm_num at hpnt
  have hpart := squareOrderNine_defectNeighbor_bin_partition
    G hfree hmin hcard hp x
  dsimp only at hpart
  change
    (∑ j ∈ Finset.range 5, (D.neighborFinset x ∩ B j).card) = D.degree x ∧
      (∑ j ∈ Finset.range 5, j * (D.neighborFinset x ∩ B j).card) =
        ∑ y ∈ D.neighborFinset x, squareOrderHighIncidenceCount G 9 y at hpart
  rw [hpnt.1, hpnt.2] at hpart
  norm_num [Finset.sum_range_succ] at hpart
  rw [hB2, hB4] at hpart
  norm_num at hpart
  have hB0card : (D.neighborFinset x ∩ B 0).card = 5 := by omega
  have hB1card : (D.neighborFinset x ∩ B 1).card = 2 := by omega
  have hB3card : (D.neighborFinset x ∩ B 3).card = 0 := by omega
  change (D.neighborFinset x ∩ B 0).card = 5 ∧
    (D.neighborFinset x ∩ B 1).card = 2 ∧
    (D.neighborFinset x ∩ B 2).card = 0 ∧
    (D.neighborFinset x ∩ B 3).card = 0
  refine ⟨hB0card, hB1card, ?_, hB3card⟩
  rw [hB2]
  simp

/-- The full 27-vertex bin-one set in the second profile induces a
two-regular graph in the second-order defect graph. -/
theorem squareOrderNine_threeHigh_secondProfile_binOne_defect_twoRegular
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
    (hc4 : squareOrderNineHighIncidenceHistogram G 4 = 0) :
    let D := secondOrderDefectGraph G
    let B := squareOrderNineLowIncidenceBin G
    ∀ y : ↥(↑(B 1) : Set V), (D.induce (↑(B 1) : Set V)).degree y = 2 := by
  classical
  dsimp only
  let D := secondOrderDefectGraph G
  let B := squareOrderNineLowIncidenceBin G
  intro y
  have hyB : y.1 ∈ B 1 := y.2
  have hyType :=
    squareOrderNine_threeHigh_secondProfile_binOne_defect_neighbors
      G hfree hmin hcover hcard hp hhigh hc2 hc4 hyB
  dsimp only at hyType
  rw [degree_induce_finset_eq_card_inter]
  exact hyType.2.1

/-- If a bin-three vertex is originally adjacent to a bin-one vertex, then
every bin-one defect edge at that partner is antipodal.  The other endpoint's
unique high neighbor is also adjacent to the bin-three vertex, so an original
partner edge would create a 4-cycle. -/
theorem squareOrderNine_threeHigh_secondProfile_binThree_partner_coreEdge_antipodal
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hhigh : (squareOrderHighVertices G 9).card = 3)
    {x y p : V}
    (hx : x ∈ squareOrderNineLowIncidenceBin G 3)
    (hy : y ∈ squareOrderNineLowIncidenceBin G 1)
    (hp : p ∈ squareOrderNineLowIncidenceBin G 1)
    (hyx : G.Adj y x)
    (hDyp : (secondOrderDefectGraph G).Adj y p) :
    (antipodalGraph G).Adj y p := by
  classical
  let H := squareOrderHighVertices G 9
  let k := squareOrderHighIncidenceCount G 9
  have hkp : k p = 1 := (Finset.mem_filter.mp hp).2
  have hpHighNonempty : (G.neighborFinset p ∩ H).Nonempty := by
    rw [← Finset.card_pos]
    change 0 < k p
    omega
  obtain ⟨b, hb⟩ := hpHighNonempty
  have ⟨hbp, hbH⟩ := Finset.mem_inter.mp hb
  have hbpAdj : G.Adj b p :=
    (G.adj_comm p b).mp ((G.mem_neighborFinset p b).mp hbp)
  have hkx : k x = 3 := (Finset.mem_filter.mp hx).2
  have hxAll : G.neighborFinset x ∩ H = H := by
    apply Finset.eq_of_subset_of_card_le
    · exact Finset.inter_subset_right
    · change H.card ≤ k x
      rw [hkx, hhigh]
  have hbx : G.Adj b x := by
    have hbNx : b ∈ G.neighborFinset x :=
      (Finset.mem_inter.mp (show b ∈ G.neighborFinset x ∩ H by
        rw [hxAll]
        exact hbH)).1
    exact (G.adj_comm x b).mp ((G.mem_neighborFinset x b).mp hbNx)
  have hpx : p ≠ x := by
    intro h
    subst x
    have hkp' := (Finset.mem_filter.mp hp).2
    have hkx' := (Finset.mem_filter.mp hx).2
    omega
  have hby : b ≠ y := by
    intro h
    subst b
    have hyLow := (Finset.mem_filter.mp hy).1
    exact (Finset.mem_sdiff.mp hyLow).2 hbH
  have hpAnti : (antipodalGraph G).Adj p y :=
    antipodal_of_defectMate_crosses_shared_high
      G hfree (x := p) (u := x) (y := y) (r := b)
        hpx hby hbpAdj hbx hDyp.symm hyx
  exact hpAnti.symm

/-- Two distinct bin-one partners of the rare bin-three vertex cannot be
defect-adjacent: the bin-three vertex is already their common original
neighbor.  Thus the three marked vertices form an independent set in the
two-regular defect core. -/
theorem squareOrderNine_threeHigh_secondProfile_binThree_partners_not_defectAdjacent
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    {x y z : V} (hyz : y ≠ z)
    (hyx : G.Adj y x) (hzx : G.Adj z x) :
    ¬ (secondOrderDefectGraph G).Adj y z := by
  exact not_secondOrderDefect_adj_of_commonNeighbor
    G hfree hyz hyx hzx

/-- In the second profile the bin-three vertex marks exactly three vertices
of the 27-vertex two-regular bin-one core. -/
theorem squareOrderNine_threeHigh_secondProfile_marked_core_cardinalities
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ z : V, 9 ≤ G.degree z)
    (hcard : Fintype.card V = 81)
    (hp : SquareOrderNonregularSectorProfile G 9)
    (hhigh : (squareOrderHighVertices G 9).card = 3)
    (hc2 : squareOrderNineHighIncidenceHistogram G 2 = 0)
    (hc3 : squareOrderNineHighIncidenceHistogram G 3 = 1)
    (hc4 : squareOrderNineHighIncidenceHistogram G 4 = 0)
    {x : V} (hx : x ∈ squareOrderNineLowIncidenceBin G 3) :
    let B := squareOrderNineLowIncidenceBin G
    (B 1).card = 27 ∧ (G.neighborFinset x ∩ B 1).card = 3 := by
  classical
  dsimp only
  constructor
  · have hprofiles := squareOrderNine_highIncidence_profile_of_three_high
      G hcard hp hhigh
    dsimp only at hprofiles
    rcases hprofiles with hfirst | hsecond
    · rw [hfirst.2.2.2.1] at hc3
      omega
    · exact (squareOrderNine_lowIncidenceBin_card_eq_histogram_of_ne_zero
        G hp (i := 1) (by omega)).trans hsecond.2.1
  · exact squareOrderNine_threeHigh_secondProfile_binThree_original_binOne_neighbors
      G hfree hmin hcard hp hhigh hc2 hc3 hc4 hx

end

end Erdos85

#print axioms Erdos85.squareOrderNine_threeHigh_secondProfile_binOne_defect_neighbors
#print axioms Erdos85.squareOrderNine_threeHigh_secondProfile_binOne_defect_twoRegular
#print axioms Erdos85.squareOrderNine_threeHigh_secondProfile_binThree_partner_coreEdge_antipodal
#print axioms Erdos85.squareOrderNine_threeHigh_secondProfile_binThree_partners_not_defectAdjacent
#print axioms Erdos85.squareOrderNine_threeHigh_secondProfile_marked_core_cardinalities
