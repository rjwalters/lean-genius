import Proofs.Erdos85OrderFortyNineSmallHighCubeCover
import Proofs.Erdos85OrderFortyNineThreeHighCompleteTerminal
import Proofs.Erdos85OrderFortyNineFiveHighTwoFiber
import Proofs.Erdos85OrderFortyNineFiveHighCanonicalMasks
import Proofs.Erdos85OrderFortyNineVariableHighCnfSemantics
import Proofs.Erdos85OrderFortyNineStrataCapstone

/-!
# Direct consumers for the order-49 small-high cube grids

`OrderFortyNineSmallHighCheckedCubeGrid` proves `CNF.Unsat` for a base
formula.  The older order-49 terminal sockets accepted only one monolithic
`LRAT.check`.  This file supplies the missing semantic bridge, so the 406
checked cube leaves can feed the graph exclusions without first being merged
into seven monolithic LRAT traces.
-/

namespace Erdos85

open SimpleGraph Std Sat
open OrderFortyNineSmallHighCensus

theorem false_of_orderFortyNine_generated_variableHigh_h5_unsat
    {masks : Array Nat} {edges : BitVec 1176}
    (hc : orderFortyNineBooleanConstraints 5 masks edges)
    (hexcluded : OrderFortyNineVariableHighPartitionExcluded (5 : Fin 50) masks)
    (hunsat : (orderFortyNineGeneratedVariableHighSatCnf
      (5 : Fin 50) masks).Unsat) : False := by
  obtain ⟨val, hsegments, _⟩ :=
    orderFortyNineVariableCnfSegments_satisfied (by omega) hc hexcluded
  have hsat := sat_of_orderFortyNineVariableCnfSegmentsSatisfied_of_covered
    hsegments (orderFortyNineGeneratedVariableHighSatCnf_five_covered masks)
  have hfalse := hunsat (satAssignmentOfDimacs val)
  rw [hsat] at hfalse
  contradiction

theorem false_of_orderFortyNine_generated_h3_scout_unsat
    {masks : Array Nat} {geometry : Array DimacsClause} {edges : BitVec 1176}
    (hc : orderFortyNineBooleanConstraints 3 masks edges)
    (hexcluded : OrderFortyNineVariableHighPartitionExcluded (3 : Fin 50) masks)
    (hgeometryNonzero : ∀ clause ∈ geometry, DimacsClauseNonzero clause)
    (hgeometryBounded : dimacsFormulaBounded 1176 geometry)
    (hgeometrySat : dimacsFormulaSatisfied
      (orderFortyNineDimacsEdgeVal edges) geometry)
    (hunsat : (orderFortyNineGeneratedThreeHighScoutCnf masks geometry).Unsat) :
    False := by
  obtain ⟨val, hsegments, hagree⟩ :=
    orderFortyNineVariableCnfSegments_satisfied (by omega) hc hexcluded
  have hgeometrySat' : dimacsFormulaSatisfied val geometry :=
    dimacsFormulaSatisfied_of_bounded_agree hgeometrySat hgeometryBounded
      (fun id hid => (hagree id hid).symm)
  have hsat := sat_of_orderFortyNineThreeHighScoutSegments hsegments
    hgeometrySat'
    (orderFortyNineGeneratedThreeHighScoutCnf_covered masks geometry
      hgeometryNonzero)
  have hfalse := hunsat (satAssignmentOfDimacs val)
  rw [hsat] at hfalse
  contradiction

theorem false_of_threeHighDistTwoScoutAlignedLabeling_unsat
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (E : Equiv.Perm (Fin 49))
    (haligned : ThreeHighDistTwoScoutAlignedLabeling G E)
    (hunsat : orderFortyNineGeneratedThreeHighDistTwoScoutCnf.Unsat) : False := by
  rcases haligned with ⟨hlabel, h0, h1, h2, hroot⟩
  let H := orderFortyNineRelabeledGraph G E
  let edges := orderFortyNineGraphEdges H
  apply false_of_orderFortyNine_generated_h3_scout_unsat
    (edges := edges)
    (orderFortyNineBooleanConstraints_of_smallHighAlignedLabeling
      (h := 3) (by omega) G hfree E orderFortyNineThreeHighDistTwoMasks hlabel)
    orderFortyNineThreeHighDistTwoMasks_partitionExcluded
    orderFortyNineThreeHighDistTwoGeometryClauses_nonzero
    orderFortyNineThreeHighDistTwoGeometryClauses_bounded
    (orderFortyNineThreeHighDistTwoGeometryClauses_satisfied
      (orderFortyNineGraphPinnedMatchingRealized_edges H h0)
      (orderFortyNineGraphPinnedMatchingRealized_edges H h1)
      (orderFortyNineGraphPinnedMatchingRealized_edges H h2)
      (orderFortyNineThreeHighDistTwoRootEmptyGraphRealized_edges H hroot))
    hunsat

theorem false_of_threeHighDistOneC2ScoutAlignedLabeling_unsat
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (E : Equiv.Perm (Fin 49))
    (haligned : ThreeHighDistOneC2ScoutAlignedLabeling G E)
    (hunsat : orderFortyNineGeneratedThreeHighDistOneC2ScoutCnf.Unsat) : False := by
  rcases haligned with ⟨hlabel, h0, h1, h2⟩
  let H := orderFortyNineRelabeledGraph G E
  let edges := orderFortyNineGraphEdges H
  apply false_of_orderFortyNine_generated_h3_scout_unsat
    (edges := edges)
    (orderFortyNineBooleanConstraints_of_smallHighAlignedLabeling
      (h := 3) (by omega) G hfree E orderFortyNineThreeHighDistOneC2Masks hlabel)
    orderFortyNineThreeHighDistOneC2Masks_partitionExcluded
    orderFortyNineThreeHighDistOneC2GeometryClauses_nonzero
    orderFortyNineThreeHighDistOneC2GeometryClauses_bounded
    (orderFortyNineThreeHighDistOneC2GeometryClauses_satisfied
      (orderFortyNineGraphPinnedMatchingRealized_edges H h0)
      (orderFortyNineGraphPinnedMatchingRealized_edges H h1)
      (orderFortyNineGraphPinnedMatchingRealized_edges H h2))
    hunsat

theorem false_of_threeHighDistOneB1ScoutAlignedLabeling_unsat
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (E : Equiv.Perm (Fin 49))
    (haligned : ThreeHighDistOneB1ScoutAlignedLabeling G E)
    (hunsat : orderFortyNineGeneratedThreeHighDistOneB1ScoutCnf.Unsat) : False := by
  rcases haligned with ⟨hlabel, h0, h1, h2⟩
  let H := orderFortyNineRelabeledGraph G E
  let edges := orderFortyNineGraphEdges H
  apply false_of_orderFortyNine_generated_h3_scout_unsat
    (edges := edges)
    (orderFortyNineBooleanConstraints_of_smallHighAlignedLabeling
      (h := 3) (by omega) G hfree E
        orderFortyNineThreeHighDistOneNoCoincidenceMasks hlabel)
    orderFortyNineThreeHighDistOneNoCoincidenceMasks_partitionExcluded
    orderFortyNineThreeHighDistOneB1GeometryClauses_nonzero
    orderFortyNineThreeHighDistOneB1GeometryClauses_bounded
    (orderFortyNineThreeHighDistOneB1GeometryClauses_satisfied
      (orderFortyNineGraphPinnedMatchingRealized_edges H h0)
      (orderFortyNineGraphPinnedMatchingRealized_edges H h1)
      (orderFortyNineGraphPinnedMatchingRealized_edges H h2))
    hunsat

theorem false_of_threeHighDistOneC1ScoutAlignedLabeling_unsat
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (E : Equiv.Perm (Fin 49))
    (haligned : ThreeHighDistOneC1ScoutAlignedLabeling G E)
    (hunsat : orderFortyNineGeneratedThreeHighDistOneC1ScoutCnf.Unsat) : False := by
  rcases haligned with ⟨hlabel, h0, h1, h2⟩
  let H := orderFortyNineRelabeledGraph G E
  let edges := orderFortyNineGraphEdges H
  apply false_of_orderFortyNine_generated_h3_scout_unsat
    (edges := edges)
    (orderFortyNineBooleanConstraints_of_smallHighAlignedLabeling
      (h := 3) (by omega) G hfree E
        orderFortyNineThreeHighDistOneNoCoincidenceMasks hlabel)
    orderFortyNineThreeHighDistOneNoCoincidenceMasks_partitionExcluded
    orderFortyNineThreeHighDistOneC1GeometryClauses_nonzero
    orderFortyNineThreeHighDistOneC1GeometryClauses_bounded
    (orderFortyNineThreeHighDistOneC1GeometryClauses_satisfied
      (orderFortyNineGraphPinnedMatchingRealized_edges H h0)
      (orderFortyNineGraphPinnedMatchingRealized_edges H h1)
      (orderFortyNineGraphPinnedMatchingRealized_edges H h2))
    hunsat

theorem orderFortyNineStratumExcluded_three_of_cubeBaseUnsat
    (hb1 : orderFortyNineGeneratedThreeHighDistOneB1ScoutCnf.Unsat)
    (hc1 : orderFortyNineGeneratedThreeHighDistOneC1ScoutCnf.Unsat)
    (hc2 : orderFortyNineGeneratedThreeHighDistOneC2ScoutCnf.Unsat)
    (hdist2 : orderFortyNineGeneratedThreeHighDistTwoScoutCnf.Unsat) :
    OrderFortyNineStratumExcluded 3 := by
  have hb1Excluded : ThreeHighDistOneB1Excluded := by
    intro G _ _ _ hfree hmin D hcase
    obtain ⟨E, hE⟩ := orderFortyNine_threeHighDistOneB1AlignedCover G
      inferInstance inferInstance inferInstance hfree hmin D hcase
    exact false_of_threeHighDistOneB1ScoutAlignedLabeling_unsat G hfree E hE hb1
  have hc1Excluded : ThreeHighDistOneC1Excluded := by
    intro G _ _ _ hfree hmin D hcase
    obtain ⟨E, hE⟩ := orderFortyNine_threeHighDistOneC1AlignedCover G
      inferInstance inferInstance inferInstance hfree hmin D hcase
    exact false_of_threeHighDistOneC1ScoutAlignedLabeling_unsat G hfree E hE hc1
  have hcover : ThreeHighDistinctRootAlignedCover :=
    threeHighDistinctRootAlignedCover_of_b1_c1_c2 hb1Excluded hc1Excluded
      orderFortyNine_threeHighDistOneC2AlignedCover
  have hdistinct : ThreeHighDistinctRootExcluded := by
    intro G _ _ _ hfree hmin v1 v2 v3 u12 u13 u23 hHigh
      hv1 hv2 hv3 h12 h13 h23 hu12 hu13 hu23 h1213 h1223 h1323
    obtain ⟨E, hE⟩ := hcover G inferInstance inferInstance inferInstance
      hfree hmin v1 v2 v3 u12 u13 u23 hHigh hv1 hv2 hv3 h12 h13 h23
      hu12 hu13 hu23 h1213 h1223 h1323
    exact false_of_threeHighDistOneC2ScoutAlignedLabeling_unsat G hfree E hE hc2
  intro G _ _ _ hfree hmin hHighCard
  obtain ⟨v1, v2, v3, u12, u13, u23, hHigh,
      hv1, hv2, hv3, h12, h13, h23, hu12, hu13, hu23, hroots⟩ :=
    orderFortyNine_three_high_normal_form
      G hfree hmin (Fintype.card_fin 49) hHighCard
  rcases hroots with ⟨h1213, h1323⟩ | hdistinctRoots
  · have hu12mem : u12 ∈ G.neighborFinset v1 ∩ G.neighborFinset v2 := by
      simp [hu12]
    have hu13mem : u13 ∈ G.neighborFinset v1 ∩ G.neighborFinset v3 := by
      simp [hu13]
    have hs1 : G.Adj u12 v1 :=
      ((G.mem_neighborFinset v1 u12).mp (Finset.mem_inter.mp hu12mem).1).symm
    have hs2 : G.Adj u12 v2 :=
      ((G.mem_neighborFinset v2 u12).mp (Finset.mem_inter.mp hu12mem).2).symm
    have hs3 : G.Adj u12 v3 := by
      have hz : G.Adj u13 v3 :=
        ((G.mem_neighborFinset v3 u13).mp (Finset.mem_inter.mp hu13mem).2).symm
      simpa [h1213] using hz
    have hsLow : G.degree u12 = 7 :=
      orderFortyNine_neighbor_degree_seven_of_degreeEight
        G hfree hmin (Fintype.card_fin 49) hv1 hs1.symm
    obtain ⟨E, hEv1, hEv2, hEv3, hN0, hN1, hN2,
        hmatch0, hmatch1, hmatch2, hroot⟩ :=
      exists_orderFortyNine_threeHighDistTwo_geometryLabeling
        G hfree hmin (Fintype.card_fin 49) hv1 hv2 hv3 hsLow
        h12 h13 h23 hs1 hs2 hs3 hHigh
    exact false_of_threeHighDistTwoScoutAlignedLabeling_unsat G hfree E
      ⟨orderFortyNineThreeHighDistTwo_smallHighAlignedLabeling
        G hfree hmin hHigh E hEv1 hEv2 hEv3 hN0 hN1 hN2,
        hmatch0, hmatch1, hmatch2, hroot⟩ hdist2
  · exact hdistinct G inferInstance inferInstance inferInstance
      hfree hmin v1 v2 v3 u12 u13 u23 hHigh hv1 hv2 hv3
      h12 h13 h23 hu12 hu13 hu23
      hdistinctRoots.1 hdistinctRoots.2.1 hdistinctRoots.2.2

theorem orderFortyNineStratumExcluded_five_of_cubeBaseUnsat
    (h0 : (orderFortyNineGeneratedVariableHighSatCnf (5 : Fin 50)
      orderFortyNineFiveHighT0Masks).Unsat)
    (h1 : (orderFortyNineGeneratedVariableHighSatCnf (5 : Fin 50)
      orderFortyNineFiveHighT1Masks).Unsat)
    (h2 : (orderFortyNineGeneratedVariableHighSatCnf (5 : Fin 50)
      orderFortyNineFiveHighT2Masks).Unsat) :
    OrderFortyNineStratumExcluded 5 := by
  apply orderFortyNineStratumExcluded_five_of_representativeExclusions
  intro index hindex edges hc
  interval_cases index
  · have hm : fiveHighRepresentativeMasks 0 =
        orderFortyNineFiveHighT0Masks := by native_decide
    rw [hm] at hc
    exact false_of_orderFortyNine_generated_variableHigh_h5_unsat hc
      orderFortyNineFiveHighT0Masks_partitionExcluded h0
  · have hm : fiveHighRepresentativeMasks 1 =
        orderFortyNineFiveHighT1Masks := by native_decide
    rw [hm] at hc
    exact false_of_orderFortyNine_generated_variableHigh_h5_unsat hc
      orderFortyNineFiveHighT1Masks_partitionExcluded h1
  · have hm : fiveHighRepresentativeMasks 2 =
        orderFortyNineFiveHighT2Masks := by native_decide
    rw [hm] at hc
    exact false_of_orderFortyNine_generated_variableHigh_h5_unsat hc
      orderFortyNineFiveHighT2Masks_partitionExcluded h2

/-- The exact Tier-A insertion socket.  Each hypothesis is produced from its
58 checked leaves by `orderFortyNineSmallHigh_unsat_of_checkedCubeGrid`. -/
theorem not_c4FreeMinDegreeWitness_fortyNine_seven_of_smallHighCubeBaseUnsat
    (h1 : OrderFortyNineStratumExcluded 1)
    (hb1 : orderFortyNineGeneratedThreeHighDistOneB1ScoutCnf.Unsat)
    (hc1 : orderFortyNineGeneratedThreeHighDistOneC1ScoutCnf.Unsat)
    (hc2 : orderFortyNineGeneratedThreeHighDistOneC2ScoutCnf.Unsat)
    (hdist2 : orderFortyNineGeneratedThreeHighDistTwoScoutCnf.Unsat)
    (h50 : (orderFortyNineGeneratedVariableHighSatCnf (5 : Fin 50)
      orderFortyNineFiveHighT0Masks).Unsat)
    (h51 : (orderFortyNineGeneratedVariableHighSatCnf (5 : Fin 50)
      orderFortyNineFiveHighT1Masks).Unsat)
    (h52 : (orderFortyNineGeneratedVariableHighSatCnf (5 : Fin 50)
      orderFortyNineFiveHighT2Masks).Unsat)
    (h7 : OrderFortyNineStratumExcluded 7) :
    ¬ C4FreeMinDegreeWitness 49 7 := by
  exact not_c4FreeMinDegreeWitness_fortyNine_seven_of_strata h1
    (orderFortyNineStratumExcluded_three_of_cubeBaseUnsat hb1 hc1 hc2 hdist2)
    (orderFortyNineStratumExcluded_five_of_cubeBaseUnsat h50 h51 h52) h7

end Erdos85

#print axioms Erdos85.orderFortyNineStratumExcluded_three_of_cubeBaseUnsat
#print axioms Erdos85.not_c4FreeMinDegreeWitness_fortyNine_seven_of_smallHighCubeBaseUnsat
