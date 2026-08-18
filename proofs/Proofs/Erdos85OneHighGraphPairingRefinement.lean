import Proofs.Erdos85MatchingPairingRefinement
import Proofs.Erdos85OneHighGraphMissLabelCounting
import Proofs.Erdos85OneHighGlobalMissLabelCounting
import Proofs.Erdos85OneHighPairingRefinementOfFn
import Proofs.Erdos85OneHighRawPresentation
import Proofs.Erdos85OneHighV2F3bRawLedger

/-! # The pairing refinement induced by a raw one-high graph -/

namespace Erdos85

noncomputable section

open SimpleGraph

/-- In a far target column, the fiber of the unique miss-label function on
matched vertices is exactly the directed graph miss count.  The reverse
direction uses dirty conservation: a vertex missing a far branch has positive
internal degree, hence degree one in its C4-free source branch. -/
theorem card_oneHighMatchingLabelFiber_eq_highBranchMissCount
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {v : V}
    (hv : G.degree v = 8)
    (hexternal : externalRepairCandidates G v = ∅)
    (houterDegree : ∀ {a : V}, a ∈ secondLayer G v → G.degree a = 7)
    (rootMate : {z : V // z ∈ G.neighborSet v} →
      {z : V // z ∈ G.neighborSet v})
    (hrootAdj : ∀ s, G.Adj s.1 (rootMate s).1)
    (s u : {z : V // z ∈ G.neighborSet v})
    (hu : u ∈ ((Finset.univ.erase s).erase (rootMate s))) :
    (matchingLabelFiber
      (oneHighMatchedMissLabel G hfree hv hexternal houterDegree
        rootMate hrootAdj s) u).card =
      highBranchMissCount G v s u := by
  classical
  let X := OneHighMatchedBranchVertices G v s
  let label : X → {z : V // z ∈ G.neighborSet v} :=
    oneHighMatchedMissLabel G hfree hv hexternal houterDegree
      rootMate hrootAdj s
  let M := (secondLayerBranch G v s).filter fun a =>
    (G.neighborFinset a ∩ secondLayerBranch G v u).card = 0
  change (matchingLabelFiber label u).card = M.card
  apply Finset.card_bij (fun x _ => x.1.1)
  · intro x hx
    have hxLabel : label x = u := (Finset.mem_filter.mp hx).2
    have hxMatched : (G.neighborFinset x.1.1 ∩
        secondLayerBranch G v s).card = 1 := by
      rw [← degree_induce_secondLayerBranch_eq_card_inter]
      exact x.2
    have hmem := oneHighMissingBranch_mem_of_matched
      G hfree hv hexternal houterDegree rootMate hrootAdj s
        x.1.1 x.1.2 hxMatched
    have hmiss := (Finset.mem_filter.mp hmem).2
    have hxLabel' : oneHighMissingBranch G v rootMate s x.1.1 = u := by
      simpa [label, oneHighMatchedMissLabel] using hxLabel
    rw [hxLabel'] at hmiss
    apply Finset.mem_filter.mpr
    exact ⟨x.1.2, hmiss⟩
  · intro x _ y _ hxy
    exact Subtype.ext (Subtype.ext hxy)
  · intro a ha
    have haParts := Finset.mem_filter.mp ha
    have haSecond : a ∈ secondLayer G v := by
      rw [secondLayer]
      exact Finset.mem_biUnion.mpr ⟨s, Finset.mem_univ _, haParts.1⟩
    have hfarCard := card_farBranch_misses_eq_internalDegree
      G hfree (d := 7) (by omega) hexternal s (rootMate s)
        (hrootAdj s) a haParts.1 (houterDegree haSecond)
    have huMem : u ∈
        (((Finset.univ.erase s).erase (rootMate s)).filter fun w =>
          (G.neighborFinset a ∩ secondLayerBranch G v w).card = 0) :=
      Finset.mem_filter.mpr ⟨hu, haParts.2⟩
    have hpos : 0 < (G.neighborFinset a ∩
        secondLayerBranch G v s).card := by
      have : 0 < ((((Finset.univ.erase s).erase (rootMate s)).filter fun w =>
          (G.neighborFinset a ∩ secondLayerBranch G v w).card = 0).card) :=
        Finset.card_pos.mpr ⟨u, huMem⟩
      omega
    have hle := degree_induce_secondLayerBranch_le_one G hfree v s ⟨a, haParts.1⟩
    rw [degree_induce_secondLayerBranch_eq_card_inter] at hle
    have hle' : (G.neighborFinset a ∩
        secondLayerBranch G v s).card ≤ 1 := by
      simpa using hle
    have haMatched : (G.neighborFinset a ∩
        secondLayerBranch G v s).card = 1 := by omega
    let x : X := ⟨⟨a, haParts.1⟩, by
      rw [degree_induce_secondLayerBranch_eq_card_inter]
      exact haMatched⟩
    have heq := eq_oneHighMissingBranch_of_matched_of_mem
      G hfree hv hexternal houterDegree rootMate hrootAdj s
        a haParts.1 haMatched u
        (Finset.mem_filter.mpr ⟨hu, haParts.2⟩)
    refine ⟨x, ?_, rfl⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    simpa [label, x, oneHighMatchedMissLabel] using heq.symm

theorem card_matchingLabelFiber_equiv_comp
    {X L K : Type*} [Fintype X] [DecidableEq X]
    [DecidableEq L] [DecidableEq K]
    (e : L ≃ K) (label : X → L) (k : K) :
    (matchingLabelFiber (fun x => e (label x)) k).card =
      (matchingLabelFiber label (e.symm k)).card := by
  congr 1
  ext x
  simp only [matchingLabelFiber, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h
    apply e.injective
    simpa using h
  · intro h
    simpa [h]

/-- The concrete sorted pairing chosen in one canonical source branch. -/
def oneHighGraphSourcePairing
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {v : V} (hv : G.degree v = 8)
    (p : OneHighRawV2Presentation G hfree v) (source : Fin 8) :
    List OneHighLabelPair :=
  let s := p.branchLabel.symm source
  matchingPairingListSorted (oneHighInternalMate G hfree v s) fun x =>
    p.branchLabel (oneHighMatchedMissLabel G hfree hv p.external_empty
      p.outer_degree p.mate p.mate_adj s x)

/-- The graph table restricted to the 24 coordinates actually stored by the
inventory.  Diagonal and standard-mate coordinates are deliberately zero. -/
def oneHighGraphRelevantMissTable
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj] (profile : Nat) :
    OneHighMissTable := fun c j =>
  if c < 8 ∧ j < 8 ∧ c ≠ j ∧ j ≠ (c ^^^ 1) then
    oneHighFamilyTableGet (oneHighFamilyGraphTable R profile) c j
  else 0

theorem oneHighFamilyTableGet_graphRelevantMissTable
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj] (profile : Nat)
    (source label : Fin 8) :
    oneHighFamilyTableGet (oneHighGraphRelevantMissTable R profile)
        source.val label.val =
      oneHighGraphRelevantMissTable R profile source.val label.val := by
  fin_cases source <;> fin_cases label <;>
    simp [oneHighFamilyTableGet, oneHighGraphRelevantMissTable]

theorem oneHighGraphSourcePairing_endpointCount
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {v : V} (hv : G.degree v = 8)
    (p : OneHighRawV2Presentation G hfree v) (source label : Fin 8) :
    oneHighPairingEndpointCount
        (oneHighGraphSourcePairing G hfree hv p source) label =
      oneHighGraphRelevantMissTable
          (oneHighRelabeledLeafGraph G v
            (oneHighLeafFinFortyEquiv G hfree v p.branchLabel p.leafLabel))
          p.profile
        source.val label.val := by
  classical
  let s := p.branchLabel.symm source
  let u := p.branchLabel.symm label
  let rootLabel := oneHighMatchedMissLabel G hfree hv p.external_empty
    p.outer_degree p.mate p.mate_adj s
  let R := oneHighRelabeledLeafGraph G v
    (oneHighLeafFinFortyEquiv G hfree v p.branchLabel p.leafLabel)
  change oneHighPairingEndpointCount
      (matchingPairingListSorted (oneHighInternalMate G hfree v s)
        (fun x => p.branchLabel (rootLabel x))) label = _
  have hend := matchingPairingListSorted_endpointCount
    (oneHighInternalMate G hfree v s)
    (fun x => p.branchLabel (rootLabel x)) label
    (degreeOneMate_involutive _ _)
    (degreeOneMate_ne _ _)
  rw [hend]
  rw [card_matchingLabelFiber_equiv_comp p.branchLabel rootLabel label]
  by_cases hus : u = s
  · have hls : label = source := by
      apply p.branchLabel.symm.injective
      simpa [u, s] using hus
    subst label
    have hfiber : matchingLabelFiber rootLabel s = ∅ := by
      ext x
      simp only [matchingLabelFiber, Finset.mem_filter, Finset.mem_univ,
        true_and]
      constructor
      · intro hxLabel
        have hfar := oneHighMatchedMissLabel_mem G hfree hv p.external_empty
          p.outer_degree p.mate p.mate_adj s x
        have hbase := (Finset.mem_filter.mp hfar).1
        have hne := (Finset.mem_erase.mp
          (Finset.mem_erase.mp hbase).2).1
        exact (hne hxLabel).elim
      · intro hx
        simpa using hx
    change (matchingLabelFiber rootLabel s).card = _
    rw [hfiber]
    simp [oneHighGraphRelevantMissTable]
  · by_cases hum : u = p.mate s
    · have hlm : label = oneHighStandardMate source := by
        calc
          label = p.branchLabel u := by simp [u]
          _ = p.branchLabel (p.mate s) := congrArg p.branchLabel hum
          _ = oneHighStandardMate (p.branchLabel s) := p.branch_mate s
          _ = oneHighStandardMate source := by simp [s]
      have hfiber : matchingLabelFiber rootLabel u = ∅ := by
        ext x
        simp only [matchingLabelFiber, Finset.mem_filter, Finset.mem_univ,
          true_and]
        constructor
        · intro hxLabel
          have hfar := oneHighMatchedMissLabel_mem G hfree hv p.external_empty
            p.outer_degree p.mate p.mate_adj s x
          have hbase := (Finset.mem_filter.mp hfar).1
          have hne := (Finset.mem_erase.mp hbase).1
          exact (hne (hxLabel.trans hum)).elim
        · intro hx
          simpa using hx
      rw [hfiber]
      simp [oneHighGraphRelevantMissTable, hlm,
        oneHighStandardMate_val_eq_xor]
    · have huFar : u ∈ ((Finset.univ.erase s).erase (p.mate s)) := by
        simp [hus, hum]
      rw [card_oneHighMatchingLabelFiber_eq_highBranchMissCount
        G hfree hv p.external_empty p.outer_degree p.mate p.mate_adj s u huFar]
      have htable := oneHighFamilyGraphTable_eq_highBranchMissCount
        G hfree v p.mate p.branchLabel p.branch_mate p.leafLabel
          p.profile p.constraints s u hus hum
      have hlabelS : p.branchLabel s = source := by simp [s]
      have hlabelU : p.branchLabel u = label := by simp [u]
      have hget := oneHighFamilyTableGet_graphTable_eq p.profile R
        p.constraints source label
          (fun h => hus (p.branchLabel.injective (by simpa [s, u] using h)))
          (fun h => hum (p.branchLabel.injective (by
            rw [p.branch_mate s]
            simpa [s, u] using h)))
      simp only [oneHighGraphRelevantMissTable]
      rw [if_pos]
      · rw [hget]
        simpa [R, hlabelS, hlabelU] using htable.symm
      · refine ⟨source.isLt, label.isLt, ?_, ?_⟩
        · intro h
          apply hus
          apply p.branchLabel.injective
          simpa [s, u] using (Fin.ext h).symm
        · exact fun h => hum (p.branchLabel.injective (by
            rw [p.branch_mate s]
            apply Fin.ext
            simpa [s, u, oneHighStandardMate_val_eq_xor] using h))

theorem oneHighGraphSourcePairing_compatible
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {v : V} (hv : G.degree v = 8)
    (p : OneHighRawV2Presentation G hfree v) (source : Fin 8) :
    oneHighSourcePairingCompatible
      (oneHighGraphRelevantMissTable
        (oneHighRelabeledLeafGraph G v
          (oneHighLeafFinFortyEquiv G hfree v p.branchLabel p.leafLabel))
        p.profile)
      source (oneHighGraphSourcePairing G hfree hv p source) = true := by
  rw [oneHighSourcePairingCompatible, List.all_eq_true]
  intro label _
  apply decide_eq_true
  rw [oneHighGraphSourcePairing_endpointCount]
  symm
  exact oneHighFamilyTableGet_graphRelevantMissTable _ _ source label

/-- The concrete pairing row has exactly the profile-prescribed number of
internal matching edges. -/
theorem oneHighGraphSourcePairing_length
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {v : V} (hv : G.degree v = 8)
    (p : OneHighRawV2Presentation G hfree v) (source : Fin 8) :
    (oneHighGraphSourcePairing G hfree hv p source).length =
      oneHighFamilyInternalEdges p.profile source := by
  let s := p.branchLabel.symm source
  let mate := oneHighInternalMate G hfree v s
  let label := fun x => p.branchLabel
    (oneHighMatchedMissLabel G hfree hv p.external_empty p.outer_degree
      p.mate p.mate_adj s x)
  have hcard : Fintype.card (OneHighMatchedBranchVertices G v s) =
      2 * oneHighFamilyInternalEdges p.profile source := by
    calc
      Fintype.card (OneHighMatchedBranchVertices G v s) =
          highBranchMatchedCount G v s :=
        card_oneHighMatchedBranchVertices_eq_highBranchMatchedCount G v s
      _ = 2 * oneHighFamilyInternalEdges p.profile source := by
        simpa [s] using p.matched_count source
  have htwo := two_mul_matchingPairingList_length mate label
    (degreeOneMate_involutive _ _) (degreeOneMate_ne _ _)
  have hsorted := matchingPairingListSorted_length mate label
  change (matchingPairingListSorted mate label).length = _
  omega

theorem oneHighGraphSourcePairing_mem_shapes
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {v : V} (hv : G.degree v = 8)
    (p : OneHighRawV2Presentation G hfree v) (source : Fin 8) :
    oneHighGraphSourcePairing G hfree hv p source ∈
      oneHighSourcePairingShapes p.profile source := by
  let s := p.branchLabel.symm source
  let mate := oneHighInternalMate G hfree v s
  let label := fun x => p.branchLabel
    (oneHighMatchedMissLabel G hfree hv p.external_empty p.outer_degree
      p.mate p.mate_adj s x)
  let pairs := oneHighGraphSourcePairing G hfree hv p source
  have hcard : Fintype.card (OneHighMatchedBranchVertices G v s) =
      2 * oneHighFamilyInternalEdges p.profile source := by
    calc
      Fintype.card (OneHighMatchedBranchVertices G v s) =
          highBranchMatchedCount G v s :=
        card_oneHighMatchedBranchVertices_eq_highBranchMatchedCount G v s
      _ = 2 * oneHighFamilyInternalEdges p.profile source := by
        simpa [s] using p.matched_count source
  have hlen : pairs.length = oneHighFamilyInternalEdges p.profile source := by
    have htwo := two_mul_matchingPairingList_length mate label
      (degreeOneMate_involutive _ _) (degreeOneMate_ne _ _)
    have hsorted := matchingPairingListSorted_length mate label
    change pairs.length = _
    change (matchingPairingListSorted mate label).length = _
    omega
  change pairs ∈ oneHighSourcePairingShapes p.profile source
  by_cases hedge : oneHighFamilyInternalEdges p.profile source = 1
  · have hpairs : pairs.length = 1 := hlen.trans hedge
    obtain ⟨pair, hpairsEq⟩ := List.length_eq_one_iff.mp hpairs
    rw [hpairsEq]
    apply oneHigh_singleton_mem_sourcePairingShapes hedge
    apply mem_matchingPairingListSorted_canonical mate label
    change pair ∈ pairs
    rw [hpairsEq]
    simp
  · have hedgeTwo : oneHighFamilyInternalEdges p.profile source = 2 := by
      unfold oneHighFamilyInternalEdges at hedge ⊢
      split <;> simp_all
    have hpairs : pairs.length = 2 := hlen.trans hedgeTwo
    obtain ⟨first, second, hpairsEq⟩ := List.length_eq_two.mp hpairs
    rw [hpairsEq]
    apply oneHigh_pair_mem_sourcePairingShapes hedge
    · apply mem_matchingPairingListSorted_canonical mate label
      change first ∈ pairs
      rw [hpairsEq]
      simp
    · apply mem_matchingPairingListSorted_canonical mate label
      change second ∈ pairs
      rw [hpairsEq]
      simp
    · have hs := matchingPairingListSorted_pairwise_code mate label
      change pairs.Pairwise (fun a b =>
        oneHighLabelPairCode a ≤ oneHighLabelPairCode b) at hs
      rw [hpairsEq] at hs
      simpa using hs

theorem oneHighGraphSourcePairing_mem_compatible
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {v : V} (hv : G.degree v = 8)
    (p : OneHighRawV2Presentation G hfree v) (source : Fin 8) :
    oneHighGraphSourcePairing G hfree hv p source ∈
      oneHighCompatibleSourcePairings p.profile
        (oneHighGraphRelevantMissTable
          (oneHighRelabeledLeafGraph G v
            (oneHighLeafFinFortyEquiv G hfree v p.branchLabel p.leafLabel))
          p.profile)
        source := by
  rw [oneHigh_mem_compatibleSourcePairings_iff]
  exact ⟨oneHighGraphSourcePairing_mem_shapes G hfree hv p source,
    oneHighGraphSourcePairing_compatible G hfree hv p source⟩

/-- The actual eight-source refinement induced by the graph presentation. -/
def oneHighGraphPairingRefinement
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {v : V} (hv : G.degree v = 8)
    (p : OneHighRawV2Presentation G hfree v) :
    List (List OneHighLabelPair) :=
  List.ofFn fun source : Fin 8 =>
    oneHighGraphSourcePairing G hfree hv p source

theorem oneHighGraphPairingRefinement_mem
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {v : V} (hv : G.degree v = 8)
    (p : OneHighRawV2Presentation G hfree v) :
    oneHighGraphPairingRefinement G hfree hv p ∈
      oneHighPairingRefinements p.profile
        (oneHighGraphRelevantMissTable
          (oneHighRelabeledLeafGraph G v
            (oneHighLeafFinFortyEquiv G hfree v p.branchLabel p.leafLabel))
          p.profile) := by
  apply oneHigh_listOfFn_mem_pairingRefinements
  intro source
  exact oneHighGraphSourcePairing_mem_compatible G hfree hv p source

end

end Erdos85
