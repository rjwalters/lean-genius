import Proofs.Erdos85OneHighTurnResidualInventory
import Proofs.Erdos85OneHighTurnGraphInventoryBridge

/-! # Soundness of the ordered same-owner turn residual -/

namespace Erdos85

open SimpleGraph

/-- A concrete compatible same-owner turn which has neither an odd mate key
nor an alternating odd cross block is accepted by the compact residual
evaluator. -/
theorem oneHighTableHasSaturatedOddTurnResidualByParity_of_refinement
    {profile : Nat} {table : OneHighMissTable}
    {refinement : List (List OneHighLabelPair)}
    (hrefinement : refinement ∈
      oneHighPairingRefinements profile (oneHighTableRestrict table))
    (hturn : oneHighRefinementHasSaturatedOddThreePairTurn refinement = true)
    (hnoMate : oneHighRefinementHasOddMateKey refinement = false)
    (hnoCross : oneHighRefinementHasOddCrossBlock refinement = false) :
    oneHighTableHasSaturatedOddTurnResidualByParity profile table = true := by
  rw [oneHighRefinementHasSaturatedOddThreePairTurn,
    decide_eq_true_eq] at hturn
  rcases hturn with ⟨source, a, b, c, row, hget, hperm,
    hsa, hsb, hsc, hab, hbc, hac, hoddAB, hoddBC⟩
  let choices := List.ofFn fun current : Fin 8 =>
    oneHighCompatibleSourcePairings profile (oneHighTableRestrict table) current
  have hcompatible : OneHighChoicesCompatible choices refinement := by
    exact (oneHighPairingRefinements_mem_iff profile
      (oneHighTableRestrict table) refinement).1 hrefinement
  have hrowMemRaw : row ∈ choices[source.val]! :=
    mem_getElem!_of_oneHighChoicesCompatible_getElem?_eq_some
      hcompatible hget
  have habRow : oneHighCanonicalLabelPair a b ∈ row := by
    rw [hperm.mem_iff]
    simp
  have hbcRow : oneHighCanonicalLabelPair b c ∈ row := by
    rw [hperm.mem_iff]
    simp
  let labels := (row.flatMap fun pair => [pair.1, pair.2]).eraseDups
  have haLabels : a ∈ labels := by
    simp only [labels, List.mem_eraseDups, List.mem_flatMap]
    exact ⟨oneHighCanonicalLabelPair a b, habRow,
      left_mem_canonicalPair_endpoints a b⟩
  have hbLabels : b ∈ labels := by
    simp only [labels, List.mem_eraseDups, List.mem_flatMap]
    exact ⟨oneHighCanonicalLabelPair a b, habRow,
      right_mem_canonicalPair_endpoints a b⟩
  have hcLabels : c ∈ labels := by
    simp only [labels, List.mem_eraseDups, List.mem_flatMap]
    exact ⟨oneHighCanonicalLabelPair b c, hbcRow,
      right_mem_canonicalPair_endpoints b c⟩
  have htriple : (a, b, c) ∈ oneHighSaturatedTurnRowTriples source row := by
    simp only [oneHighSaturatedTurnRowTriples, List.mem_flatMap,
      List.mem_filterMap]
    exact ⟨a, haLabels, b, hbLabels, c, hcLabels,
      by simp [hperm, hsa, hsb, hsc, hab, hbc, hac]⟩
  have hfixed : OneHighChoicesCompatible
      (choices.set source.val [row]) refinement :=
    oneHighChoicesCompatible_set_singleton_of_getElem?_eq_some
      hcompatible hget
  have hmaskMem : oneHighPairingRefinementParityMask refinement ∈
      oneHighPairingParityStatesWithSourceRowChoices choices source row := by
    rw [oneHighPairingParityStatesWithSourceRowChoices,
      mem_oneHighChooseEachParityStates_iff]
    exact ⟨refinement,
      (oneHighChooseEach_mem_iff _ _).2 hfixed, rfl⟩
  have hmaskAB : oneHighParityMaskOdd
      (oneHighPairingRefinementParityMask refinement) a b = true := by
    rw [oneHighParityMaskOdd_refinement]
    simp [oneHighMultiplicityOdd, Nat.odd_iff.mp hoddAB]
  have hmaskBC : oneHighParityMaskOdd
      (oneHighPairingRefinementParityMask refinement) b c = true := by
    rw [oneHighParityMaskOdd_refinement]
    simp [oneHighMultiplicityOdd, Nat.odd_iff.mp hoddBC]
  have hmaskNoMate : oneHighParityMaskHasOddMateKey
      (oneHighPairingRefinementParityMask refinement) = false := by
    rwa [oneHighParityMaskHasOddMateKey_refinement]
  have hmaskNoCross : oneHighParityMaskHasOddCrossBlock
      (oneHighPairingRefinementParityMask refinement) = false := by
    rwa [oneHighParityMaskHasOddCrossBlock_refinement]
  have htriplesNe : oneHighSaturatedTurnRowTriples source row ≠ [] :=
    List.ne_nil_of_mem htriple
  have hrowFilteredRaw : row ∈ choices[source.val]!.filter fun candidate =>
      !(oneHighSaturatedTurnRowTriples source candidate).isEmpty := by
    rw [List.mem_filter]
    exact ⟨hrowMemRaw, by simpa using htriplesNe⟩
  rw [oneHighTableHasSaturatedOddTurnResidualByParity]
  change (List.ofFn fun source : Fin 8 => source).any (fun source =>
    let rows := choices[source.val]!.filter fun candidate =>
      !(oneHighSaturatedTurnRowTriples source candidate).isEmpty
    !rows.isEmpty && rows.any fun row =>
      let triples := oneHighSaturatedTurnRowTriples source row
      (oneHighPairingParityStatesWithSourceRowChoices
        choices source row).any fun mask =>
        !oneHighParityMaskHasOddMateKey mask &&
          !oneHighParityMaskHasOddCrossBlock mask &&
          triples.any fun triple =>
            oneHighParityMaskOdd mask triple.1 triple.2.1 &&
              oneHighParityMaskOdd mask triple.2.1 triple.2.2) = true
  rw [List.any_eq_true]
  refine ⟨source, ?_, ?_⟩
  · fin_cases source <;> simp
  rw [Bool.and_eq_true]
  constructor
  · cases hrows : choices[source.val]!.filter fun candidate =>
        !(oneHighSaturatedTurnRowTriples source candidate).isEmpty with
    | nil =>
        rw [hrows] at hrowFilteredRaw
        simp at hrowFilteredRaw
    | cons head tail => simp
  · rw [List.any_eq_true]
    refine ⟨row, hrowFilteredRaw, ?_⟩
    rw [List.any_eq_true]
    refine ⟨oneHighPairingRefinementParityMask refinement, hmaskMem, ?_⟩
    simp [hmaskNoMate, hmaskNoCross]
    exact ⟨a, b, c, htriple,
      by simpa using hmaskAB, by simpa using hmaskBC⟩

/-- Capacity packaging for the ordered 7,433-row residual. -/
theorem mem_oneHighSaturatedOddTurnResidualInventoryTables_of_refinement
    {profile : Fin 5} {table : OneHighMissTable}
    (hcapacity : table ∈ oneHighCapacityInventoryTables profile)
    {refinement : List (List OneHighLabelPair)}
    (hrefinement : refinement ∈
      oneHighPairingRefinements profile.val (oneHighTableRestrict table))
    (hturn : oneHighRefinementHasSaturatedOddThreePairTurn refinement = true)
    (hnoMate : oneHighRefinementHasOddMateKey refinement = false)
    (hnoCross : oneHighRefinementHasOddCrossBlock refinement = false) :
    table ∈ oneHighSaturatedOddTurnResidualInventoryTables profile := by
  rw [oneHighSaturatedOddTurnResidualInventoryTables, List.mem_filter]
  exact ⟨hcapacity,
    oneHighTableHasSaturatedOddTurnResidualByParity_of_refinement
      hrefinement hturn hnoMate hnoCross⟩

/-- Graph-level ordered-residual socket. -/
theorem OneHighPinnedThreePairTurn.mem_saturatedOddTurnResidualInventory
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {v : V} (hv : G.degree v = 8)
    (p : OneHighRawV2Presentation G hfree v)
    (T : OneHighPinnedThreePairTurn G hfree hv p)
    (howner : T.qAB.sourceEdge.1 = T.qBC.sourceEdge.1)
    (hnoMate : oneHighRefinementHasOddMateKey
      (oneHighGraphPairingRefinement G hfree hv p) = false)
    (hnoCross : oneHighRefinementHasOddCrossBlock
      (oneHighGraphPairingRefinement G hfree hv p) = false)
    (table : OneHighMissTable)
    (hcapacity : table ∈ oneHighCapacityInventoryTables
      ⟨p.profile, Nat.lt_succ_iff.mpr p.profile_le⟩)
    (hagree : OneHighTableRelevantAgree
      (oneHighFamilyGraphTable
        (oneHighRelabeledLeafGraph G v
          (oneHighLeafFinFortyEquiv G hfree v
            p.branchLabel p.leafLabel)) p.profile) table) :
    table ∈ oneHighSaturatedOddTurnResidualInventoryTables
      ⟨p.profile, Nat.lt_succ_iff.mpr p.profile_le⟩ := by
  have hrefinement :=
    oneHighGraphPairingRefinement_mem_restrict_graphTable G hfree hv p
  rw [oneHighTableRestrict_eq_of_relevantAgree hagree] at hrefinement
  exact mem_oneHighSaturatedOddTurnResidualInventoryTables_of_refinement
    hcapacity hrefinement
      (T.graphPairingRefinement_hasSaturatedOddTurn G hfree hv p howner)
      hnoMate hnoCross

end Erdos85
