import Proofs.Erdos85OneHighTurnParityReflection

/-! # Graph-to-inventory bridge for the saturated odd turn -/

namespace Erdos85

open SimpleGraph

noncomputable section

/-- Relevant agreement becomes literal equality after zero-normalization. -/
theorem oneHighTableRestrict_eq_of_relevantAgree
    {left right : OneHighMissTable}
    (h : OneHighTableRelevantAgree left right) :
    oneHighTableRestrict left = oneHighTableRestrict right := by
  funext c j
  unfold oneHighTableRestrict
  split
  · next hp => exact h (c, j) hp
  · rfl

/-- The normalized raw graph table has exactly the same `Fin 8` row reads as
the graph-relevant table used to construct the concrete pairing. -/
theorem oneHighFamilyTableGet_restrict_graphTable_eq_graphRelevant
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (profile : Nat) (source label : Fin 8) :
    oneHighFamilyTableGet
        (oneHighTableRestrict (oneHighFamilyGraphTable R profile))
        source.val label.val =
      oneHighFamilyTableGet (oneHighGraphRelevantMissTable R profile)
        source.val label.val := by
  fin_cases source <;> fin_cases label <;>
    simp [oneHighFamilyTableGet, oneHighTableRestrict,
      oneHighGraphRelevantMissTable, oneHighFamilyTablePairs]

/-- Exact source-pairing compatibility depends only on the eight normalized
row reads. -/
theorem oneHighSourcePairingCompatible_congr
    {left right : OneHighMissTable} {source : Fin 8}
    (h : ∀ label : Fin 8,
      oneHighFamilyTableGet left source.val label.val =
        oneHighFamilyTableGet right source.val label.val)
    (pairs : List OneHighLabelPair) :
    oneHighSourcePairingCompatible left source pairs =
      oneHighSourcePairingCompatible right source pairs := by
  unfold oneHighSourcePairingCompatible
  apply congrArg (fun predicate : Fin 8 → Bool =>
    (List.ofFn fun label : Fin 8 => label).all predicate)
  funext label
  rw [h label]

/-- The graph-induced refinement is compatible with the normalized raw graph
table, the form that transports literally across inventory agreement. -/
theorem oneHighGraphPairingRefinement_mem_restrict_graphTable
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {v : V} (hv : G.degree v = 8)
    (p : OneHighRawV2Presentation G hfree v) :
    oneHighGraphPairingRefinement G hfree hv p ∈
      oneHighPairingRefinements p.profile
        (oneHighTableRestrict
          (oneHighFamilyGraphTable
            (oneHighRelabeledLeafGraph G v
              (oneHighLeafFinFortyEquiv G hfree v
                p.branchLabel p.leafLabel)) p.profile)) := by
  apply oneHigh_listOfFn_mem_pairingRefinements
  intro source
  rw [oneHigh_mem_compatibleSourcePairings_iff]
  refine ⟨oneHighGraphSourcePairing_mem_shapes G hfree hv p source, ?_⟩
  have hcompat := oneHighGraphSourcePairing_compatible
    G hfree hv p source
  rw [oneHighSourcePairingCompatible_congr
    (fun label => oneHighFamilyTableGet_restrict_graphTable_eq_graphRelevant
      (oneHighRelabeledLeafGraph G v
        (oneHighLeafFinFortyEquiv G hfree v
          p.branchLabel p.leafLabel)) p.profile source label)]
  exact hcompat

/-- Complete graph-to-finite-inventory socket for the same-owner turn.  A
capacity representative agreeing with the raw graph table lies in the exact
9,707-row odd-turn inventory. -/
theorem OneHighPinnedThreePairTurn.mem_saturatedOddTurnParityInventory
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {v : V} (hv : G.degree v = 8)
    (p : OneHighRawV2Presentation G hfree v)
    (T : OneHighPinnedThreePairTurn G hfree hv p)
    (howner : T.qAB.sourceEdge.1 = T.qBC.sourceEdge.1)
    (table : OneHighMissTable)
    (hcapacity : table ∈ oneHighCapacityInventoryTables
      ⟨p.profile, Nat.lt_succ_iff.mpr p.profile_le⟩)
    (hagree : OneHighTableRelevantAgree
      (oneHighFamilyGraphTable
        (oneHighRelabeledLeafGraph G v
          (oneHighLeafFinFortyEquiv G hfree v
            p.branchLabel p.leafLabel)) p.profile) table) :
    table ∈ oneHighSaturatedOddTurnParityInventoryTables
      ⟨p.profile, Nat.lt_succ_iff.mpr p.profile_le⟩ := by
  have hrefinement :=
    oneHighGraphPairingRefinement_mem_restrict_graphTable G hfree hv p
  have hrestrict := oneHighTableRestrict_eq_of_relevantAgree hagree
  rw [hrestrict] at hrefinement
  exact mem_oneHighSaturatedOddTurnParityInventoryTables_of_refinement
    hcapacity hrefinement
      (T.graphPairingRefinement_hasSaturatedOddTurn G hfree hv p howner)

end

end Erdos85
