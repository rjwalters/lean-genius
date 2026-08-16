import Proofs.Erdos85OneHighTurnPairingBridge
import Proofs.Erdos85OneHighV2CapacityInventory

/-! # Sound saturated-turn-row subinventory -/

namespace Erdos85

open SimpleGraph

/-- The relevant graph-table normal form agrees with the raw graph table on
every coordinate stored by the v2 inventory. -/
theorem oneHighGraphRelevantMissTable_relevantAgree_graphTable
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj] (profile : Nat) :
    OneHighTableRelevantAgree
      (oneHighGraphRelevantMissTable R profile)
      (oneHighFamilyGraphTable R profile) := by
  intro pair hpair
  have hp := oneHighFamilyTablePairs_mem_bounds hpair
  rcases pair with ⟨c, j⟩
  simp only at hp
  simp [oneHighGraphRelevantMissTable, hp.1, hp.2.1,
    ne_of_lt hp.2.2.1, hp.2.2.2, oneHighFamilyTableGet,
    min_eq_left hp.2.2.1.le, max_eq_right hp.2.2.1.le]

/-- Capacity-admissible representatives compatible with the exact
same-owner saturated-turn signature. -/
def oneHighSaturatedTurnRowInventoryTables (profile : Fin 5) :
    List OneHighMissTable :=
  (oneHighCapacityInventoryTables profile).filter
    (oneHighTableHasSaturatedTurnRow profile.val)

/-- A same-owner turn in a graph presentation lands in the saturated-turn
subinventory whenever its raw graph table agrees with a capacity
representative. -/
theorem OneHighPinnedThreePairTurn.mem_saturatedTurnRowInventory
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {v : V} (hv : G.degree v = 8)
    (p : OneHighRawV2Presentation G hfree v)
    (T : OneHighPinnedThreePairTurn G hfree hv p)
    (howner : T.qAB.sourceEdge.1 = T.qBC.sourceEdge.1)
    (table : OneHighMissTable)
    (hmem : table ∈ oneHighCapacityInventoryTables
      ⟨p.profile, Nat.lt_succ_iff.mpr p.profile_le⟩)
    (hagree : OneHighTableRelevantAgree
      (oneHighFamilyGraphTable
        (oneHighRelabeledLeafGraph G v
          (oneHighLeafFinFortyEquiv G hfree v p.branchLabel p.leafLabel))
        p.profile) table) :
    table ∈ oneHighSaturatedTurnRowInventoryTables
      ⟨p.profile, Nat.lt_succ_iff.mpr p.profile_le⟩ := by
  rw [oneHighSaturatedTurnRowInventoryTables, List.mem_filter]
  refine ⟨hmem, ?_⟩
  apply oneHighTableHasSaturatedTurnRow_of_relevantAgree
    ((oneHighGraphRelevantMissTable_relevantAgree_graphTable
      (oneHighRelabeledLeafGraph G v
        (oneHighLeafFinFortyEquiv G hfree v p.branchLabel p.leafLabel))
      p.profile).trans hagree)
  exact T.graphRelevantMissTable_hasSaturatedTurnRow G hfree hv p howner

end Erdos85
