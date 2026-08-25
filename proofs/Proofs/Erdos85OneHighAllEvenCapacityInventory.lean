import Proofs.Erdos85OneHighProfileOneAllEvenInventoryTerminal

/-! # Capacity inventory for the complete one-high all-even sector

Unlike the reciprocal-singleton inventory, this filter assumes only that the
actual graph pairing has even multiplicity on every off-diagonal miss key.
It therefore gives an honest finite target for the complete all-even branch.
-/

namespace Erdos85

noncomputable section

/-- Transport-stable all-even pairing predicate.  Restricting the table first
ensures that it depends only on the 24 coordinates retained by the orbit
inventory. -/
def oneHighTableHasAllEvenPairingRestricted
    (profile : Nat) (table : OneHighMissTable) : Bool :=
  oneHighTableHasAllEvenPairing profile
    (oneHighPairingTableRestrict table)

/-- Capacity-compatible orbit rows admitting an all-even pairing refinement. -/
def oneHighAllEvenCapacityInventoryTables (profile : Fin 5) :
    List OneHighMissTable :=
  (oneHighCapacityInventoryTables profile).filter
    (oneHighTableHasAllEvenPairingRestricted profile.val)

/-- Exact per-profile census, in profiles `0,1,2,3,4`. -/
theorem oneHighAllEvenCapacityInventoryTables_lengths :
    (List.finRange 5).map (fun profile =>
      (oneHighAllEvenCapacityInventoryTables profile).length) =
        [609, 16, 1587, 6, 285] := by
  native_decide

/-- The direct all-even filter reduces the 13,351-row capacity inventory to
2,503 rows without a same-miss or reciprocal-singleton assumption. -/
theorem oneHighAllEvenCapacityInventoryTables_total_length :
    ((List.finRange 5).map fun profile =>
      (oneHighAllEvenCapacityInventoryTables profile).length).sum = 2503 := by
  rw [oneHighAllEvenCapacityInventoryTables_lengths]
  decide

theorem oneHighTableHasAllEvenPairingRestricted_of_relevantAgree
    {profile : Nat} {left right : OneHighMissTable}
    (hagree : OneHighTableRelevantAgree left right)
    (hleft : oneHighTableHasAllEvenPairingRestricted profile left = true) :
    oneHighTableHasAllEvenPairingRestricted profile right = true := by
  unfold oneHighTableHasAllEvenPairingRestricted at hleft ⊢
  rw [← oneHighPairingTableRestrict_eq_of_relevantAgree hagree]
  exact hleft

/-- An all-even graph pairing makes its relevant graph table pass the
transport-stable executable filter. -/
theorem oneHighGraphTable_hasAllEvenPairingRestricted
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {v : V} (hv : G.degree v = 8)
    (p : OneHighRawV2Presentation G hfree v)
    (heven : ∀ key ∈ exchangedMissPairKeys (Fin 8),
      Even (exchangedMissPairMultiplicity
        (oneHighGlobalInternalMate G hfree v)
        (fun x => p.branchLabel
          (oneHighGlobalMissLabel G hfree hv p.external_empty p.outer_degree
            p.mate p.mate_adj x)) key)) :
    oneHighTableHasAllEvenPairingRestricted p.profile
      (oneHighGraphRelevantMissTable
        (oneHighRelabeledLeafGraph G v
          (oneHighLeafFinFortyEquiv G hfree v p.branchLabel p.leafLabel))
        p.profile) = true := by
  unfold oneHighTableHasAllEvenPairingRestricted
  rw [oneHighTableRestrict_graphRelevantMissTable]
  exact oneHighTableHasAllEvenPairing_of_refinement
    (oneHighGraphPairingRefinement_mem G hfree hv p)
    (oneHighGraphPairingRefinement_allOffDiagonalEven G hfree hv p heven)

/-- Any stored capacity representative agreeing with an all-even graph table
belongs to the exact 2,503-row all-even inventory. -/
theorem oneHigh_storedTable_mem_allEvenCapacityInventory
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {v : V} (hv : G.degree v = 8)
    (p : OneHighRawV2Presentation G hfree v)
    (heven : ∀ key ∈ exchangedMissPairKeys (Fin 8),
      Even (exchangedMissPairMultiplicity
        (oneHighGlobalInternalMate G hfree v)
        (fun x => p.branchLabel
          (oneHighGlobalMissLabel G hfree hv p.external_empty p.outer_degree
            p.mate p.mate_adj x)) key))
    (stored : OneHighMissTable)
    (hstored : stored ∈ oneHighCapacityInventoryTables
      ⟨p.profile, Nat.lt_succ_iff.mpr p.profile_le⟩)
    (hagree : OneHighTableRelevantAgree
      (oneHighFamilyGraphTable
        (oneHighRelabeledLeafGraph G v
          (oneHighLeafFinFortyEquiv G hfree v p.branchLabel p.leafLabel))
        p.profile) stored) :
    stored ∈ oneHighAllEvenCapacityInventoryTables
      ⟨p.profile, Nat.lt_succ_iff.mpr p.profile_le⟩ := by
  rw [oneHighAllEvenCapacityInventoryTables, List.mem_filter]
  refine ⟨hstored, ?_⟩
  apply oneHighTableHasAllEvenPairingRestricted_of_relevantAgree
    (oneHighGraphRelevantMissTable_relevantAgree_of_graphTable _ _ hagree)
  exact oneHighGraphTable_hasAllEvenPairingRestricted G hfree hv p heven

end

end Erdos85
