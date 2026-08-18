import Proofs.Erdos85OneHighAllEvenSectorTerminal
import Proofs.Erdos85OneHighV2CapacityCover

/-! # Profile-two reciprocal inventory terminal -/

namespace Erdos85

/-- Relevant-coordinate form of the profile-2 reciprocal diagonal cycle.
Unlike the pairing-search predicate, this signature transports immediately
across orbit-table relevant agreement. -/
def oneHighProfileTwoHasReciprocalEntry (table : OneHighMissTable) : Bool :=
  decide (table 0 2 = 2)

/-- The capacity inventory cut out by the transport-stable reciprocal entry. -/
def oneHighProfileTwoReciprocalEntryInventoryTables : List OneHighMissTable :=
  (oneHighCapacityInventoryTables 2).filter
    oneHighProfileTwoHasReciprocalEntry

/-- The transport-stable formulation recovers the same sharp 78-row
profile-2 residual as the explicit compatible-pairing two-cycle predicate. -/
theorem oneHighProfileTwoReciprocalEntryInventoryTables_length :
    oneHighProfileTwoReciprocalEntryInventoryTables.length = 78 := by
  native_decide

theorem oneHighProfileTwoHasReciprocalEntry_of_relevantAgree
    {graphTable stored : OneHighMissTable}
    (hagree : OneHighTableRelevantAgree graphTable stored)
    (hgraph : oneHighProfileTwoHasReciprocalEntry graphTable = true) :
    oneHighProfileTwoHasReciprocalEntry stored = true := by
  have h02 := hagree ((0 : Nat), (2 : Nat)) (by decide)
  simp only [oneHighProfileTwoHasReciprocalEntry, decide_eq_true_eq] at hgraph ⊢
  rw [← h02]
  exact hgraph

theorem profile_two_oneEdge_eq_two
    (u : Fin 8) (hu0 : u ≠ 0) (hu1 : u ≠ 1)
    (hedge : oneHighFamilyInternalEdges 2 u = 1) :
    u = 2 := by
  decide +revert

/-- The one-edge reciprocal-target arm forces the transport-stable `(0,2)=2`
entry on the concrete graph table. -/
theorem OneHighReciprocalSameMissEdges.graphTable_profileTwoHasReciprocalEntry
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {hfree : ¬ containsC4 V G} {v : V} {hv : G.degree v = 8}
    {p : OneHighRawV2Presentation G hfree v}
    (q : OneHighReciprocalSameMissEdges G hfree hv p)
    (hprofile : p.profile = 2)
    (huEdge : oneHighFamilyInternalEdges p.profile (p.branchLabel q.u) = 1) :
    oneHighProfileTwoHasReciprocalEntry
      (oneHighFamilyGraphTable
        (oneHighRelabeledLeafGraph G v
          (oneHighLeafFinFortyEquiv G hfree v p.branchLabel p.leafLabel))
        p.profile) = true := by
  have hus : q.u ≠ q.s :=
    (Finset.mem_erase.mp (Finset.mem_erase.mp q.u_far).2).1
  have hum : q.u ≠ p.mate q.s := (Finset.mem_erase.mp q.u_far).1
  have hu0 : p.branchLabel q.u ≠ 0 := by
    intro hu
    apply hus
    apply p.branchLabel.injective
    rw [hu, q.s_label]
  have hu1 : p.branchLabel q.u ≠ 1 := by
    intro hu
    apply hum
    apply p.branchLabel.injective
    rw [hu, p.branch_mate, q.s_label]
    decide
  have hu2 : p.branchLabel q.u = 2 :=
    profile_two_oneEdge_eq_two _ hu0 hu1 (by simpa [hprofile] using huEdge)
  have hcount := oneHighGraphSourcePairing_endpointCount G hfree hv p
    (p.branchLabel q.s) (p.branchLabel q.u)
  rw [q.source_pairing_eq_singleton (by omega), q.s_label, hu2] at hcount
  have hrelevant : oneHighGraphRelevantMissTable
      (oneHighRelabeledLeafGraph G v
        (oneHighLeafFinFortyEquiv G hfree v p.branchLabel p.leafLabel))
      p.profile 0 2 = 2 := by
    simpa [oneHighPairingEndpointCount, oneHighLabelPairEndpointCount] using
      hcount.symm
  simpa [oneHighProfileTwoHasReciprocalEntry,
    oneHighGraphRelevantMissTable, oneHighFamilyTableGet] using hrelevant

/-- Complete profile-2 reciprocal residual relative to a stored capacity orbit
representative: either that representative lies in the 78-row finite lane,
or the graph supplies the isolated-target packing witness. -/
theorem OneHighReciprocalSameMissEdges.storedTable_mem_profileTwoInventory_or_isolatedTarget
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {hfree : ¬ containsC4 V G} {v : V} {hv : G.degree v = 8}
    {p : OneHighRawV2Presentation G hfree v}
    (q : OneHighReciprocalSameMissEdges G hfree hv p)
    (hprofile : p.profile = 2)
    (stored : OneHighMissTable)
    (hstored : stored ∈ oneHighCapacityInventoryTables 2)
    (hagree : OneHighTableRelevantAgree
      (oneHighFamilyGraphTable
        (oneHighRelabeledLeafGraph G v
          (oneHighLeafFinFortyEquiv G hfree v p.branchLabel p.leafLabel))
        p.profile)
      stored) :
    stored ∈ oneHighProfileTwoReciprocalEntryInventoryTables ∨
      ∃ w : {r : V // r ∈ G.neighborSet v},
        w ≠ q.u ∧
        Nonempty (OneHighReciprocalIsolatedTarget G hfree hv p q w) := by
  rcases q.profileTwo_targetOneEdge_or_isolatedTarget hprofile with
      huEdge | hisolated
  · left
    rw [oneHighProfileTwoReciprocalEntryInventoryTables, List.mem_filter]
    refine ⟨hstored, ?_⟩
    exact oneHighProfileTwoHasReciprocalEntry_of_relevantAgree hagree
      (q.graphTable_profileTwoHasReciprocalEntry hprofile huEdge)
  · exact Or.inr hisolated

/-- Once checked UNSAT evidence covers the exact 78-row inventory, the finite
arm of the stored-orbit dichotomy is impossible; only the isolated-target
packing residual remains.  This is the direct consumer socket for the
targeted certificate campaign. -/
theorem OneHighReciprocalSameMissEdges.exists_isolatedTarget_of_profileTwo_checked
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    {v : Fin 49} {hv : G.degree v = 8}
    {p : OneHighRawV2Presentation G hfree v}
    (q : OneHighReciprocalSameMissEdges G hfree hv p)
    (hprofile : p.profile = 2)
    (stored : OneHighMissTable)
    (hstored : stored ∈ oneHighCapacityInventoryTables 2)
    (hagree : OneHighTableRelevantAgree
      (oneHighFamilyGraphTable
        (oneHighRelabeledLeafGraph G v
          (oneHighLeafFinFortyEquiv G hfree v p.branchLabel p.leafLabel))
        p.profile)
      stored)
    (hchecked : ∀ table ∈ oneHighProfileTwoReciprocalEntryInventoryTables,
      OneHighFamilyV2CheckedUnsat 2 table) :
    ∃ w : {r : Fin 49 // r ∈ G.neighborSet v},
      w ≠ q.u ∧
      Nonempty (OneHighReciprocalIsolatedTarget G hfree hv p q w) := by
  rcases q.storedTable_mem_profileTwoInventory_or_isolatedTarget hprofile
      stored hstored hagree with hmem | hisolated
  · have hcertStored : OneHighFamilyV2CheckedUnsat p.profile stored := by
      simpa [hprofile] using hchecked stored hmem
    have hcertGraph : OneHighFamilyV2CheckedUnsat p.profile
        (oneHighFamilyGraphTable
          (oneHighRelabeledLeafGraph G v
            (oneHighLeafFinFortyEquiv G hfree v p.branchLabel p.leafLabel))
          p.profile) :=
      hcertStored.transport hagree.symm
    exact False.elim (false_of_rawOneHigh_v2Checked
      G hfree hmin (Fintype.card_fin 49) hv p.unique_high p.external_empty
        p.outer_degree p.mate p.mate_involutive p.mate_adj p.branchLabel
        p.branch_mate p.leafLabel p.profile p.constraints hcertGraph)
  · exact hisolated

end Erdos85
