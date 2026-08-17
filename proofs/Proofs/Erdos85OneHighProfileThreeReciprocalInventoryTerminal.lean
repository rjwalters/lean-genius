import Proofs.Erdos85OneHighProfileTwoReciprocalInventoryTerminal

/-! # Profile-three reciprocal inventory terminal -/

namespace Erdos85

/-- Transport-stable form of the profile-three reciprocal-cycle arm. -/
def oneHighProfileThreeHasReciprocalEntry (table : OneHighMissTable) : Bool :=
  decide (table 0 2 = 2) || decide (table 0 4 = 2)

def oneHighProfileThreeReciprocalEntryInventoryTables :
    List OneHighMissTable :=
  (oneHighCapacityInventoryTables 3).filter
    oneHighProfileThreeHasReciprocalEntry

/-- Only nine orbit representatives survive the exact profile-three
reciprocal-cycle signature. -/
theorem oneHighProfileThreeReciprocalEntryInventoryTables_length :
    oneHighProfileThreeReciprocalEntryInventoryTables.length = 9 := by
  native_decide

theorem oneHighProfileThreeHasReciprocalEntry_of_relevantAgree
    {graphTable stored : OneHighMissTable}
    (hagree : OneHighTableRelevantAgree graphTable stored)
    (hgraph : oneHighProfileThreeHasReciprocalEntry graphTable = true) :
    oneHighProfileThreeHasReciprocalEntry stored = true := by
  have h02 := hagree ((0 : Nat), (2 : Nat)) (by decide)
  have h04 := hagree ((0 : Nat), (4 : Nat)) (by decide)
  simp only [oneHighProfileThreeHasReciprocalEntry, Bool.or_eq_true,
    decide_eq_true_eq] at hgraph ⊢
  rcases hgraph with hgraph | hgraph
  · exact Or.inl (h02 ▸ hgraph)
  · exact Or.inr (h04 ▸ hgraph)

theorem profile_three_oneEdge_eq_two_or_four
    (u : Fin 8) (hu0 : u ≠ 0) (hu1 : u ≠ 1)
    (hedge : oneHighFamilyInternalEdges 3 u = 1) :
    u = 2 ∨ u = 4 := by
  decide +revert

/-- If the reciprocal target is not a one-edge branch in profile three,
both remaining one-edge labels `2` and `4` are available and distinct. -/
theorem profile_three_targetOneEdge_or_two_other_oneEdge
    (u : Fin 8) (hu0 : u ≠ 0) (hu1 : u ≠ 1) :
    oneHighFamilyInternalEdges 3 u = 1 ∨
      ∃ w₁ w₂ : Fin 8,
        w₁ ≠ w₂ ∧ w₁ ≠ 0 ∧ w₁ ≠ 1 ∧ w₁ ≠ u ∧
        w₂ ≠ 0 ∧ w₂ ≠ 1 ∧ w₂ ≠ u ∧
        oneHighFamilyInternalEdges 3 w₁ = 1 ∧
        oneHighFamilyInternalEdges 3 w₂ = 1 := by
  decide +revert

/-- The one-edge reciprocal-target arm forces one of the two stable
profile-three source-row entries on the concrete graph table. -/
theorem OneHighReciprocalSameMissEdges.graphTable_profileThreeHasReciprocalEntry
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {hfree : ¬ containsC4 V G} {v : V} {hv : G.degree v = 8}
    {p : OneHighRawV2Presentation G hfree v}
    (q : OneHighReciprocalSameMissEdges G hfree hv p)
    (hprofile : p.profile = 3)
    (huEdge : oneHighFamilyInternalEdges p.profile (p.branchLabel q.u) = 1) :
    oneHighProfileThreeHasReciprocalEntry
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
  have hu24 : p.branchLabel q.u = 2 ∨ p.branchLabel q.u = 4 :=
    profile_three_oneEdge_eq_two_or_four _ hu0 hu1
      (by simpa [hprofile] using huEdge)
  have hcount := oneHighGraphSourcePairing_endpointCount G hfree hv p
    (p.branchLabel q.s) (p.branchLabel q.u)
  rw [q.source_pairing_eq_singleton (by omega), q.s_label] at hcount
  rcases hu24 with hu2 | hu4
  · rw [hu2] at hcount
    have hrelevant : oneHighGraphRelevantMissTable
        (oneHighRelabeledLeafGraph G v
          (oneHighLeafFinFortyEquiv G hfree v p.branchLabel p.leafLabel))
        p.profile 0 2 = 2 := by
      simpa [oneHighPairingEndpointCount,
        oneHighLabelPairEndpointCount] using hcount.symm
    rw [oneHighProfileThreeHasReciprocalEntry, Bool.or_eq_true]
    left
    simpa [oneHighGraphRelevantMissTable, oneHighFamilyTableGet] using hrelevant
  · rw [hu4] at hcount
    have hrelevant : oneHighGraphRelevantMissTable
        (oneHighRelabeledLeafGraph G v
          (oneHighLeafFinFortyEquiv G hfree v p.branchLabel p.leafLabel))
        p.profile 0 4 = 2 := by
      simpa [oneHighPairingEndpointCount,
        oneHighLabelPairEndpointCount] using hcount.symm
    rw [oneHighProfileThreeHasReciprocalEntry, Bool.or_eq_true]
    right
    simpa [oneHighGraphRelevantMissTable, oneHighFamilyTableGet] using hrelevant

/-- Profile three has a sharp dichotomy: the reciprocal branch supplies the
nine-row finite cycle lane, or two distinct one-edge branches supply isolated
packing witnesses. -/
theorem OneHighReciprocalSameMissEdges.profileThree_targetOneEdge_or_two_isolatedTargets
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {hfree : ¬ containsC4 V G} {v : V} {hv : G.degree v = 8}
    {p : OneHighRawV2Presentation G hfree v}
    (q : OneHighReciprocalSameMissEdges G hfree hv p)
    (hprofile : p.profile = 3) :
    oneHighFamilyInternalEdges p.profile (p.branchLabel q.u) = 1 ∨
      ∃ w₁ w₂ : {r : V // r ∈ G.neighborSet v},
        w₁ ≠ w₂ ∧ w₁ ≠ q.u ∧ w₂ ≠ q.u ∧
        Nonempty (OneHighReciprocalIsolatedTarget G hfree hv p q w₁) ∧
        Nonempty (OneHighReciprocalIsolatedTarget G hfree hv p q w₂) := by
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
  rcases profile_three_targetOneEdge_or_two_other_oneEdge
      (p.branchLabel q.u) hu0 hu1 with huEdge | hother
  · exact Or.inl (by simpa [hprofile] using huEdge)
  · right
    rcases hother with ⟨i₁, i₂, hiNe, hi10, hi11, hi1u,
      hi20, hi21, hi2u, hi1Edge, hi2Edge⟩
    let w₁ := p.branchLabel.symm i₁
    let w₂ := p.branchLabel.symm i₂
    have farMem (i : Fin 8) (hi0 : i ≠ 0) (hi1 : i ≠ 1) :
        p.branchLabel.symm i ∈
          ((Finset.univ.erase q.s).erase (p.mate q.s)) := by
      apply Finset.mem_erase.mpr
      constructor
      · intro heq
        apply hi1
        have hlabel := congrArg p.branchLabel heq
        have hmate01 : oneHighStandardMate (0 : Fin 8) = 1 := by decide
        simpa [p.branch_mate, q.s_label, hmate01] using hlabel
      · apply Finset.mem_erase.mpr
        refine ⟨?_, Finset.mem_univ _⟩
        intro heq
        apply hi0
        simpa [q.s_label] using congrArg p.branchLabel heq
    have hw₁u : w₁ ≠ q.u := by
      intro heq
      apply hi1u
      simpa [w₁] using congrArg p.branchLabel heq
    have hw₂u : w₂ ≠ q.u := by
      intro heq
      apply hi2u
      simpa [w₂] using congrArg p.branchLabel heq
    have hw₁Edge : oneHighFamilyInternalEdges p.profile
        (p.branchLabel w₁) = 1 := by
      simpa [hprofile, w₁] using hi1Edge
    have hw₂Edge : oneHighFamilyInternalEdges p.profile
        (p.branchLabel w₂) = 1 := by
      simpa [hprofile, w₂] using hi2Edge
    refine ⟨w₁, w₂, ?_, hw₁u, hw₂u,
      q.nonempty_isolatedTarget (by omega) (farMem i₁ hi10 hi11) hw₁u hw₁Edge,
      q.nonempty_isolatedTarget (by omega) (farMem i₂ hi20 hi21) hw₂u hw₂Edge⟩
    intro heq
    apply hiNe
    simpa [w₁, w₂] using congrArg p.branchLabel heq

/-- Stored-orbit form of the complete profile-three dichotomy. -/
theorem OneHighReciprocalSameMissEdges.storedTable_mem_profileThreeInventory_or_two_isolatedTargets
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {hfree : ¬ containsC4 V G} {v : V} {hv : G.degree v = 8}
    {p : OneHighRawV2Presentation G hfree v}
    (q : OneHighReciprocalSameMissEdges G hfree hv p)
    (hprofile : p.profile = 3)
    (stored : OneHighMissTable)
    (hstored : stored ∈ oneHighCapacityInventoryTables 3)
    (hagree : OneHighTableRelevantAgree
      (oneHighFamilyGraphTable
        (oneHighRelabeledLeafGraph G v
          (oneHighLeafFinFortyEquiv G hfree v p.branchLabel p.leafLabel))
        p.profile) stored) :
    stored ∈ oneHighProfileThreeReciprocalEntryInventoryTables ∨
      ∃ w₁ w₂ : {r : V // r ∈ G.neighborSet v},
        w₁ ≠ w₂ ∧ w₁ ≠ q.u ∧ w₂ ≠ q.u ∧
        Nonempty (OneHighReciprocalIsolatedTarget G hfree hv p q w₁) ∧
        Nonempty (OneHighReciprocalIsolatedTarget G hfree hv p q w₂) := by
  rcases q.profileThree_targetOneEdge_or_two_isolatedTargets hprofile with
      huEdge | hisolated
  · left
    rw [oneHighProfileThreeReciprocalEntryInventoryTables, List.mem_filter]
    exact ⟨hstored, oneHighProfileThreeHasReciprocalEntry_of_relevantAgree
      hagree (q.graphTable_profileThreeHasReciprocalEntry hprofile huEdge)⟩
  · exact Or.inr hisolated

/-- Checked UNSAT coverage of the nine finite rows eliminates the cycle arm,
leaving two distinct isolated-target packing witnesses. -/
theorem OneHighReciprocalSameMissEdges.exists_two_isolatedTargets_of_profileThree_checked
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    {v : Fin 49} {hv : G.degree v = 8}
    {p : OneHighRawV2Presentation G hfree v}
    (q : OneHighReciprocalSameMissEdges G hfree hv p)
    (hprofile : p.profile = 3)
    (stored : OneHighMissTable)
    (hstored : stored ∈ oneHighCapacityInventoryTables 3)
    (hagree : OneHighTableRelevantAgree
      (oneHighFamilyGraphTable
        (oneHighRelabeledLeafGraph G v
          (oneHighLeafFinFortyEquiv G hfree v p.branchLabel p.leafLabel))
        p.profile) stored)
    (hchecked : ∀ table ∈ oneHighProfileThreeReciprocalEntryInventoryTables,
      OneHighFamilyV2CheckedUnsat 3 table) :
    ∃ w₁ w₂ : {r : Fin 49 // r ∈ G.neighborSet v},
      w₁ ≠ w₂ ∧ w₁ ≠ q.u ∧ w₂ ≠ q.u ∧
      Nonempty (OneHighReciprocalIsolatedTarget G hfree hv p q w₁) ∧
      Nonempty (OneHighReciprocalIsolatedTarget G hfree hv p q w₂) := by
  rcases q.storedTable_mem_profileThreeInventory_or_two_isolatedTargets
      hprofile stored hstored hagree with hmem | hisolated
  · have hcertStored : OneHighFamilyV2CheckedUnsat p.profile stored := by
      simpa [hprofile] using hchecked stored hmem
    have hcertGraph : OneHighFamilyV2CheckedUnsat p.profile
        (oneHighFamilyGraphTable
          (oneHighRelabeledLeafGraph G v
            (oneHighLeafFinFortyEquiv G hfree v p.branchLabel p.leafLabel))
          p.profile) := hcertStored.transport hagree.symm
    exact False.elim (false_of_rawOneHigh_v2Checked
      G hfree hmin (Fintype.card_fin 49) hv p.unique_high p.external_empty
        p.outer_degree p.mate p.mate_involutive p.mate_adj p.branchLabel
        p.branch_mate p.leafLabel p.profile p.constraints hcertGraph)
  · exact hisolated

end Erdos85
