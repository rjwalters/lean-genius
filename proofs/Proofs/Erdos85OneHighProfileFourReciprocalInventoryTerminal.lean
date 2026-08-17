import Proofs.Erdos85OneHighProfileThreeReciprocalInventoryTerminal

/-! # Profile-four reciprocal inventory terminal -/

namespace Erdos85

/-- Transport-stable form of the profile-four reciprocal-cycle arm. -/
def oneHighProfileFourHasReciprocalEntry (table : OneHighMissTable) : Bool :=
  decide (table 0 2 = 2) || decide (table 0 4 = 2) ||
    decide (table 0 6 = 2)

def oneHighProfileFourReciprocalEntryInventoryTables :
    List OneHighMissTable :=
  (oneHighCapacityInventoryTables 4).filter
    oneHighProfileFourHasReciprocalEntry

theorem oneHighProfileFourReciprocalEntryInventoryTables_length :
    oneHighProfileFourReciprocalEntryInventoryTables.length = 46 := by
  native_decide

theorem oneHighProfileFourHasReciprocalEntry_of_relevantAgree
    {graphTable stored : OneHighMissTable}
    (hagree : OneHighTableRelevantAgree graphTable stored)
    (hgraph : oneHighProfileFourHasReciprocalEntry graphTable = true) :
    oneHighProfileFourHasReciprocalEntry stored = true := by
  have h02 := hagree ((0 : Nat), (2 : Nat)) (by decide)
  have h04 := hagree ((0 : Nat), (4 : Nat)) (by decide)
  have h06 := hagree ((0 : Nat), (6 : Nat)) (by decide)
  simp only [oneHighProfileFourHasReciprocalEntry, Bool.or_eq_true,
    decide_eq_true_eq] at hgraph ⊢
  rcases hgraph with (hgraph | hgraph) | hgraph
  · exact Or.inl (Or.inl (by rw [← h02]; exact hgraph))
  · exact Or.inl (Or.inr (by rw [← h04]; exact hgraph))
  · exact Or.inr (by rw [← h06]; exact hgraph)

theorem profile_four_oneEdge_eq_two_or_four_or_six
    (u : Fin 8) (hu0 : u ≠ 0) (hu1 : u ≠ 1)
    (hedge : oneHighFamilyInternalEdges 4 u = 1) :
    u = 2 ∨ u = 4 ∨ u = 6 := by
  decide +revert

/-- If the reciprocal target is not one-edge in profile four, all three
other low-even labels are available one-edge branches. -/
theorem profile_four_targetOneEdge_or_three_other_oneEdge
    (u : Fin 8) (hu0 : u ≠ 0) (hu1 : u ≠ 1) :
    oneHighFamilyInternalEdges 4 u = 1 ∨
      ∃ w₁ w₂ w₃ : Fin 8,
        w₁ ≠ w₂ ∧ w₁ ≠ w₃ ∧ w₂ ≠ w₃ ∧
        w₁ ≠ 0 ∧ w₁ ≠ 1 ∧ w₁ ≠ u ∧
        w₂ ≠ 0 ∧ w₂ ≠ 1 ∧ w₂ ≠ u ∧
        w₃ ≠ 0 ∧ w₃ ≠ 1 ∧ w₃ ≠ u ∧
        oneHighFamilyInternalEdges 4 w₁ = 1 ∧
        oneHighFamilyInternalEdges 4 w₂ = 1 ∧
        oneHighFamilyInternalEdges 4 w₃ = 1 := by
  by_cases hedge : oneHighFamilyInternalEdges 4 u = 1
  · exact Or.inl hedge
  · right
    have hu2 : u ≠ 2 := by
      intro h
      subst u
      exact hedge (by decide)
    have hu4 : u ≠ 4 := by
      intro h
      subst u
      exact hedge (by decide)
    have hu6 : u ≠ 6 := by
      intro h
      subst u
      exact hedge (by decide)
    exact ⟨2, 4, 6, by decide, by decide, by decide,
      by decide, by decide, hu2.symm,
      by decide, by decide, hu4.symm,
      by decide, by decide, hu6.symm,
      by decide, by decide, by decide⟩

theorem OneHighReciprocalSameMissEdges.graphTable_profileFourHasReciprocalEntry
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {hfree : ¬ containsC4 V G} {v : V} {hv : G.degree v = 8}
    {p : OneHighRawV2Presentation G hfree v}
    (q : OneHighReciprocalSameMissEdges G hfree hv p)
    (hprofile : p.profile = 4)
    (huEdge : oneHighFamilyInternalEdges p.profile (p.branchLabel q.u) = 1) :
    oneHighProfileFourHasReciprocalEntry
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
  have hu246 : p.branchLabel q.u = 2 ∨ p.branchLabel q.u = 4 ∨
      p.branchLabel q.u = 6 :=
    profile_four_oneEdge_eq_two_or_four_or_six _ hu0 hu1
      (by simpa [hprofile] using huEdge)
  have hcount := oneHighGraphSourcePairing_endpointCount G hfree hv p
    (p.branchLabel q.s) (p.branchLabel q.u)
  rw [q.source_pairing_eq_singleton (by omega), q.s_label] at hcount
  rcases hu246 with hu2 | hu4 | hu6
  · rw [hu2] at hcount
    have hrelevant : oneHighGraphRelevantMissTable
        (oneHighRelabeledLeafGraph G v
          (oneHighLeafFinFortyEquiv G hfree v p.branchLabel p.leafLabel))
        p.profile 0 2 = 2 := by
      simpa [oneHighPairingEndpointCount,
        oneHighLabelPairEndpointCount] using hcount.symm
    simp only [oneHighProfileFourHasReciprocalEntry, Bool.or_eq_true,
      decide_eq_true_eq]
    exact Or.inl (Or.inl (by simpa [oneHighGraphRelevantMissTable,
      oneHighFamilyTableGet] using hrelevant))
  · rw [hu4] at hcount
    have hrelevant : oneHighGraphRelevantMissTable
        (oneHighRelabeledLeafGraph G v
          (oneHighLeafFinFortyEquiv G hfree v p.branchLabel p.leafLabel))
        p.profile 0 4 = 2 := by
      simpa [oneHighPairingEndpointCount,
        oneHighLabelPairEndpointCount] using hcount.symm
    simp only [oneHighProfileFourHasReciprocalEntry, Bool.or_eq_true,
      decide_eq_true_eq]
    exact Or.inl (Or.inr (by simpa [oneHighGraphRelevantMissTable,
      oneHighFamilyTableGet] using hrelevant))
  · rw [hu6] at hcount
    have hrelevant : oneHighGraphRelevantMissTable
        (oneHighRelabeledLeafGraph G v
          (oneHighLeafFinFortyEquiv G hfree v p.branchLabel p.leafLabel))
        p.profile 0 6 = 2 := by
      simpa [oneHighPairingEndpointCount,
        oneHighLabelPairEndpointCount] using hcount.symm
    simp only [oneHighProfileFourHasReciprocalEntry, Bool.or_eq_true,
      decide_eq_true_eq]
    exact Or.inr (by simpa [oneHighGraphRelevantMissTable,
      oneHighFamilyTableGet] using hrelevant)

/-- Profile four has a 46-row finite arm or three distinct isolated-target
packing witnesses. -/
theorem OneHighReciprocalSameMissEdges.profileFour_targetOneEdge_or_three_isolatedTargets
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {hfree : ¬ containsC4 V G} {v : V} {hv : G.degree v = 8}
    {p : OneHighRawV2Presentation G hfree v}
    (q : OneHighReciprocalSameMissEdges G hfree hv p)
    (hprofile : p.profile = 4) :
    oneHighFamilyInternalEdges p.profile (p.branchLabel q.u) = 1 ∨
      ∃ w₁ w₂ w₃ : {r : V // r ∈ G.neighborSet v},
        w₁ ≠ w₂ ∧ w₁ ≠ w₃ ∧ w₂ ≠ w₃ ∧
        w₁ ≠ q.u ∧ w₂ ≠ q.u ∧ w₃ ≠ q.u ∧
        Nonempty (OneHighReciprocalIsolatedTarget G hfree hv p q w₁) ∧
        Nonempty (OneHighReciprocalIsolatedTarget G hfree hv p q w₂) ∧
        Nonempty (OneHighReciprocalIsolatedTarget G hfree hv p q w₃) := by
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
  rcases profile_four_targetOneEdge_or_three_other_oneEdge
      (p.branchLabel q.u) hu0 hu1 with huEdge | hother
  · exact Or.inl (by simpa [hprofile] using huEdge)
  · right
    rcases hother with ⟨i₁, i₂, i₃, hi12, hi13, hi23,
      hi10, hi11, hi1u, hi20, hi21, hi2u, hi30, hi31, hi3u,
      hi1Edge, hi2Edge, hi3Edge⟩
    let w₁ := p.branchLabel.symm i₁
    let w₂ := p.branchLabel.symm i₂
    let w₃ := p.branchLabel.symm i₃
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
    have distinctOf {i j : Fin 8} (hij : i ≠ j) :
        p.branchLabel.symm i ≠ p.branchLabel.symm j := by
      intro heq
      apply hij
      simpa using congrArg p.branchLabel heq
    have notU {i : Fin 8} (hiu : i ≠ p.branchLabel q.u) :
        p.branchLabel.symm i ≠ q.u := by
      intro heq
      apply hiu
      simpa using congrArg p.branchLabel heq
    have hw₁u : w₁ ≠ q.u := notU hi1u
    have hw₂u : w₂ ≠ q.u := notU hi2u
    have hw₃u : w₃ ≠ q.u := notU hi3u
    have hw₁Edge : oneHighFamilyInternalEdges p.profile
        (p.branchLabel w₁) = 1 := by simpa [hprofile, w₁] using hi1Edge
    have hw₂Edge : oneHighFamilyInternalEdges p.profile
        (p.branchLabel w₂) = 1 := by simpa [hprofile, w₂] using hi2Edge
    have hw₃Edge : oneHighFamilyInternalEdges p.profile
        (p.branchLabel w₃) = 1 := by simpa [hprofile, w₃] using hi3Edge
    exact ⟨w₁, w₂, w₃, distinctOf hi12, distinctOf hi13,
      distinctOf hi23, hw₁u, hw₂u, hw₃u,
      q.nonempty_isolatedTarget (by omega) (farMem i₁ hi10 hi11) hw₁u hw₁Edge,
      q.nonempty_isolatedTarget (by omega) (farMem i₂ hi20 hi21) hw₂u hw₂Edge,
      q.nonempty_isolatedTarget (by omega) (farMem i₃ hi30 hi31) hw₃u hw₃Edge⟩

theorem OneHighReciprocalSameMissEdges.storedTable_mem_profileFourInventory_or_three_isolatedTargets
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {hfree : ¬ containsC4 V G} {v : V} {hv : G.degree v = 8}
    {p : OneHighRawV2Presentation G hfree v}
    (q : OneHighReciprocalSameMissEdges G hfree hv p)
    (hprofile : p.profile = 4)
    (stored : OneHighMissTable)
    (hstored : stored ∈ oneHighCapacityInventoryTables 4)
    (hagree : OneHighTableRelevantAgree
      (oneHighFamilyGraphTable
        (oneHighRelabeledLeafGraph G v
          (oneHighLeafFinFortyEquiv G hfree v p.branchLabel p.leafLabel))
        p.profile) stored) :
    stored ∈ oneHighProfileFourReciprocalEntryInventoryTables ∨
      ∃ w₁ w₂ w₃ : {r : V // r ∈ G.neighborSet v},
        w₁ ≠ w₂ ∧ w₁ ≠ w₃ ∧ w₂ ≠ w₃ ∧
        w₁ ≠ q.u ∧ w₂ ≠ q.u ∧ w₃ ≠ q.u ∧
        Nonempty (OneHighReciprocalIsolatedTarget G hfree hv p q w₁) ∧
        Nonempty (OneHighReciprocalIsolatedTarget G hfree hv p q w₂) ∧
        Nonempty (OneHighReciprocalIsolatedTarget G hfree hv p q w₃) := by
  rcases q.profileFour_targetOneEdge_or_three_isolatedTargets hprofile with
      huEdge | hisolated
  · left
    rw [oneHighProfileFourReciprocalEntryInventoryTables, List.mem_filter]
    exact ⟨hstored, oneHighProfileFourHasReciprocalEntry_of_relevantAgree
      hagree (q.graphTable_profileFourHasReciprocalEntry hprofile huEdge)⟩
  · exact Or.inr hisolated

/-- Checked UNSAT coverage of the 46 finite rows leaves three distinct
isolated-target packing witnesses. -/
theorem OneHighReciprocalSameMissEdges.exists_three_isolatedTargets_of_profileFour_checked
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    {v : Fin 49} {hv : G.degree v = 8}
    {p : OneHighRawV2Presentation G hfree v}
    (q : OneHighReciprocalSameMissEdges G hfree hv p)
    (hprofile : p.profile = 4)
    (stored : OneHighMissTable)
    (hstored : stored ∈ oneHighCapacityInventoryTables 4)
    (hagree : OneHighTableRelevantAgree
      (oneHighFamilyGraphTable
        (oneHighRelabeledLeafGraph G v
          (oneHighLeafFinFortyEquiv G hfree v p.branchLabel p.leafLabel))
        p.profile) stored)
    (hchecked : ∀ table ∈ oneHighProfileFourReciprocalEntryInventoryTables,
      OneHighFamilyV2CheckedUnsat 4 table) :
    ∃ w₁ w₂ w₃ : {r : Fin 49 // r ∈ G.neighborSet v},
      w₁ ≠ w₂ ∧ w₁ ≠ w₃ ∧ w₂ ≠ w₃ ∧
      w₁ ≠ q.u ∧ w₂ ≠ q.u ∧ w₃ ≠ q.u ∧
      Nonempty (OneHighReciprocalIsolatedTarget G hfree hv p q w₁) ∧
      Nonempty (OneHighReciprocalIsolatedTarget G hfree hv p q w₂) ∧
      Nonempty (OneHighReciprocalIsolatedTarget G hfree hv p q w₃) := by
  rcases q.storedTable_mem_profileFourInventory_or_three_isolatedTargets
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

/-- Among three isolated-target witnesses, two use the same endpoint of the
reciprocal source edge as their isolated vertex.  This is the packing form
needed downstream: the same source vertex reaches isolated vertices in two
distinct branches. -/
theorem exists_sameSide_isolatedTarget_pair_of_three
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {hfree : ¬ containsC4 V G} {v : V} {hv : G.degree v = 8}
    {p : OneHighRawV2Presentation G hfree v}
    {q : OneHighReciprocalSameMissEdges G hfree hv p}
    {w₁ w₂ w₃ : {r : V // r ∈ G.neighborSet v}}
    (hw12 : w₁ ≠ w₂) (hw13 : w₁ ≠ w₃) (hw23 : w₂ ≠ w₃)
    (hT₁ : Nonempty (OneHighReciprocalIsolatedTarget G hfree hv p q w₁))
    (hT₂ : Nonempty (OneHighReciprocalIsolatedTarget G hfree hv p q w₂))
    (hT₃ : Nonempty (OneHighReciprocalIsolatedTarget G hfree hv p q w₃)) :
    ∃ wa wb : {r : V // r ∈ G.neighborSet v}, wa ≠ wb ∧
      ∃ (Ta : OneHighReciprocalIsolatedTarget G hfree hv p q wa)
        (Tb : OneHighReciprocalIsolatedTarget G hfree hv p q wb),
        (((G.neighborFinset Ta.y ∩ secondLayerBranch G v wa).card = 0 ∧
          (G.neighborFinset Tb.y ∩ secondLayerBranch G v wb).card = 0) ∨
         ((G.neighborFinset Ta.y' ∩ secondLayerBranch G v wa).card = 0 ∧
          (G.neighborFinset Tb.y' ∩ secondLayerBranch G v wb).card = 0)) := by
  rcases hT₁ with ⟨T₁⟩
  rcases hT₂ with ⟨T₂⟩
  rcases hT₃ with ⟨T₃⟩
  rcases T₁.isolated with h₁ | h₁
  · rcases T₂.isolated with h₂ | h₂
    · exact ⟨w₁, w₂, hw12, T₁, T₂, Or.inl ⟨h₁, h₂⟩⟩
    · rcases T₃.isolated with h₃ | h₃
      · exact ⟨w₁, w₃, hw13, T₁, T₃, Or.inl ⟨h₁, h₃⟩⟩
      · exact ⟨w₂, w₃, hw23, T₂, T₃, Or.inr ⟨h₂, h₃⟩⟩
  · rcases T₂.isolated with h₂ | h₂
    · rcases T₃.isolated with h₃ | h₃
      · exact ⟨w₂, w₃, hw23, T₂, T₃, Or.inl ⟨h₂, h₃⟩⟩
      · exact ⟨w₁, w₃, hw13, T₁, T₃, Or.inr ⟨h₁, h₃⟩⟩
    · exact ⟨w₁, w₂, hw12, T₁, T₂, Or.inr ⟨h₁, h₂⟩⟩

/-- Certificate-backed profile-four capstone in same-side packing form. -/
theorem OneHighReciprocalSameMissEdges.exists_sameSide_isolatedTarget_pair_of_profileFour_checked
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    {v : Fin 49} {hv : G.degree v = 8}
    {p : OneHighRawV2Presentation G hfree v}
    (q : OneHighReciprocalSameMissEdges G hfree hv p)
    (hprofile : p.profile = 4)
    (stored : OneHighMissTable)
    (hstored : stored ∈ oneHighCapacityInventoryTables 4)
    (hagree : OneHighTableRelevantAgree
      (oneHighFamilyGraphTable
        (oneHighRelabeledLeafGraph G v
          (oneHighLeafFinFortyEquiv G hfree v p.branchLabel p.leafLabel))
        p.profile) stored)
    (hchecked : ∀ table ∈ oneHighProfileFourReciprocalEntryInventoryTables,
      OneHighFamilyV2CheckedUnsat 4 table) :
    ∃ wa wb : {r : Fin 49 // r ∈ G.neighborSet v}, wa ≠ wb ∧
      ∃ (Ta : OneHighReciprocalIsolatedTarget G hfree hv p q wa)
        (Tb : OneHighReciprocalIsolatedTarget G hfree hv p q wb),
        (((G.neighborFinset Ta.y ∩ secondLayerBranch G v wa).card = 0 ∧
          (G.neighborFinset Tb.y ∩ secondLayerBranch G v wb).card = 0) ∨
         ((G.neighborFinset Ta.y' ∩ secondLayerBranch G v wa).card = 0 ∧
          (G.neighborFinset Tb.y' ∩ secondLayerBranch G v wb).card = 0)) := by
  obtain ⟨w₁, w₂, w₃, hw12, hw13, hw23, _, _, _, hT₁, hT₂, hT₃⟩ :=
    q.exists_three_isolatedTargets_of_profileFour_checked G hfree hmin
      hprofile stored hstored hagree hchecked
  exact exists_sameSide_isolatedTarget_pair_of_three
    hw12 hw13 hw23 hT₁ hT₂ hT₃

end Erdos85
