import Proofs.Erdos85OneHighProfileFourReciprocalInventoryTerminal

/-! # Saturation of isolated reciprocal targets -/

namespace Erdos85

/-- An internally isolated second-layer vertex hits every one of its six far
branches exactly once.  This is pointwise dirty conservation plus the C4-free
per-branch upper bound. -/
theorem oneHigh_isolatedVertex_hits_farBranch
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {hfree : ¬ containsC4 V G} {v : V} {hv : G.degree v = 8}
    {p : OneHighRawV2Presentation G hfree v}
    {w : {r : V // r ∈ G.neighborSet v}} {y : V}
    (hy : y ∈ secondLayerBranch G v w)
    (hisolated : (G.neighborFinset y ∩
      secondLayerBranch G v w).card = 0)
    {u : {r : V // r ∈ G.neighborSet v}}
    (hu : u ∈ ((Finset.univ.erase w).erase (p.mate w))) :
    (G.neighborFinset y ∩ secondLayerBranch G v u).card = 1 := by
  have hySecond : y ∈ secondLayer G v := by
    rw [secondLayer]
    exact Finset.mem_biUnion.mpr ⟨w, Finset.mem_univ _, hy⟩
  have hyDegree : G.degree y = 7 := p.outer_degree hySecond
  have hmiss := card_farBranch_misses_eq_internalDegree
    G hfree (d := 7) (by omega) p.external_empty w (p.mate w)
      (p.mate_adj w) y hy hyDegree
  rw [hisolated] at hmiss
  have hnotzero :
      (G.neighborFinset y ∩ secondLayerBranch G v u).card ≠ 0 := by
    intro hzero
    have humem : u ∈ (((Finset.univ.erase w).erase (p.mate w)).filter
        fun z => (G.neighborFinset y ∩
          secondLayerBranch G v z).card = 0) :=
      Finset.mem_filter.mpr ⟨hu, hzero⟩
    have hpos := Finset.card_pos.mpr ⟨u, humem⟩
    omega
  have hyu : y ≠ u.1 := by
    intro heq
    subst y
    exact (Finset.mem_sdiff.mp hy).2 (by
      simp only [Finset.mem_insert, SimpleGraph.mem_neighborFinset]
      exact Or.inr u.2)
  have hle := card_neighborFinset_inter_secondLayerBranch_le_one
    G hfree v y u hyu
  omega

theorem OneHighReciprocalIsolatedTarget.y_hits_farBranch
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {hfree : ¬ containsC4 V G} {v : V} {hv : G.degree v = 8}
    {p : OneHighRawV2Presentation G hfree v}
    {q : OneHighReciprocalSameMissEdges G hfree hv p}
    {w : {r : V // r ∈ G.neighborSet v}}
    (T : OneHighReciprocalIsolatedTarget G hfree hv p q w)
    (hisolated : (G.neighborFinset T.y ∩
      secondLayerBranch G v w).card = 0)
    {u : {r : V // r ∈ G.neighborSet v}}
    (hu : u ∈ ((Finset.univ.erase w).erase (p.mate w))) :
    (G.neighborFinset T.y ∩ secondLayerBranch G v u).card = 1 :=
  oneHigh_isolatedVertex_hits_farBranch (hv := hv) T.y_mem hisolated hu

theorem OneHighReciprocalIsolatedTarget.y'_hits_farBranch
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {hfree : ¬ containsC4 V G} {v : V} {hv : G.degree v = 8}
    {p : OneHighRawV2Presentation G hfree v}
    {q : OneHighReciprocalSameMissEdges G hfree hv p}
    {w : {r : V // r ∈ G.neighborSet v}}
    (T : OneHighReciprocalIsolatedTarget G hfree hv p q w)
    (hisolated : (G.neighborFinset T.y' ∩
      secondLayerBranch G v w).card = 0)
    {u : {r : V // r ∈ G.neighborSet v}}
    (hu : u ∈ ((Finset.univ.erase w).erase (p.mate w))) :
    (G.neighborFinset T.y' ∩ secondLayerBranch G v u).card = 1 :=
  oneHigh_isolatedVertex_hits_farBranch (hv := hv) T.y'_mem hisolated hu

theorem profile_four_oneEdge_not_standardMate
    (a b : Fin 8)
    (ha : oneHighFamilyInternalEdges 4 a = 1)
    (hb : oneHighFamilyInternalEdges 4 b = 1) :
    b ≠ oneHighStandardMate a := by
  native_decide +revert

/-- Two distinct one-edge branches in profile four cannot be root mates, so
each lies in the other's six-branch far sector. -/
theorem profileFour_distinct_oneEdge_mem_far
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {hfree : ¬ containsC4 V G} {v : V}
    {p : OneHighRawV2Presentation G hfree v}
    (hprofile : p.profile = 4)
    {wa wb : {r : V // r ∈ G.neighborSet v}}
    (hwne : wa ≠ wb)
    (hwa : oneHighFamilyInternalEdges p.profile (p.branchLabel wa) = 1)
    (hwb : oneHighFamilyInternalEdges p.profile (p.branchLabel wb) = 1) :
    wb ∈ ((Finset.univ.erase wa).erase (p.mate wa)) := by
  have hlabelMate : p.branchLabel wb ≠
      oneHighStandardMate (p.branchLabel wa) := by
    have hwa' : oneHighFamilyInternalEdges 4 (p.branchLabel wa) = 1 := by
      simpa [hprofile] using hwa
    have hwb' : oneHighFamilyInternalEdges 4 (p.branchLabel wb) = 1 := by
      simpa [hprofile] using hwb
    exact profile_four_oneEdge_not_standardMate _ _ hwa' hwb'
  apply Finset.mem_erase.mpr
  constructor
  · intro heq
    apply hlabelMate
    rw [heq, p.branch_mate]
  · exact Finset.mem_erase.mpr ⟨hwne.symm, Finset.mem_univ _⟩

/-- Same-side isolated targets in distinct profile-four one-edge branches
must each hit the other target branch exactly once. -/
theorem sameSide_isolatedTargets_hit_eachOtherBranches
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {hfree : ¬ containsC4 V G} {v : V} {hv : G.degree v = 8}
    {p : OneHighRawV2Presentation G hfree v}
    {q : OneHighReciprocalSameMissEdges G hfree hv p}
    (hprofile : p.profile = 4)
    {wa wb : {r : V // r ∈ G.neighborSet v}}
    (hwne : wa ≠ wb)
    (hwa : oneHighFamilyInternalEdges p.profile (p.branchLabel wa) = 1)
    (hwb : oneHighFamilyInternalEdges p.profile (p.branchLabel wb) = 1)
    (Ta : OneHighReciprocalIsolatedTarget G hfree hv p q wa)
    (Tb : OneHighReciprocalIsolatedTarget G hfree hv p q wb)
    (hsame :
      ((G.neighborFinset Ta.y ∩ secondLayerBranch G v wa).card = 0 ∧
       (G.neighborFinset Tb.y ∩ secondLayerBranch G v wb).card = 0) ∨
      ((G.neighborFinset Ta.y' ∩ secondLayerBranch G v wa).card = 0 ∧
       (G.neighborFinset Tb.y' ∩ secondLayerBranch G v wb).card = 0)) :
    (((G.neighborFinset Ta.y ∩ secondLayerBranch G v wb).card = 1 ∧
      (G.neighborFinset Tb.y ∩ secondLayerBranch G v wa).card = 1) ∨
     ((G.neighborFinset Ta.y' ∩ secondLayerBranch G v wb).card = 1 ∧
      (G.neighborFinset Tb.y' ∩ secondLayerBranch G v wa).card = 1)) := by
  have hwab := profileFour_distinct_oneEdge_mem_far
    hprofile hwne hwa hwb
  have hwba := profileFour_distinct_oneEdge_mem_far
    hprofile hwne.symm hwb hwa
  rcases hsame with hsame | hsame
  · exact Or.inl ⟨Ta.y_hits_farBranch hsame.1 hwab,
      Tb.y_hits_farBranch hsame.2 hwba⟩
  · exact Or.inr ⟨Ta.y'_hits_farBranch hsame.1 hwab,
      Tb.y'_hits_farBranch hsame.2 hwba⟩

/-- The complete local packing payload: two same-side isolated targets in
distinct branches, together with the forced mutual branch hits. -/
def OneHighSaturatedSameSideIsolatedPair
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {v : V} (hv : G.degree v = 8)
    (p : OneHighRawV2Presentation G hfree v)
    (q : OneHighReciprocalSameMissEdges G hfree hv p)
    (wa wb : {r : V // r ∈ G.neighborSet v})
    (Ta : OneHighReciprocalIsolatedTarget G hfree hv p q wa)
    (Tb : OneHighReciprocalIsolatedTarget G hfree hv p q wb) : Prop :=
  (((G.neighborFinset Ta.y ∩ secondLayerBranch G v wa).card = 0 ∧
    (G.neighborFinset Tb.y ∩ secondLayerBranch G v wb).card = 0 ∧
    (G.neighborFinset Ta.y ∩ secondLayerBranch G v wb).card = 1 ∧
    (G.neighborFinset Tb.y ∩ secondLayerBranch G v wa).card = 1) ∨
   ((G.neighborFinset Ta.y' ∩ secondLayerBranch G v wa).card = 0 ∧
    (G.neighborFinset Tb.y' ∩ secondLayerBranch G v wb).card = 0 ∧
    (G.neighborFinset Ta.y' ∩ secondLayerBranch G v wb).card = 1 ∧
    (G.neighborFinset Tb.y' ∩ secondLayerBranch G v wa).card = 1))

/-- Certificate-backed profile-four terminal with dirty-conservation
saturation already assembled. -/
theorem OneHighReciprocalSameMissEdges.exists_saturatedSameSidePair_of_profileFour_checked
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
      oneHighFamilyInternalEdges p.profile (p.branchLabel wa) = 1 ∧
      oneHighFamilyInternalEdges p.profile (p.branchLabel wb) = 1 ∧
      ∃ (Ta : OneHighReciprocalIsolatedTarget G hfree hv p q wa)
        (Tb : OneHighReciprocalIsolatedTarget G hfree hv p q wb),
        OneHighSaturatedSameSideIsolatedPair G hfree hv p q wa wb Ta Tb := by
  obtain ⟨wa, wb, hwne, hwa, hwb, Ta, Tb, hsame⟩ :=
    q.exists_sameSide_isolatedTarget_pair_of_profileFour_checked
      G hfree hmin hprofile stored hstored hagree hchecked
  refine ⟨wa, wb, hwne, hwa, hwb, Ta, Tb, ?_⟩
  have hwab := profileFour_distinct_oneEdge_mem_far
    hprofile hwne hwa hwb
  have hwba := profileFour_distinct_oneEdge_mem_far
    hprofile hwne.symm hwb hwa
  rcases hsame with hsame | hsame
  · exact Or.inl ⟨hsame.1, hsame.2,
      Ta.y_hits_farBranch hsame.1 hwab,
      Tb.y_hits_farBranch hsame.2 hwba⟩
  · exact Or.inr ⟨hsame.1, hsame.2,
      Ta.y'_hits_farBranch hsame.1 hwab,
      Tb.y'_hits_farBranch hsame.2 hwba⟩

end Erdos85
