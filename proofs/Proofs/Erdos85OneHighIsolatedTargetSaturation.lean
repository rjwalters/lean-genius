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

/-- Choose the isolated side of a packaged target and retain its forced hit
in any specified far branch. -/
theorem OneHighReciprocalIsolatedTarget.isolatedSide_hits_farBranch
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {hfree : ¬ containsC4 V G} {v : V} {hv : G.degree v = 8}
    {p : OneHighRawV2Presentation G hfree v}
    {q : OneHighReciprocalSameMissEdges G hfree hv p}
    {w : {r : V // r ∈ G.neighborSet v}}
    (T : OneHighReciprocalIsolatedTarget G hfree hv p q w)
    {u : {r : V // r ∈ G.neighborSet v}}
    (hu : u ∈ ((Finset.univ.erase w).erase (p.mate w))) :
    (((G.neighborFinset T.y ∩ secondLayerBranch G v w).card = 0 ∧
      (G.neighborFinset T.y ∩ secondLayerBranch G v u).card = 1) ∨
     ((G.neighborFinset T.y' ∩ secondLayerBranch G v w).card = 0 ∧
      (G.neighborFinset T.y' ∩ secondLayerBranch G v u).card = 1)) := by
  rcases T.isolated with hisolated | hisolated
  · exact Or.inl ⟨hisolated, T.y_hits_farBranch hisolated hu⟩
  · exact Or.inr ⟨hisolated, T.y'_hits_farBranch hisolated hu⟩

theorem profile_three_oneEdge_not_standardMate
    (a b : Fin 8)
    (ha : oneHighFamilyInternalEdges 3 a = 1)
    (hb : oneHighFamilyInternalEdges 3 b = 1) :
    b ≠ oneHighStandardMate a := by
  native_decide +revert

theorem profileThree_distinct_oneEdge_mem_far
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {hfree : ¬ containsC4 V G} {v : V}
    {p : OneHighRawV2Presentation G hfree v}
    (hprofile : p.profile = 3)
    {wa wb : {r : V // r ∈ G.neighborSet v}}
    (hwne : wa ≠ wb)
    (hwa : oneHighFamilyInternalEdges p.profile (p.branchLabel wa) = 1)
    (hwb : oneHighFamilyInternalEdges p.profile (p.branchLabel wb) = 1) :
    wb ∈ ((Finset.univ.erase wa).erase (p.mate wa)) := by
  have hwa' : oneHighFamilyInternalEdges 3 (p.branchLabel wa) = 1 := by
    simpa [hprofile] using hwa
  have hwb' : oneHighFamilyInternalEdges 3 (p.branchLabel wb) = 1 := by
    simpa [hprofile] using hwb
  have hlabelMate := profile_three_oneEdge_not_standardMate
    (p.branchLabel wa) (p.branchLabel wb) hwa' hwb'
  apply Finset.mem_erase.mpr
  constructor
  · intro heq
    apply hlabelMate
    rw [heq, p.branch_mate]
  · exact Finset.mem_erase.mpr ⟨hwne.symm, Finset.mem_univ _⟩

/-- Once the nine profile-three finite rows are checked, both surviving
isolated targets are saturated toward the other one-edge branch. -/
theorem OneHighReciprocalSameMissEdges.exists_mutuallySaturated_isolatedTargets_of_profileThree_checked
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
      w₁ ∈ ((Finset.univ.erase q.s).erase (p.mate q.s)) ∧
      w₂ ∈ ((Finset.univ.erase q.s).erase (p.mate q.s)) ∧
      oneHighFamilyInternalEdges p.profile (p.branchLabel w₁) = 1 ∧
      oneHighFamilyInternalEdges p.profile (p.branchLabel w₂) = 1 ∧
      ∃ (T₁ : OneHighReciprocalIsolatedTarget G hfree hv p q w₁)
        (T₂ : OneHighReciprocalIsolatedTarget G hfree hv p q w₂),
        (((G.neighborFinset T₁.y ∩ secondLayerBranch G v w₁).card = 0 ∧
          (G.neighborFinset T₁.y ∩ secondLayerBranch G v w₂).card = 1) ∨
         ((G.neighborFinset T₁.y' ∩ secondLayerBranch G v w₁).card = 0 ∧
          (G.neighborFinset T₁.y' ∩ secondLayerBranch G v w₂).card = 1)) ∧
        (((G.neighborFinset T₂.y ∩ secondLayerBranch G v w₂).card = 0 ∧
          (G.neighborFinset T₂.y ∩ secondLayerBranch G v w₁).card = 1) ∨
         ((G.neighborFinset T₂.y' ∩ secondLayerBranch G v w₂).card = 0 ∧
          (G.neighborFinset T₂.y' ∩ secondLayerBranch G v w₁).card = 1)) := by
  obtain ⟨w₁, w₂, hwne, hw₁u, hw₂u, hw₁Far, hw₂Far,
    hw₁Edge, hw₂Edge, hT₁, hT₂⟩ :=
    q.exists_two_isolatedTargets_of_profileThree_checked
      G hfree hmin hprofile stored hstored hagree hchecked
  rcases hT₁ with ⟨T₁⟩
  rcases hT₂ with ⟨T₂⟩
  have hw12 := profileThree_distinct_oneEdge_mem_far
    hprofile hwne hw₁Edge hw₂Edge
  have hw21 := profileThree_distinct_oneEdge_mem_far
    hprofile hwne.symm hw₂Edge hw₁Edge
  exact ⟨w₁, w₂, hwne, hw₁u, hw₂u, hw₁Far, hw₂Far, hw₁Edge, hw₂Edge,
    T₁, T₂, T₁.isolatedSide_hits_farBranch hw12,
    T₂.isolatedSide_hits_farBranch hw21⟩

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

/-- A saturated same-side pair either closes a triangle between its two
isolated vertices or supplies two genuine cross-detour vertices, one in each
target branch. -/
def OneHighSameSideTriangleOrDetour
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {v : V} (hv : G.degree v = 8)
    (p : OneHighRawV2Presentation G hfree v)
    (q : OneHighReciprocalSameMissEdges G hfree hv p)
    (wa wb : {r : V // r ∈ G.neighborSet v})
    (Ta : OneHighReciprocalIsolatedTarget G hfree hv p q wa)
    (Tb : OneHighReciprocalIsolatedTarget G hfree hv p q wb) : Prop :=
  ((G.Adj Ta.y Tb.y ∨
      ∃ za zb : V,
        za ∈ secondLayerBranch G v wb ∧
        zb ∈ secondLayerBranch G v wa ∧
        G.Adj Ta.y za ∧ G.Adj Tb.y zb ∧
        za ≠ Tb.y ∧ zb ≠ Ta.y) ∨
   (G.Adj Ta.y' Tb.y' ∨
      ∃ za zb : V,
        za ∈ secondLayerBranch G v wb ∧
        zb ∈ secondLayerBranch G v wa ∧
        G.Adj Ta.y' za ∧ G.Adj Tb.y' zb ∧
        za ≠ Tb.y' ∧ zb ≠ Ta.y'))

theorem triangleOrDetour_of_saturatedSameSidePair
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {hfree : ¬ containsC4 V G} {v : V} {hv : G.degree v = 8}
    {p : OneHighRawV2Presentation G hfree v}
    {q : OneHighReciprocalSameMissEdges G hfree hv p}
    {wa wb : {r : V // r ∈ G.neighborSet v}}
    {Ta : OneHighReciprocalIsolatedTarget G hfree hv p q wa}
    {Tb : OneHighReciprocalIsolatedTarget G hfree hv p q wb}
    (hsat : OneHighSaturatedSameSideIsolatedPair
      G hfree hv p q wa wb Ta Tb) :
    OneHighSameSideTriangleOrDetour G hfree hv p q wa wb Ta Tb := by
  rcases hsat with hsat | hsat
  · left
    by_cases hab : G.Adj Ta.y Tb.y
    · exact Or.inl hab
    · right
      obtain ⟨za, hza⟩ := Finset.card_eq_one.mp hsat.2.2.1
      obtain ⟨zb, hzb⟩ := Finset.card_eq_one.mp hsat.2.2.2
      have hzaMem : za ∈ G.neighborFinset Ta.y ∩
          secondLayerBranch G v wb := by rw [hza]; simp
      have hzbMem : zb ∈ G.neighborFinset Tb.y ∩
          secondLayerBranch G v wa := by rw [hzb]; simp
      refine ⟨za, zb, (Finset.mem_inter.mp hzaMem).2,
        (Finset.mem_inter.mp hzbMem).2,
        (G.mem_neighborFinset Ta.y za).mp (Finset.mem_inter.mp hzaMem).1,
        (G.mem_neighborFinset Tb.y zb).mp (Finset.mem_inter.mp hzbMem).1,
        ?_, ?_⟩
      · intro heq
        subst za
        exact hab ((G.mem_neighborFinset Ta.y Tb.y).mp
          (Finset.mem_inter.mp hzaMem).1)
      · intro heq
        subst zb
        exact hab (((G.mem_neighborFinset Tb.y Ta.y).mp
          (Finset.mem_inter.mp hzbMem).1).symm)
  · right
    by_cases hab : G.Adj Ta.y' Tb.y'
    · exact Or.inl hab
    · right
      obtain ⟨za, hza⟩ := Finset.card_eq_one.mp hsat.2.2.1
      obtain ⟨zb, hzb⟩ := Finset.card_eq_one.mp hsat.2.2.2
      have hzaMem : za ∈ G.neighborFinset Ta.y' ∩
          secondLayerBranch G v wb := by rw [hza]; simp
      have hzbMem : zb ∈ G.neighborFinset Tb.y' ∩
          secondLayerBranch G v wa := by rw [hzb]; simp
      refine ⟨za, zb, (Finset.mem_inter.mp hzaMem).2,
        (Finset.mem_inter.mp hzbMem).2,
        (G.mem_neighborFinset Ta.y' za).mp (Finset.mem_inter.mp hzaMem).1,
        (G.mem_neighborFinset Tb.y' zb).mp (Finset.mem_inter.mp hzbMem).1,
        ?_, ?_⟩
      · intro heq
        subst za
        exact hab ((G.mem_neighborFinset Ta.y' Tb.y').mp
          (Finset.mem_inter.mp hzaMem).1)
      · intro heq
        subst zb
        exact hab (((G.mem_neighborFinset Tb.y' Ta.y').mp
          (Finset.mem_inter.mp hzbMem).1).symm)

/-- A second vertex in a far branch cannot also meet a canonical source
endpoint once its unique neighbor in that branch is fixed. -/
theorem OneHighReciprocalSameMissEdges.not_adj_other_of_source_unique
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {hfree : ¬ containsC4 V G} {v : V} {hv : G.degree v = 8}
    {p : OneHighRawV2Presentation G hfree v}
    (q : OneHighReciprocalSameMissEdges G hfree hv p)
    (hprofile : 0 < p.profile)
    (z : OneHighMatchedBranchVertices G v q.s)
    {w : {r : V // r ∈ G.neighborSet v}}
    (hw : w ∈ ((Finset.univ.erase q.s).erase (p.mate q.s)))
    (hwu : w ≠ q.u)
    {b a : V} (hb : b ∈ secondLayerBranch G v w) (hzb : G.Adj z.1.1 b)
    (ha : a ∈ secondLayerBranch G v w) (hab : a ≠ b) :
    ¬ G.Adj z.1.1 a := by
  obtain ⟨_, _, hunique⟩ :=
    q.existsUnique_source_neighbor_other hprofile z hw hwu
  intro hza
  exact hab (hunique a ⟨ha, hza⟩ ▸ hunique b ⟨hb, hzb⟩).symm

/-- An internally isolated vertex is nonadjacent to every vertex in its own
branch. -/
theorem not_adj_of_internal_isolated
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {v : V}
    {w : {r : V // r ∈ G.neighborSet v}} {b a : V}
    (hisolated : (G.neighborFinset b ∩
      secondLayerBranch G v w).card = 0)
    (ha : a ∈ secondLayerBranch G v w) :
    ¬ G.Adj b a := by
  intro hba
  have hamem : a ∈ G.neighborFinset b ∩ secondLayerBranch G v w :=
    Finset.mem_inter.mpr ⟨(G.mem_neighborFinset b a).mpr hba, ha⟩
  have hempty := Finset.card_eq_zero.mp hisolated
  rw [hempty] at hamem
  exact Finset.notMem_empty a hamem

/-- Rigid version of the same-side dichotomy.  In the nontriangle arm the
two cross-detour vertices are excluded from both the common source endpoint
and the isolated vertex in their own branch. -/
def OneHighSameSideTriangleOrRigidDetour
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {v : V} (hv : G.degree v = 8)
    (p : OneHighRawV2Presentation G hfree v)
    (q : OneHighReciprocalSameMissEdges G hfree hv p)
    (wa wb : {r : V // r ∈ G.neighborSet v})
    (Ta : OneHighReciprocalIsolatedTarget G hfree hv p q wa)
    (Tb : OneHighReciprocalIsolatedTarget G hfree hv p q wb) : Prop :=
  ((G.Adj Ta.y Tb.y ∨
      ∃ za zb : V,
        za ∈ secondLayerBranch G v wb ∧
        zb ∈ secondLayerBranch G v wa ∧
        G.Adj Ta.y za ∧ G.Adj Tb.y zb ∧
        za ≠ Tb.y ∧ zb ≠ Ta.y ∧
        ¬ G.Adj q.x.1.1 za ∧
        ¬ G.Adj q.x.1.1 zb ∧
        ¬ G.Adj Tb.y za ∧ ¬ G.Adj Ta.y zb) ∨
   (G.Adj Ta.y' Tb.y' ∨
      ∃ za zb : V,
        za ∈ secondLayerBranch G v wb ∧
        zb ∈ secondLayerBranch G v wa ∧
        G.Adj Ta.y' za ∧ G.Adj Tb.y' zb ∧
        za ≠ Tb.y' ∧ zb ≠ Ta.y' ∧
        ¬ G.Adj (oneHighInternalMate G hfree v q.s q.x).1.1 za ∧
        ¬ G.Adj (oneHighInternalMate G hfree v q.s q.x).1.1 zb ∧
        ¬ G.Adj Tb.y' za ∧ ¬ G.Adj Ta.y' zb))

theorem rigidDetour_of_saturatedSameSidePair
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {hfree : ¬ containsC4 V G} {v : V} {hv : G.degree v = 8}
    {p : OneHighRawV2Presentation G hfree v}
    {q : OneHighReciprocalSameMissEdges G hfree hv p}
    (hprofile : 0 < p.profile)
    {wa wb : {r : V // r ∈ G.neighborSet v}}
    (hwaFar : wa ∈ ((Finset.univ.erase q.s).erase (p.mate q.s)))
    (hwbFar : wb ∈ ((Finset.univ.erase q.s).erase (p.mate q.s)))
    (hwau : wa ≠ q.u) (hwbu : wb ≠ q.u)
    {Ta : OneHighReciprocalIsolatedTarget G hfree hv p q wa}
    {Tb : OneHighReciprocalIsolatedTarget G hfree hv p q wb}
    (hsat : OneHighSaturatedSameSideIsolatedPair
      G hfree hv p q wa wb Ta Tb) :
    OneHighSameSideTriangleOrRigidDetour G hfree hv p q wa wb Ta Tb := by
  rcases hsat with hsat | hsat
  · left
    by_cases hab : G.Adj Ta.y Tb.y
    · exact Or.inl hab
    · right
      obtain ⟨za, hza⟩ := Finset.card_eq_one.mp hsat.2.2.1
      obtain ⟨zb, hzb⟩ := Finset.card_eq_one.mp hsat.2.2.2
      have hzaMem : za ∈ G.neighborFinset Ta.y ∩
          secondLayerBranch G v wb := by rw [hza]; simp
      have hzbMem : zb ∈ G.neighborFinset Tb.y ∩
          secondLayerBranch G v wa := by rw [hzb]; simp
      have hzaBranch := (Finset.mem_inter.mp hzaMem).2
      have hzbBranch := (Finset.mem_inter.mp hzbMem).2
      have hAza := (G.mem_neighborFinset Ta.y za).mp
        (Finset.mem_inter.mp hzaMem).1
      have hBzb := (G.mem_neighborFinset Tb.y zb).mp
        (Finset.mem_inter.mp hzbMem).1
      have hzaB : za ≠ Tb.y := by
        intro heq; subst za; exact hab hAza
      have hzbA : zb ≠ Ta.y := by
        intro heq; subst zb; exact hab hBzb.symm
      exact ⟨za, zb, hzaBranch, hzbBranch, hAza, hBzb, hzaB, hzbA,
        q.not_adj_other_of_source_unique hprofile q.x hwbFar hwbu
          Tb.y_mem Tb.x_adj_y hzaBranch hzaB,
        q.not_adj_other_of_source_unique hprofile q.x hwaFar hwau
          Ta.y_mem Ta.x_adj_y hzbBranch hzbA,
        not_adj_of_internal_isolated hsat.2.1 hzaBranch,
        not_adj_of_internal_isolated hsat.1 hzbBranch⟩
  · right
    by_cases hab : G.Adj Ta.y' Tb.y'
    · exact Or.inl hab
    · right
      obtain ⟨za, hza⟩ := Finset.card_eq_one.mp hsat.2.2.1
      obtain ⟨zb, hzb⟩ := Finset.card_eq_one.mp hsat.2.2.2
      have hzaMem : za ∈ G.neighborFinset Ta.y' ∩
          secondLayerBranch G v wb := by rw [hza]; simp
      have hzbMem : zb ∈ G.neighborFinset Tb.y' ∩
          secondLayerBranch G v wa := by rw [hzb]; simp
      have hzaBranch := (Finset.mem_inter.mp hzaMem).2
      have hzbBranch := (Finset.mem_inter.mp hzbMem).2
      have hAza := (G.mem_neighborFinset Ta.y' za).mp
        (Finset.mem_inter.mp hzaMem).1
      have hBzb := (G.mem_neighborFinset Tb.y' zb).mp
        (Finset.mem_inter.mp hzbMem).1
      have hzaB : za ≠ Tb.y' := by
        intro heq; subst za; exact hab hAza
      have hzbA : zb ≠ Ta.y' := by
        intro heq; subst zb; exact hab hBzb.symm
      let xm := oneHighInternalMate G hfree v q.s q.x
      exact ⟨za, zb, hzaBranch, hzbBranch, hAza, hBzb, hzaB, hzbA,
        q.not_adj_other_of_source_unique hprofile xm hwbFar hwbu
          Tb.y'_mem Tb.xmate_adj_y' hzaBranch hzaB,
        q.not_adj_other_of_source_unique hprofile xm hwaFar hwau
          Ta.y'_mem Ta.xmate_adj_y' hzbBranch hzbA,
        not_adj_of_internal_isolated hsat.2.1 hzaBranch,
        not_adj_of_internal_isolated hsat.1 hzbBranch⟩

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
      wa ∈ ((Finset.univ.erase q.s).erase (p.mate q.s)) ∧
      wb ∈ ((Finset.univ.erase q.s).erase (p.mate q.s)) ∧
      wa ≠ q.u ∧ wb ≠ q.u ∧
      ∃ (Ta : OneHighReciprocalIsolatedTarget G hfree hv p q wa)
        (Tb : OneHighReciprocalIsolatedTarget G hfree hv p q wb),
        OneHighSaturatedSameSideIsolatedPair G hfree hv p q wa wb Ta Tb := by
  obtain ⟨wa, wb, hwne, hwa, hwb, hwaFar, hwbFar,
    hwau, hwbu, Ta, Tb, hsame⟩ :=
    q.exists_sameSide_isolatedTarget_pair_of_profileFour_checked
      G hfree hmin hprofile stored hstored hagree hchecked
  refine ⟨wa, wb, hwne, hwa, hwb, hwaFar, hwbFar,
    hwau, hwbu, Ta, Tb, ?_⟩
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

/-- Fully assembled profile-four local residual: saturation plus its exact
triangle-versus-cross-detour consequence. -/
theorem OneHighReciprocalSameMissEdges.exists_saturated_triangleOrDetour_of_profileFour_checked
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
      wa ∈ ((Finset.univ.erase q.s).erase (p.mate q.s)) ∧
      wb ∈ ((Finset.univ.erase q.s).erase (p.mate q.s)) ∧
      wa ≠ q.u ∧ wb ≠ q.u ∧
      ∃ (Ta : OneHighReciprocalIsolatedTarget G hfree hv p q wa)
        (Tb : OneHighReciprocalIsolatedTarget G hfree hv p q wb),
        OneHighSaturatedSameSideIsolatedPair G hfree hv p q wa wb Ta Tb ∧
        OneHighSameSideTriangleOrDetour G hfree hv p q wa wb Ta Tb := by
  obtain ⟨wa, wb, hwne, hwa, hwb, hwaFar, hwbFar,
    hwau, hwbu, Ta, Tb, hsat⟩ :=
    q.exists_saturatedSameSidePair_of_profileFour_checked
      G hfree hmin hprofile stored hstored hagree hchecked
  exact ⟨wa, wb, hwne, hwa, hwb, hwaFar, hwbFar,
    hwau, hwbu, Ta, Tb, hsat,
    triangleOrDetour_of_saturatedSameSidePair hsat⟩

/-- Strongest assembled profile-four residual: the nontriangle arm records
the source and internal nonedges that make both detours rigid five-cycle
skeletons. -/
theorem OneHighReciprocalSameMissEdges.exists_saturated_triangleOrRigidDetour_of_profileFour_checked
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
      wa ∈ ((Finset.univ.erase q.s).erase (p.mate q.s)) ∧
      wb ∈ ((Finset.univ.erase q.s).erase (p.mate q.s)) ∧
      wa ≠ q.u ∧ wb ≠ q.u ∧
      ∃ (Ta : OneHighReciprocalIsolatedTarget G hfree hv p q wa)
        (Tb : OneHighReciprocalIsolatedTarget G hfree hv p q wb),
        OneHighSaturatedSameSideIsolatedPair G hfree hv p q wa wb Ta Tb ∧
        OneHighSameSideTriangleOrRigidDetour G hfree hv p q wa wb Ta Tb := by
  obtain ⟨wa, wb, hwne, hwa, hwb, hwaFar, hwbFar,
    hwau, hwbu, Ta, Tb, hsat⟩ :=
    q.exists_saturatedSameSidePair_of_profileFour_checked
      G hfree hmin hprofile stored hstored hagree hchecked
  exact ⟨wa, wb, hwne, hwa, hwb, hwaFar, hwbFar,
    hwau, hwbu, Ta, Tb, hsat,
    rigidDetour_of_saturatedSameSidePair (by omega)
      hwaFar hwbFar hwau hwbu hsat⟩

end Erdos85
