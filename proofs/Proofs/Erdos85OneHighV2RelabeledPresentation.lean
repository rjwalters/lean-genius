import Proofs.Erdos85OneHighV2ProfileSymmetry

/-! # Rebuilding a raw presentation after a profile symmetry -/

namespace Erdos85

open SimpleGraph

noncomputable section

theorem OneHighTableRelevantAgree.trans {a b c : OneHighMissTable}
    (hab : OneHighTableRelevantAgree a b)
    (hbc : OneHighTableRelevantAgree b c) :
    OneHighTableRelevantAgree a c := by
  intro pair hpair
  exact (hab pair hpair).trans (hbc pair hpair)

/-- Pure finite-classifier obligation for the stored representative lists.
It contains no graph or CNF semantics: every admissible finite table must
have a profile-stabilizer image agreeing with a stored table. -/
def OneHighFiniteRepresentativeCover
    (tables : Fin 5 → List OneHighMissTable) : Prop :=
  ∀ (profile : Fin 5) (table : OneHighMissTable),
    OneHighFamilyV2Admissible profile.val table →
      ∃ (σ : OneHighProfilePerm profile.val) (stored : OneHighMissTable),
        stored ∈ tables profile ∧
        OneHighTableRelevantAgree (σ.permuteTable table) stored

/-- After any profile-preserving CP4 branch permutation, fresh branch-local
labels can be chosen so that the complete PURE constraints (including the
numeric lex WLOG) hold again. -/
theorem OneHighRawV2Presentation.exists_relabel
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49) {v : V} (hv : G.degree v = 8)
    (p : OneHighRawV2Presentation G hfree v)
    (σ : OneHighProfilePerm p.profile) :
    ∃ p' : OneHighRawV2Presentation G hfree v,
      p'.mate = p.mate ∧
      p'.profile = p.profile ∧
      p'.branchLabel = p.relabelBranch σ := by
  classical
  let branchLabel := p.relabelBranch σ
  have hlabels : ∀ s, ∃ (twoEdges : Bool)
      (e : secondLayerBranch G v s ≃ Fin 5),
      ((twoEdges = false ∧ highBranchMatchedCount G v s = 2) ∨
        (twoEdges = true ∧ highBranchMatchedCount G v s = 4)) ∧
      (∀ x y, decide (G.Adj x.1 y.1) =
        oneHighCanonicalBranchAdj twoEdges (e x) (e y)) ∧
      branchLabel (oneHighMissingBranch G v p.mate s (e.symm 0).1) ≤
        branchLabel (oneHighMissingBranch G v p.mate s (e.symm 1).1) ∧
      (twoEdges = true →
        branchLabel (oneHighMissingBranch G v p.mate s (e.symm 2).1) ≤
          branchLabel (oneHighMissingBranch G v p.mate s (e.symm 3).1) ∧
        branchLabel (oneHighMissingBranch G v p.mate s (e.symm 0).1) ≤
          branchLabel (oneHighMissingBranch G v p.mate s (e.symm 2).1)) := by
    intro s
    exact exists_oneHigh_branchVertexLabeling_generatorLex
      G hfree hmin hcard hv p.unique_high p.external_empty p.outer_degree
        p.mate p.mate_involutive p.mate_adj branchLabel s
  let twoEdges := fun s => (hlabels s).choose
  let leafLabel := fun s => (hlabels s).choose_spec.choose
  have hword : ∀ i, twoEdges (branchLabel.symm i) =
      oneHighFamilyTwoEdges p.profile i := by
    intro i
    have hstate := (hlabels (branchLabel.symm i)).choose_spec.choose_spec.1
    have hcount := p.relabelBranch_matchedCount σ i
    change highBranchMatchedCount G v (branchLabel.symm i) = _ at hcount
    unfold oneHighFamilyInternalEdges at hcount
    unfold oneHighFamilyTwoEdges
    by_cases hi : i.val % 2 = 0 ∧ i.val / 2 < p.profile
    · simp [hi] at hcount ⊢
      rcases hstate with hstate | hstate
      · exact hstate.1
      · omega
    · simp [hi] at hcount ⊢
      rcases hstate with hstate | hstate
      · omega
      · exact hstate.1
  have hc : OneHighPureFamilyCnfConstraints p.profile
      (oneHighRelabeledLeafGraph G v
        (oneHighLeafFinFortyEquiv G hfree v branchLabel leafLabel)) := by
    let E := oneHighLeafFinFortyEquiv G hfree v branchLabel leafLabel
    let R := oneHighRelabeledLeafGraph G v E
    refine ⟨?_, ?_⟩
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro i j hij
        exact oneHighRelabeledLeafGraph_adj_eq_familyInternal
          G hfree branchLabel twoEdges leafLabel
            (fun s => (hlabels s).choose_spec.choose_spec.2.1)
            p.profile hword i j hij
      · intro i j hij
        exact oneHighRelabeledLeafGraph_not_adj_of_standardMate_blocks
          G hfree p.mate p.mate_adj branchLabel
            (p.relabelBranch_mate σ) leafLabel i j hij
      · intro i j hij
        exact oneHighRelabeledLeafGraph_common_le_one G hfree E i j hij
      · intro i j hij hblock
        exact oneHighRelabeledLeafGraph_sameBlock_common_eq_zero
          G hfree branchLabel leafLabel i j hij hblock
      · intro i k l hkl hblock
        exact oneHighRelabeledLeafGraph_not_adj_two_in_sameBlock
          G hfree branchLabel leafLabel i k l hkl hblock
      · intro i
        exact card_oneHighEncodedFarNeighbors_eq_familyFarDegree
          G hfree p.external_empty p.mate p.mate_adj branchLabel
            (p.relabelBranch_mate σ) twoEdges leafLabel
            (fun s => (hlabels s).choose_spec.choose_spec.2.1)
            p.profile hword i (p.outer_degree (E.symm i).2)
      · intro b
        have hledger := card_oneHighEncodedCommonPairBlock_add_familyIN_eq_thirty
          G hfree hmin hcard hv p.unique_high p.external_empty p.outer_degree
            p.mate p.mate_involutive p.mate_adj branchLabel
            (p.relabelBranch_mate σ) leafLabel p.profile
            (p.relabelBranch_matchedCount σ) (branchLabel.symm b)
        simpa [R, E] using hledger
    · apply oneHighPureFamilyLexConstraints_of_generatorLabels
        G hfree hv p.external_empty p.outer_degree p.mate p.mate_adj
          branchLabel (p.relabelBranch_mate σ) twoEdges leafLabel
          (fun s => (hlabels s).choose_spec.choose_spec.2.1)
          p.profile hword
      intro s
      exact ⟨(hlabels s).choose_spec.choose_spec.2.2.1,
        (hlabels s).choose_spec.choose_spec.2.2.2⟩
  let p' : OneHighRawV2Presentation G hfree v :=
    { mate := p.mate
      mate_involutive := p.mate_involutive
      mate_adj := p.mate_adj
      branchLabel := branchLabel
      branch_mate := p.relabelBranch_mate σ
      leafLabel := leafLabel
      profile := p.profile
      profile_le := p.profile_le
      matched_count := p.relabelBranch_matchedCount σ
      unique_high := p.unique_high
      external_empty := p.external_empty
      outer_degree := p.outer_degree
      constraints := hc }
  exact ⟨p', rfl, rfl, rfl⟩

/-- The rebuilt presentation realizes the pullback action on every table
coordinate consumed by the exact-v2 generator.  Fresh within-branch labels
do not affect this statement because graph-table entries are intrinsic branch
miss counts. -/
theorem OneHighRawV2Presentation.exists_relabel_graphTable_agrees
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49) {v : V} (hv : G.degree v = 8)
    (p : OneHighRawV2Presentation G hfree v)
    (σ : OneHighProfilePerm p.profile) :
    ∃ p' : OneHighRawV2Presentation G hfree v,
      p'.mate = p.mate ∧ p'.profile = p.profile ∧
      p'.branchLabel = p.relabelBranch σ ∧
      OneHighTableRelevantAgree
        (oneHighFamilyGraphTable
          (oneHighRelabeledLeafGraph G v
            (oneHighLeafFinFortyEquiv G hfree v
              p'.branchLabel p'.leafLabel)) p'.profile)
        (σ.permuteTable
          (oneHighFamilyGraphTable
            (oneHighRelabeledLeafGraph G v
              (oneHighLeafFinFortyEquiv G hfree v
                p.branchLabel p.leafLabel)) p.profile)) := by
  classical
  obtain ⟨p', hmate, hprofile, hlabel⟩ :=
    p.exists_relabel G hfree hmin hcard hv σ
  refine ⟨p', hmate, hprofile, hlabel, ?_⟩
  intro pair hpair
  have hp := oneHighFamilyTablePairs_mem_bounds hpair
  let c : Fin 8 := ⟨pair.1, hp.1⟩
  let j : Fin 8 := ⟨pair.2, hp.2.1⟩
  let s' := p'.branchLabel.symm c
  let u' := p'.branchLabel.symm j
  let s := p.branchLabel.symm (σ.1.symm c)
  let u := p.branchLabel.symm (σ.1.symm j)
  have hu's' : u' ≠ s' := by
    intro h
    have := congrArg p'.branchLabel h
    simp [u', s'] at this
    exact (Fin.ne_of_lt hp.2.2.1) this.symm
  have hu'm' : u' ≠ p'.mate s' := by
    intro h
    have hh := congrArg p'.branchLabel h
    rw [p'.branch_mate] at hh
    simp [u', s'] at hh
    have hval := congrArg Fin.val hh
    rw [oneHighStandardMate_val_eq_xor] at hval
    exact hp.2.2.2 hval
  have hus : u ≠ s := by
    intro h
    have hh := congrArg p.branchLabel h
    simp [u, s] at hh
    exact (Fin.ne_of_lt hp.2.2.1) hh.symm
  have hum : u ≠ p.mate s := by
    intro h
    have hh := congrArg p.branchLabel h
    rw [p.branch_mate] at hh
    simp only [u, s, Equiv.apply_symm_apply] at hh
    have hcj := congrArg σ.1 hh
    rw [σ.1.apply_symm_apply, σ.2.1, σ.1.apply_symm_apply] at hcj
    have hval := congrArg Fin.val hcj
    rw [oneHighStandardMate_val_eq_xor] at hval
    exact hp.2.2.2 hval
  have hnew := oneHighFamilyGraphTable_eq_highBranchMissCount
    G hfree v p'.mate p'.branchLabel p'.branch_mate p'.leafLabel
      p'.profile p'.constraints s' u' hu's' hu'm'
  have hold := oneHighFamilyGraphTable_eq_highBranchMissCount
    G hfree v p.mate p.branchLabel p.branch_mate p.leafLabel
      p.profile p.constraints s u hus hum
  have hnew' : oneHighFamilyGraphTable
      (oneHighRelabeledLeafGraph G v
        (oneHighLeafFinFortyEquiv G hfree v
          p'.branchLabel p'.leafLabel)) p'.profile c.val j.val =
      highBranchMissCount G v s' u' := by
    simpa [s', u'] using hnew
  have hold' : oneHighFamilyGraphTable
      (oneHighRelabeledLeafGraph G v
        (oneHighLeafFinFortyEquiv G hfree v
          p.branchLabel p.leafLabel)) p.profile
        (σ.1.symm c).val (σ.1.symm j).val =
      highBranchMissCount G v s u := by
    simpa [s, u] using hold
  have hs : s' = s := by
    simp [s', s, hlabel, OneHighRawV2Presentation.relabelBranch]
  have hu : u' = u := by
    simp [u', u, hlabel, OneHighRawV2Presentation.relabelBranch]
  change oneHighFamilyGraphTable _ _ c.val j.val =
    σ.permuteTable _ c.val j.val
  rw [OneHighProfilePerm.permuteTable_apply]
  rw [hnew', hold', hs, hu]

/-- A verified finite representative classifier supplies the artifact-aligned
raw orbit cover required by the h=1 terminal. -/
theorem oneHighRawV2OrbitCover_of_finiteRepresentativeCover
    {tables : Fin 5 → List OneHighMissTable}
    (hcover : OneHighFiniteRepresentativeCover tables) :
    OneHighRawV2OrbitCover tables := by
  intro G _ _ _ hfree hmin hHigh
  have hnonempty : (orderFortyNineHighVertices G).Nonempty :=
    Finset.card_pos.mp (by omega)
  obtain ⟨v, hvMem⟩ := hnonempty
  have hv : G.degree v = 8 := by
    simpa [orderFortyNineHighVertices] using hvMem
  obtain ⟨p⟩ := orderFortyNine_exists_rawOneHighPresentationData
    G hfree hmin (Fintype.card_fin 49) hHigh hv
  let profile : Fin 5 :=
    ⟨p.profile, Nat.lt_succ_iff.mpr p.profile_le⟩
  let E := oneHighLeafFinFortyEquiv G hfree v p.branchLabel p.leafLabel
  let R := oneHighRelabeledLeafGraph G v E
  have hadmissible : OneHighFamilyV2Admissible profile.val
      (oneHighFamilyGraphTable R profile.val) := by
    simpa [profile, R, E] using p.graphTable_admissible G hfree hv
  obtain ⟨σ, stored, hmem, hstored⟩ :=
    hcover profile (oneHighFamilyGraphTable R profile.val) hadmissible
  obtain ⟨p', _hmate, hprofile, _hlabel, hagree⟩ :=
    p.exists_relabel_graphTable_agrees G hfree hmin
      (Fintype.card_fin 49) hv σ
  refine ⟨v, hv, p', stored, ?_, ?_⟩
  · simpa [profile, hprofile] using hmem
  · exact hagree.trans hstored

end

end Erdos85
