import Proofs.Erdos85OneHighV2ProfileSymmetry

/-! # Rebuilding a raw presentation after a profile symmetry -/

namespace Erdos85

open SimpleGraph

noncomputable section

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

end

end Erdos85
