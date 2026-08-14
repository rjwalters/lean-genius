import Proofs.Erdos85OneHighFamilyCnfSemantics

/-! # Witness-preserving presentation of a raw one-high graph -/

namespace Erdos85

open SimpleGraph

/-- Unlike the older existential PURE-family theorem, this statement retains
the canonical mate and labeling witnesses needed by the exact-v2 graph
ledgers. -/
theorem orderFortyNine_exists_rawOneHighPresentation
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49)
    (hHigh : (orderFortyNineHighVertices G).card = 1)
    {v : V} (hv : G.degree v = 8) :
    ∃ (mate : {z : V // z ∈ G.neighborSet v} →
          {z : V // z ∈ G.neighborSet v})
      (branchLabel : {z : V // z ∈ G.neighborSet v} ≃ Fin 8)
      (leafLabel : ∀ s : {z : V // z ∈ G.neighborSet v},
        secondLayerBranch G v s ≃ Fin 5)
      (profile : Nat),
      Function.Involutive mate ∧
      (∀ s, G.Adj s.1 (mate s).1) ∧
      (∀ s, branchLabel (mate s) =
        oneHighStandardMate (branchLabel s)) ∧
      profile ≤ 4 ∧
      (∀ {w : V}, G.degree w = 8 → w = v) ∧
      externalRepairCandidates G v = ∅ ∧
      (∀ {x : V}, x ∈ secondLayer G v → G.degree x = 7) ∧
      OneHighPureFamilyCnfConstraints profile
        (oneHighRelabeledLeafGraph G v
          (oneHighLeafFinFortyEquiv G hfree v branchLabel leafLabel)) := by
  classical
  obtain ⟨mate, branchLabel, twoEdges, leafLabel,
      hmateInv, hmateAdj, _haug, hbranchMate, hfamily, hword, hlabels⟩ :=
    orderFortyNine_exists_simultaneous_familyGeneratorLabels
      G hfree hmin hcard hHigh hv
  let profile := ((Finset.univ :
    Finset {z : V // z ∈ G.neighborSet v}).filter fun s =>
      highBranchMatchedCount G v s = 2).card
  let E := oneHighLeafFinFortyEquiv G hfree v branchLabel leafLabel
  let R := oneHighRelabeledLeafGraph G v E
  have hunique : ∀ {w : V}, G.degree w = 8 → w = v := by
    intro w hw
    have hvMem : v ∈ orderFortyNineHighVertices G := by
      simp [orderFortyNineHighVertices, hv]
    have hwMem : w ∈ orderFortyNineHighVertices G := by
      simp [orderFortyNineHighVertices, hw]
    obtain ⟨z, hz⟩ := Finset.card_eq_one.mp hHigh
    have hvz : v = z := by simpa [hz] using hvMem
    have hwz : w = z := by simpa [hz] using hwMem
    exact hwz.trans hvz.symm
  have hexternal : externalRepairCandidates G v = ∅ :=
    orderFortyNine_externalRepairCandidates_degreeEight_eq_empty
      G hfree hmin hcard hv
  have houterDegree : ∀ {x : V}, x ∈ secondLayer G v → G.degree x = 7 := by
    intro x hx
    rcases orderFortyNine_degree_eq_seven_or_eight
      G hfree hmin hcard x with hx7 | hx8
    · exact hx7
    · have hxv := hunique hx8
      rw [secondLayer] at hx
      rcases Finset.mem_biUnion.mp hx with ⟨s, _, hxs⟩
      exact ((Finset.mem_sdiff.mp hxs).2 (by simp [hxv])).elim
  have hprofile : profile ≤ 4 := by
    simpa [profile, oneHighAEndpointSet] using card_oneHighAEndpointSet_le_four
      G hfree hmin hcard hv hunique hexternal houterDegree
        mate hmateInv hmateAdj
  have hstates : ∀ i,
      highBranchMatchedCount G v (branchLabel.symm i) = 2 ∨
      highBranchMatchedCount G v (branchLabel.symm i) = 4 := by
    intro i
    rcases (hlabels (branchLabel.symm i)).1 with hs | hs
    · exact Or.inl hs.2
    · exact Or.inr hs.2
  have hIN : ∀ i, highBranchMatchedCount G v (branchLabel.symm i) =
      2 * oneHighFamilyInternalEdges profile i :=
    highBranchMatchedCount_eq_two_mul_familyInternalEdges
      G branchLabel profile hfamily hstates
  have hc : OneHighPureFamilyCnfConstraints profile R := by
    refine ⟨?_, ?_⟩
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro i j hij
        exact oneHighRelabeledLeafGraph_adj_eq_familyInternal
          G hfree branchLabel twoEdges leafLabel (fun s => (hlabels s).2.1)
            profile hword i j hij
      · intro i j hij
        exact oneHighRelabeledLeafGraph_not_adj_of_standardMate_blocks
          G hfree mate hmateAdj branchLabel hbranchMate leafLabel i j hij
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
          G hfree hexternal mate hmateAdj branchLabel hbranchMate twoEdges
            leafLabel (fun s => (hlabels s).2.1) profile hword i
            (houterDegree (E.symm i).2)
      · intro b
        have hledger := card_oneHighEncodedCommonPairBlock_add_familyIN_eq_thirty
          G hfree hmin hcard hv hunique hexternal houterDegree mate hmateInv
            hmateAdj branchLabel hbranchMate leafLabel profile hIN
            (branchLabel.symm b)
        simpa [R, E] using hledger
    · apply oneHighPureFamilyLexConstraints_of_generatorLabels
        G hfree hv hexternal houterDegree mate hmateAdj branchLabel hbranchMate
          twoEdges leafLabel (fun s => (hlabels s).2.1) profile hword
      intro s
      exact ⟨(hlabels s).2.2.1, (hlabels s).2.2.2⟩
  exact ⟨mate, branchLabel, leafLabel, profile, hmateInv, hmateAdj,
    hbranchMate, hprofile, hunique, hexternal, houterDegree, hc⟩

end Erdos85
