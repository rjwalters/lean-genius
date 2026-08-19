import Proofs.Erdos85SizeTwoEigenlineCyclicPermutationReconstructionHits
import Proofs.Erdos85SizeTwoEigenlineCyclicMatchingDesign

/-!
# C4-freeness of the graph reconstructed from a full permutation code

The reciprocal subcode reconstructs the undirected graph and its hit laws.
The stronger cross-agreement field of `SizeTwoCyclicFullPermutationCode` is
exactly what rules out two common neighbours with arbitrary source
differences, hence rules out a four-cycle.
-/

namespace Erdos85

noncomputable section

theorem sizeTwoCyclicRawCell_mem_sourceMatching_of_adj
    (q : ℕ) [NeZero q] (a : ZMod q)
    (code : SizeTwoCyclicFullPermutationCode q a)
    (hloop : code.toReciprocalCode.Loopless)
    (u v : sizeTwoCyclicExteriorCell q a)
    (huv : (sizeTwoCyclicCodeGraph q a code.toReciprocalCode).Adj u v) :
    v.1 ∈ sizeTwoCyclicSourceMatching code
      (sizeTwoCyclicExteriorCellEquiv q a u) := by
  let source := sizeTwoCyclicExteriorCellEquiv q a u
  have hu : u = sizeTwoCyclicCellAt q a source.1 source.2 := by
    apply (sizeTwoCyclicExteriorCellEquiv q a).injective
    simp [source]
  rw [hu, sizeTwoCyclicCodeGraph_adj_cellAt_iff
    q a code.toReciprocalCode hloop] at huv
  obtain ⟨r, rfl⟩ := huv
  rw [sizeTwoCyclicSourceMatching_mem_iff]
  refine ⟨r, ?_⟩
  apply Prod.ext
  · simp [sizeTwoCyclicMatchingEdge, source]
  · simp only [sizeTwoCyclicMatchingEdge, sizeTwoCyclicCellAt_snd]
    rw [← code.toReciprocalCode.target_column_eq source.1 source.2 r]
    abel

/-- A full cyclic permutation code reconstructs a C4-free graph. -/
theorem sizeTwoCyclicFullCodeGraph_not_containsC4
    (q : ℕ) [NeZero q] (a : ZMod q)
    (code : SizeTwoCyclicFullPermutationCode q a)
    (hloop : code.toReciprocalCode.Loopless) :
    ¬ containsC4 (sizeTwoCyclicExteriorCell q a)
      (sizeTwoCyclicCodeGraph q a code.toReciprocalCode) := by
  intro hc
  obtain ⟨u, w, v, v', huw, hvv', hvu, hvw, hv'u, hv'w⟩ :=
    exists_two_common_of_containsC4 hc
  let source₁ := sizeTwoCyclicExteriorCellEquiv q a u
  let source₂ := sizeTwoCyclicExteriorCellEquiv q a w
  have hsources : source₁ ≠ source₂ := by
    intro h
    apply huw
    exact (sizeTwoCyclicExteriorCellEquiv q a).injective h
  have hv₁ : v.1 ∈ sizeTwoCyclicSourceMatching code source₁ := by
    exact sizeTwoCyclicRawCell_mem_sourceMatching_of_adj
      q a code hloop u v hvu.symm
  have hv₂ : v.1 ∈ sizeTwoCyclicSourceMatching code source₂ := by
    exact sizeTwoCyclicRawCell_mem_sourceMatching_of_adj
      q a code hloop w v hvw.symm
  have hv'₁ : v'.1 ∈ sizeTwoCyclicSourceMatching code source₁ := by
    exact sizeTwoCyclicRawCell_mem_sourceMatching_of_adj
      q a code hloop u v' hv'u.symm
  have hv'₂ : v'.1 ∈ sizeTwoCyclicSourceMatching code source₂ := by
    exact sizeTwoCyclicRawCell_mem_sourceMatching_of_adj
      q a code hloop w v' hv'w.symm
  have htwo : 1 < (sizeTwoCyclicSourceMatching code source₁ ∩
      sizeTwoCyclicSourceMatching code source₂).card := by
    apply Finset.one_lt_card.mpr
    refine ⟨v.1, Finset.mem_inter.mpr ⟨hv₁, hv₂⟩,
      v'.1, Finset.mem_inter.mpr ⟨hv'₁, hv'₂⟩, ?_⟩
    intro h
    apply hvv'
    exact Subtype.ext h
  have hone := sizeTwoCyclicSourceMatching_inter_card_le_one
    code source₁ source₂ hsources
  omega

end

end Erdos85

#print axioms Erdos85.sizeTwoCyclicRawCell_mem_sourceMatching_of_adj
#print axioms Erdos85.sizeTwoCyclicFullCodeGraph_not_containsC4
