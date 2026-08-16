import Proofs.Erdos85MatchingPairingMultiplicity
import Proofs.Erdos85OneHighGraphPairingRefinement

/-! # Global multiplicity of the graph-induced one-high refinement -/

namespace Erdos85

noncomputable section

theorem oneHighPairingRefinementMultiplicity_eq_sum_count
    (refinement : List (List OneHighLabelPair)) (key : OneHighLabelPair) :
    oneHighPairingRefinementMultiplicity refinement key =
      (refinement.map fun pairs => pairs.count key).sum := by
  induction refinement with
  | nil => rfl
  | cons pairs refinement ih =>
      unfold oneHighPairingRefinementMultiplicity at ih ⊢
      simp only [List.flatten_cons, List.count_append, List.map_cons,
        List.sum_cons]
      rw [ih]

/-- Flattening the eight graph-induced local pairing lists counts exactly the
same unordered matching edges as the global sigma matching. -/
theorem oneHighGraphPairingRefinementMultiplicity_eq_global
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {v : V} (hv : G.degree v = 8)
    (p : OneHighRawV2Presentation G hfree v) (key : OneHighLabelPair)
    (hkey : key.1 < key.2) :
    oneHighPairingRefinementMultiplicity
        (oneHighGraphPairingRefinement G hfree hv p) key =
      exchangedMissPairMultiplicity
        (oneHighGlobalInternalMate G hfree v)
        (fun x => p.branchLabel
          (oneHighGlobalMissLabel G hfree hv p.external_empty p.outer_degree
            p.mate p.mate_adj x)) key := by
  classical
  let localMate := fun s : {z : V // z ∈ G.neighborSet v} =>
    oneHighInternalMate G hfree v s
  let localLabel := fun s : {z : V // z ∈ G.neighborSet v} =>
    fun x => p.branchLabel
      (oneHighMatchedMissLabel G hfree hv p.external_empty p.outer_degree
        p.mate p.mate_adj s x)
  have hlocalInv : ∀ s, Function.Involutive (localMate s) := by
    intro s
    exact degreeOneMate_involutive _ _
  have hlocalFree : ∀ s x, localMate s x ≠ x := by
    intro s x
    exact degreeOneMate_ne _ _ x
  have hsigma := sum_exchangedMissPairMultiplicity_eq_sigma
    localMate localLabel key hlocalInv hlocalFree hkey
  have hflatten :
      oneHighPairingRefinementMultiplicity
          (oneHighGraphPairingRefinement G hfree hv p) key =
        ∑ source : Fin 8,
          exchangedMissPairMultiplicity
            (localMate (p.branchLabel.symm source))
            (localLabel (p.branchLabel.symm source)) key := by
    rw [oneHighPairingRefinementMultiplicity_eq_sum_count]
    simp only [oneHighGraphPairingRefinement, List.map_ofFn, List.sum_ofFn]
    apply Finset.sum_congr rfl
    intro source _
    simpa [oneHighGraphSourcePairing, localMate, localLabel] using
      matchingPairingListSorted_count_eq_exchangedMissPairMultiplicity_of_lt
        (localMate (p.branchLabel.symm source))
        (localLabel (p.branchLabel.symm source)) key hkey
  rw [hflatten]
  have hreindex := p.branchLabel.symm.sum_comp (fun s =>
    exchangedMissPairMultiplicity (localMate s) (localLabel s) key)
  rw [hreindex]
  unfold oneHighGlobalInternalMate oneHighGlobalMissLabel
  simpa [localMate, localLabel] using hsigma

end

end Erdos85
