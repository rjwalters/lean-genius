import Proofs.Erdos85MatchingPairingRefinement
import Proofs.Erdos85OneHighGraphMissLabelCounting
import Proofs.Erdos85OneHighRawPresentation
import Proofs.Erdos85OneHighV2F3bRawLedger

/-! # The pairing refinement induced by a raw one-high graph -/

namespace Erdos85

noncomputable section

open SimpleGraph

/-- In a far target column, the fiber of the unique miss-label function on
matched vertices is exactly the directed graph miss count.  The reverse
direction uses dirty conservation: a vertex missing a far branch has positive
internal degree, hence degree one in its C4-free source branch. -/
theorem card_oneHighMatchedMissLabelFiber_eq_highBranchMissCount
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {v : V}
    (hv : G.degree v = 8)
    (hexternal : externalRepairCandidates G v = ∅)
    (houterDegree : ∀ {a : V}, a ∈ secondLayer G v → G.degree a = 7)
    (rootMate : {z : V // z ∈ G.neighborSet v} →
      {z : V // z ∈ G.neighborSet v})
    (hrootAdj : ∀ s, G.Adj s.1 (rootMate s).1)
    (s u : {z : V // z ∈ G.neighborSet v})
    (hu : u ∈ ((Finset.univ.erase s).erase (rootMate s))) :
    (matchingLabelFiber
      (oneHighMatchedMissLabel G hfree hv hexternal houterDegree
        rootMate hrootAdj s) u).card =
      highBranchMissCount G v s u := by
  classical
  let X := OneHighMatchedBranchVertices G v s
  let label : X → {z : V // z ∈ G.neighborSet v} :=
    oneHighMatchedMissLabel G hfree hv hexternal houterDegree
      rootMate hrootAdj s
  let M := (secondLayerBranch G v s).filter fun a =>
    (G.neighborFinset a ∩ secondLayerBranch G v u).card = 0
  change (matchingLabelFiber label u).card = M.card
  apply Finset.card_bij (fun x _ => x.1.1)
  · intro x hx
    have hxLabel : label x = u := (Finset.mem_filter.mp hx).2
    have hxMatched : (G.neighborFinset x.1.1 ∩
        secondLayerBranch G v s).card = 1 := by
      rw [← degree_induce_secondLayerBranch_eq_card_inter]
      exact x.2
    have hmem := oneHighMissingBranch_mem_of_matched
      G hfree hv hexternal houterDegree rootMate hrootAdj s
        x.1.1 x.1.2 hxMatched
    have hmiss := (Finset.mem_filter.mp hmem).2
    have hxLabel' : oneHighMissingBranch G v rootMate s x.1.1 = u := by
      simpa [label, oneHighMatchedMissLabel] using hxLabel
    rw [hxLabel'] at hmiss
    apply Finset.mem_filter.mpr
    exact ⟨x.1.2, hmiss⟩
  · intro x _ y _ hxy
    exact Subtype.ext (Subtype.ext hxy)
  · intro a ha
    have haParts := Finset.mem_filter.mp ha
    have haSecond : a ∈ secondLayer G v := by
      rw [secondLayer]
      exact Finset.mem_biUnion.mpr ⟨s, Finset.mem_univ _, haParts.1⟩
    have hfarCard := card_farBranch_misses_eq_internalDegree
      G hfree (d := 7) (by omega) hexternal s (rootMate s)
        (hrootAdj s) a haParts.1 (houterDegree haSecond)
    have huMem : u ∈
        (((Finset.univ.erase s).erase (rootMate s)).filter fun w =>
          (G.neighborFinset a ∩ secondLayerBranch G v w).card = 0) :=
      Finset.mem_filter.mpr ⟨hu, haParts.2⟩
    have hpos : 0 < (G.neighborFinset a ∩
        secondLayerBranch G v s).card := by
      have : 0 < ((((Finset.univ.erase s).erase (rootMate s)).filter fun w =>
          (G.neighborFinset a ∩ secondLayerBranch G v w).card = 0).card) :=
        Finset.card_pos.mpr ⟨u, huMem⟩
      omega
    have hle := degree_induce_secondLayerBranch_le_one G hfree v s ⟨a, haParts.1⟩
    rw [degree_induce_secondLayerBranch_eq_card_inter] at hle
    have hle' : (G.neighborFinset a ∩
        secondLayerBranch G v s).card ≤ 1 := by
      simpa using hle
    have haMatched : (G.neighborFinset a ∩
        secondLayerBranch G v s).card = 1 := by omega
    let x : X := ⟨⟨a, haParts.1⟩, by
      rw [degree_induce_secondLayerBranch_eq_card_inter]
      exact haMatched⟩
    have heq := eq_oneHighMissingBranch_of_matched_of_mem
      G hfree hv hexternal houterDegree rootMate hrootAdj s
        a haParts.1 haMatched u
        (Finset.mem_filter.mpr ⟨hu, haParts.2⟩)
    refine ⟨x, ?_, rfl⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    simpa [label, x, oneHighMatchedMissLabel] using heq.symm

end

end Erdos85
