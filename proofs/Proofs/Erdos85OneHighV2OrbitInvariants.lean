import Proofs.Erdos85OneHighRawPresentation
import Proofs.Erdos85BranchDeficitSymmetry
import Proofs.Erdos85OneHighV2F3bRawLedger

/-! # Graph-derived invariants of raw one-high orbit tables -/

namespace Erdos85

open SimpleGraph

noncomputable section

/-- The directed miss matrix of a packaged one-high presentation is
symmetric.  This is the graph-side justification for storing only the
upper-triangular part of an orbit table. -/
theorem OneHighRawV2Presentation.missCount_comm
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) (v : V)
    (p : OneHighRawV2Presentation G hfree v)
    (s t : {z : V // z ∈ G.neighborSet v}) :
    highBranchMissCount G v s t = highBranchMissCount G v t s := by
  apply highBranchMissCount_comm_of_equal_card G hfree s t
  have hs := Fintype.card_congr (p.leafLabel s)
  have ht := Fintype.card_congr (p.leafLabel t)
  simpa using hs.trans ht.symm

/-- Every raw miss row has the profile-prescribed total.  The summation is
over the six branches other than the source and its canonical mate. -/
theorem OneHighRawV2Presentation.sum_far_missCount
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {v : V} (hv : G.degree v = 8)
    (p : OneHighRawV2Presentation G hfree v)
    (s : {z : V // z ∈ G.neighborSet v}) :
    (∑ u ∈ ((Finset.univ.erase s).erase (p.mate s)),
      highBranchMissCount G v s u) =
        2 * oneHighFamilyInternalEdges p.profile (p.branchLabel s) := by
  have houter : ∀ {a : V}, a ∈ secondLayerBranch G v s →
      G.degree a = 7 := by
    intro a ha
    apply p.outer_degree
    simp only [secondLayer, Finset.mem_biUnion]
    exact ⟨s, Finset.mem_univ s, ha⟩
  have hrow := sum_far_highBranchMissCount_eq_matchedCount
    G hfree (d := 7) (by simpa using hv) p.external_empty
      s (p.mate s) (p.mate_adj s) houter
  rw [hrow]
  simpa using p.matched_count (p.branchLabel s)

/-- Coordinate form of `sum_far_missCount`: the exact v2 table row indexed
by a branch label has the prescribed total. -/
theorem OneHighRawV2Presentation.graphTable_row_sum
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {v : V} (hv : G.degree v = 8)
    (p : OneHighRawV2Presentation G hfree v)
    (s : {z : V // z ∈ G.neighborSet v}) :
    let E := oneHighLeafFinFortyEquiv G hfree v p.branchLabel p.leafLabel
    let R := oneHighRelabeledLeafGraph G v E
    (∑ j ∈ ((Finset.univ.erase (p.branchLabel s)).erase
        (oneHighStandardMate (p.branchLabel s))),
      oneHighFamilyGraphTable R p.profile (p.branchLabel s).val j.val) =
        2 * oneHighFamilyInternalEdges p.profile (p.branchLabel s) := by
  intro E R
  let e : {z : V // z ∈ G.neighborSet v} ↪ Fin 8 := p.branchLabel.toEmbedding
  have hmap :
      (((Finset.univ.erase s).erase (p.mate s)).map e) =
        ((Finset.univ.erase (p.branchLabel s)).erase
          (oneHighStandardMate (p.branchLabel s))) := by
    ext j
    simp only [Finset.mem_map, Finset.mem_erase, Finset.mem_univ]
    constructor
    · rintro ⟨u, ⟨hum, hus, _⟩, rfl⟩
      refine ⟨?_, ?_, trivial⟩
      · intro h
        change p.branchLabel u = oneHighStandardMate (p.branchLabel s) at h
        apply hum
        apply p.branchLabel.injective
        simpa [p.branch_mate s] using h
      · exact fun h => hus (p.branchLabel.injective h)
    · rintro ⟨hjm, hjc, _⟩
      refine ⟨p.branchLabel.symm j, ⟨?_, ?_, trivial⟩, ?_⟩
      · intro h
        apply hjm
        rw [← p.branch_mate s, ← h]
        simp
      · intro h
        apply hjc
        rw [← h]
        simp
      · change p.branchLabel (p.branchLabel.symm j) = j
        simp
  rw [← hmap, Finset.sum_map]
  calc
    (∑ u ∈ (Finset.univ.erase s).erase (p.mate s),
      oneHighFamilyGraphTable R p.profile (p.branchLabel s).val
        (p.branchLabel u).val) =
        ∑ u ∈ (Finset.univ.erase s).erase (p.mate s),
          highBranchMissCount G v s u := by
      apply Finset.sum_congr rfl
      intro u hu
      have hus : u ≠ s := (Finset.mem_erase.mp
        (Finset.mem_erase.mp hu).2).1
      have hum : u ≠ p.mate s := (Finset.mem_erase.mp hu).1
      exact oneHighFamilyGraphTable_eq_highBranchMissCount
        G hfree v p.mate p.branchLabel p.branch_mate p.leafLabel p.profile
          p.constraints s u hus hum
    _ = 2 * oneHighFamilyInternalEdges p.profile (p.branchLabel s) :=
      p.sum_far_missCount G hfree hv s

end

end Erdos85
