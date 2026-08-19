import Proofs.Erdos85OrderSixtyFourOutsideEdgeBijection
import Proofs.Erdos85DegreeSixMinimumSectorTerminal
import Proofs.Erdos85ExteriorDefectDecomposition

/-!
# A structural adjacency criterion for the exterior-pair graph

Node: `SIZE-TWO-EIGENLINE(8)` beneath outline F.3.

This turns an explicit internal `G`/defect block into an explicit graph of
the unordered pairs owned by exterior vertices.  It is the graph-facing
bridge needed to reuse the exterior hit machinery beyond the all-TF sector.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Two internal vertices own an exterior common neighbor exactly when they
are a non-defect pair and have no common neighbor inside the component. -/
theorem exteriorPairGraph_adj_iff_not_defect_and_no_internal_common
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (x y : c.supp) :
    (exteriorPairGraph G c.supp).Adj x y ↔
      x ≠ y ∧ ¬ (secondOrderDefectGraph G).Adj x.1 y.1 ∧
        ¬ ∃ z : c.supp, G.Adj x.1 z.1 ∧ G.Adj y.1 z.1 := by
  constructor
  · rintro ⟨hxy, z, hzout, hxz, hyz⟩
    refine ⟨hxy, ?_, ?_⟩
    · intro hD
      have hzero :=
        (secondOrderDefectGraph_adj_iff_card_common_eq_zero G hfree
          (fun h => hxy (Subtype.ext h))).mp hD
      have hzmem : z ∈ G.neighborFinset x.1 ∩ G.neighborFinset y.1 := by
        rw [Finset.mem_inter, mem_neighborFinset, mem_neighborFinset]
        exact ⟨hxz, hyz⟩
      rw [Finset.card_eq_zero] at hzero
      rw [hzero] at hzmem
      exact Finset.notMem_empty z hzmem
    · rintro ⟨w, hxw, hyw⟩
      have hzw : z ≠ w.1 := by
        intro h
        apply hzout
        rw [h]
        exact w.2
      exact hfree (containsC4_of_two_common
        (fun h => hxy (Subtype.ext h)) hzw
        hxz.symm hyz.symm hxw.symm hyw.symm)
  · rintro ⟨hxy, hnotD, hnoInternal⟩
    have hone := card_common_eq_one_of_not_defectAdj G hfree
      (fun h => hxy (Subtype.ext h)) hnotD
    have hpos : 0 < (G.neighborFinset x.1 ∩ G.neighborFinset y.1).card := by
      omega
    obtain ⟨z, hz⟩ := Finset.card_pos.mp hpos
    have hzAdj : G.Adj x.1 z ∧ G.Adj y.1 z := by
      rw [Finset.mem_inter, mem_neighborFinset, mem_neighborFinset] at hz
      exact hz
    have hzout : z ∉ c.supp := by
      intro hzin
      exact hnoInternal ⟨⟨z, hzin⟩, hzAdj⟩
    exact ⟨hxy, z, hzout, hzAdj⟩

end

end Erdos85

#print axioms Erdos85.exteriorPairGraph_adj_iff_not_defect_and_no_internal_common
