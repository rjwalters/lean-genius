import Proofs.Erdos85MuThreeAllTfSixteenCoordinates
import Proofs.Erdos85ExteriorPairGraphAdjacency

/-! # Internal common-neighbour geometry of a labeled sixteen-cycle -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- The coordinate difference predicate for distance two on `C16`. -/
def sixteenCycleOffsetTwo (i j : Fin 16) : Bool :=
  (j.val + 16 - i.val) % 16 == 2 ||
    (j.val + 16 - i.val) % 16 == 14

set_option maxRecDepth 100000 in
private theorem cycleGraph_sixteen_internalCommon_iff_offsetTwo :
    ∀ i j : Fin 16, i ≠ j →
      ((∃ k : Fin 16,
          (cycleGraph 16).Adj i k ∧ (cycleGraph 16).Adj j k) ↔
        sixteenCycleOffsetTwo i j) := by
  native_decide

/-- Two distinct vertices of a labeled spanning `C16` have an internal
common neighbour exactly when their cyclic coordinates differ by `±2`.
This is the fixed distance-two graph which complements the defect graph in
the exterior-pair relation. -/
theorem sixteenCycleLabeling_internalCommon_iff_offsetTwo
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (label : SixteenCycleLabeling H) :
    ∀ i j : Fin 16, i ≠ j →
      ((∃ z : V,
          H.Adj (label.toEquiv.symm i) z ∧
            H.Adj (label.toEquiv.symm j) z) ↔
        sixteenCycleOffsetTwo i j) := by
  intro i j hij
  rw [← cycleGraph_sixteen_internalCommon_iff_offsetTwo i j hij]
  constructor
  · rintro ⟨z, hiz, hjz⟩
    exact ⟨label.toEquiv z,
      by simpa using (label.map_adj_iff _ _).mp hiz,
      by simpa using (label.map_adj_iff _ _).mp hjz⟩
  · rintro ⟨k, hik, hjk⟩
    exact ⟨label.toEquiv.symm k,
      (label.map_adj_iff _ _).mpr (by simpa using hik),
      (label.map_adj_iff _ _).mpr (by simpa using hjk)⟩

/-- In connected `C16` coordinates the exterior-pair graph is exactly the
complement of the defect graph after deleting the fixed distance-two graph.
This identity is independent of the signed-joint eigenvalue. -/
theorem sixteenCycleLabeling_exteriorPair_adj_iff
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (label : SixteenCycleLabeling (G.induce c.supp)) :
    ∀ i j : Fin 16, i ≠ j →
      ((exteriorPairGraph G c.supp).Adj
          (label.toEquiv.symm i) (label.toEquiv.symm j) ↔
        ¬ (secondOrderDefectGraph G).Adj
            (label.toEquiv.symm i).1 (label.toEquiv.symm j).1 ∧
          ¬ sixteenCycleOffsetTwo i j) := by
  intro i j hij
  rw [exteriorPairGraph_adj_iff_not_defect_and_no_internal_common
    G hfree c]
  have hne : label.toEquiv.symm i ≠ label.toEquiv.symm j := by
    exact fun h ↦ hij (label.toEquiv.symm.injective h)
  have hcommon := sixteenCycleLabeling_internalCommon_iff_offsetTwo
    (G.induce c.supp) label i j hij
  simp only [SimpleGraph.induce_adj] at hcommon
  rw [hcommon]
  simp [hne]

end

end Erdos85

#print axioms Erdos85.sixteenCycleLabeling_internalCommon_iff_offsetTwo
#print axioms Erdos85.sixteenCycleLabeling_exteriorPair_adj_iff
