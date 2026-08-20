import Proofs.Erdos85SixteenCycleInternalCommonPairs

/-! # Matrix decomposition in connected C16 coordinates -/

open Finset SimpleGraph Matrix

namespace Erdos85

noncomputable section

/-- Defect adjacency in a labeled connected `C16`. -/
def connectedC16DefectMatrix
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (label : SixteenCycleLabeling (G.induce c.supp)) :
    Matrix (Fin 16) (Fin 16) ℤ :=
  fun i j ↦ (secondOrderDefectGraph G).adjMatrix ℤ
    (label.toEquiv.symm i).1 (label.toEquiv.symm j).1

/-- Exterior-pair adjacency in the same coordinates. -/
def connectedC16ExteriorMatrix
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (label : SixteenCycleLabeling (G.induce c.supp)) :
    Matrix (Fin 16) (Fin 16) ℤ :=
  fun i j ↦ (exteriorPairGraph G c.supp).adjMatrix ℤ
    (label.toEquiv.symm i) (label.toEquiv.symm j)

/-- The fixed distance-two adjacency matrix of `C16`. -/
def connectedC16DistanceTwoMatrix : Matrix (Fin 16) (Fin 16) ℤ :=
  fun i j ↦ if sixteenCycleOffsetTwo i j then 1 else 0

/-- Pointwise algebraic form of the connected geometry:
`K + R + C16²_offdiag = J - I`.  Thus the unknown defect and exterior
matrices partition the complement of the fixed distance-two graph. -/
theorem connectedC16_defect_add_exterior_add_distanceTwo
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (label : SixteenCycleLabeling (G.induce c.supp)) :
    ∀ i j,
      connectedC16DefectMatrix G c label i j +
          connectedC16ExteriorMatrix G c label i j +
          connectedC16DistanceTwoMatrix i j =
        if i = j then 0 else 1 := by
  classical
  intro i j
  by_cases hij : i = j
  · subst j
    simp [connectedC16DefectMatrix, connectedC16ExteriorMatrix,
      connectedC16DistanceTwoMatrix, sixteenCycleOffsetTwo]
  have hcommon := sixteenCycleLabeling_internalCommon_iff_offsetTwo
    (G.induce c.supp) label i j hij
  simp only [SimpleGraph.induce_adj] at hcommon
  have hrel := sixteenCycleLabeling_exteriorPair_adj_iff
    G hfree c label i j hij
  let x := (label.toEquiv.symm i).1
  let y := (label.toEquiv.symm j).1
  have hxy : x ≠ y := by
    intro h
    apply hij
    apply label.toEquiv.symm.injective
    exact Subtype.ext h
  have hdisj : (secondOrderDefectGraph G).Adj x y →
      ¬ sixteenCycleOffsetTwo i j := by
    intro hD hoff
    obtain ⟨z, hxz, hyz⟩ := hcommon.mpr hoff
    have hzero :=
      (secondOrderDefectGraph_adj_iff_card_common_eq_zero G hfree hxy).mp hD
    have hzmem : z.1 ∈ G.neighborFinset x ∩ G.neighborFinset y := by
      simp only [Finset.mem_inter, mem_neighborFinset]
      exact ⟨hxz, hyz⟩
    have hempty : G.neighborFinset x ∩ G.neighborFinset y = ∅ :=
      Finset.card_eq_zero.mp hzero
    rw [hempty] at hzmem
    exact Finset.notMem_empty _ hzmem
  by_cases hD : (secondOrderDefectGraph G).Adj x y
  · have hoff := hdisj hD
    have hR : ¬ (exteriorPairGraph G c.supp).Adj
        (label.toEquiv.symm i) (label.toEquiv.symm j) := by
      intro hR
      exact (hrel.mp hR).1 hD
    simp [connectedC16DefectMatrix, connectedC16ExteriorMatrix,
      connectedC16DistanceTwoMatrix, SimpleGraph.adjMatrix_apply,
      x, y, hD, hR, hoff, hij]
  · by_cases hoff : sixteenCycleOffsetTwo i j
    · have hR : ¬ (exteriorPairGraph G c.supp).Adj
          (label.toEquiv.symm i) (label.toEquiv.symm j) := by
        intro hR
        exact (hrel.mp hR).2 hoff
      simp [connectedC16DefectMatrix, connectedC16ExteriorMatrix,
        connectedC16DistanceTwoMatrix, SimpleGraph.adjMatrix_apply,
        x, y, hD, hR, hoff, hij]
    · have hR : (exteriorPairGraph G c.supp).Adj
          (label.toEquiv.symm i) (label.toEquiv.symm j) :=
        hrel.mpr ⟨hD, hoff⟩
      simp [connectedC16DefectMatrix, connectedC16ExteriorMatrix,
        connectedC16DistanceTwoMatrix, SimpleGraph.adjMatrix_apply,
        x, y, hD, hR, hoff, hij]

end

end Erdos85

#print axioms Erdos85.connectedC16_defect_add_exterior_add_distanceTwo
