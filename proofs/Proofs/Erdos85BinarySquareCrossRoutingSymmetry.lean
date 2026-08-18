import Proofs.Erdos85BinarySquareCrossBlockUniqueRouting

/-! # Endpoint-reversal symmetry of cross-component routing -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Swapping the two endpoints does not change the defect component containing
their unique common neighbor. -/
theorem crossIntermediateComponent_reverse
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    {c e : (secondOrderDefectGraph G).ConnectedComponent}
    (hce : c ≠ e) (x : c.supp) (z : e.supp) :
    crossIntermediateComponent G hfree hce x z =
      crossIntermediateComponent G hfree hce.symm z x := by
  let r := crossIntermediateComponent G hfree hce x z
  let s := crossIntermediateComponent G hfree hce.symm z x
  have hr : ∃! y : r.supp, G.Adj z.1 y.1 ∧ G.Adj x.1 y.1 := by
    obtain ⟨y, hy, hyuniq⟩ :=
      crossIntermediateComponent_spec G hfree hce x z
    refine ⟨y, ⟨hy.2, hy.1⟩, ?_⟩
    intro w hw
    exact hyuniq w ⟨hw.2, hw.1⟩
  have hs : ∃! y : s.supp, G.Adj z.1 y.1 ∧ G.Adj x.1 y.1 :=
    crossIntermediateComponent_spec G hfree hce.symm z x
  exact (existsUnique_component_existsUnique_commonNeighbor
    G hfree hce.symm z x).unique hr hs

/-- The relation selecting one intermediate routing color is transposed by
endpoint reversal. -/
theorem eq_crossIntermediateComponent_iff_reverse
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    {c e : (secondOrderDefectGraph G).ConnectedComponent}
    (hce : c ≠ e) (x : c.supp) (z : e.supp)
    (d : (secondOrderDefectGraph G).ConnectedComponent) :
    d = crossIntermediateComponent G hfree hce x z ↔
      d = crossIntermediateComponent G hfree hce.symm z x := by
  rw [crossIntermediateComponent_reverse G hfree hce x z]

/-- The zero-one matrix of endpoint pairs routed through `d`. -/
def crossRoutingColorMatrix
    {K V : Type*} [Fintype V] [DecidableEq V] [Zero K] [One K]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    {c e : (secondOrderDefectGraph G).ConnectedComponent}
    (hce : c ≠ e)
    (d : (secondOrderDefectGraph G).ConnectedComponent) :
    Matrix c.supp e.supp K :=
  fun x z => if d = crossIntermediateComponent G hfree hce x z then 1 else 0

/-- Every routing-color matrix for the reversed endpoint pair is the transpose
of the original routing-color matrix. -/
theorem crossRoutingColorMatrix_transpose
    {K V : Type*} [Fintype V] [DecidableEq V] [Zero K] [One K]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    {c e : (secondOrderDefectGraph G).ConnectedComponent}
    (hce : c ≠ e)
    (d : (secondOrderDefectGraph G).ConnectedComponent) :
    (crossRoutingColorMatrix (K := K) G hfree hce d).transpose =
      crossRoutingColorMatrix (K := K) G hfree hce.symm d := by
  ext z x
  simp only [Matrix.transpose_apply, crossRoutingColorMatrix]
  rw [crossIntermediateComponent_reverse G hfree hce x z]

/-- The Gram summand through `d` is exactly its routing-color matrix. -/
theorem transpose_cross_mul_cross_eq_routingColorMatrix
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    {c e : (secondOrderDefectGraph G).ConnectedComponent}
    (hce : c ≠ e)
    (d : (secondOrderDefectGraph G).ConnectedComponent) :
    (defectComponentCrossIncidenceMatrix (K := ℤ) G d c).transpose *
        defectComponentCrossIncidenceMatrix (K := ℤ) G d e =
      crossRoutingColorMatrix (K := ℤ) G hfree hce d := by
  ext x z
  exact transpose_cross_mul_cross_apply_eq_ite_intermediate
    G hfree hce x z d

end

end Erdos85
