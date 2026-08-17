import Proofs.Erdos85BinarySquareCrossBlockResolution

/-! # Unique routing of cross-block Gram entries -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- The unique common neighbor of vertices in distinct defect components lies
in a unique intermediate defect component. -/
theorem existsUnique_component_existsUnique_commonNeighbor
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    {c e : (secondOrderDefectGraph G).ConnectedComponent}
    (hce : c ≠ e) (x : c.supp) (z : e.supp) :
    ∃! d : (secondOrderDefectGraph G).ConnectedComponent,
      ∃! y : d.supp, G.Adj x.1 y.1 ∧ G.Adj z.1 y.1 := by
  let D := secondOrderDefectGraph G
  obtain ⟨w, hw, hwuniq⟩ :=
    existsUnique_common_neighbor_of_mem_distinct_secondOrderDefect_components
      G hfree hce x z
  let d := D.connectedComponentMk w
  let wd : d.supp := ⟨w, ConnectedComponent.connectedComponentMk_mem⟩
  refine ⟨d, ?_, ?_⟩
  · refine ⟨wd, hw, ?_⟩
    intro y hy
    exact Subtype.ext (hwuniq y.1 hy)
  · intro d' hd'
    obtain ⟨y, hy, _hyuniq⟩ := hd'
    have hycomp : D.connectedComponentMk y.1 = d' :=
      (ConnectedComponent.mem_supp_iff d' y.1).mp y.2
    have hyw : y.1 = w := hwuniq y.1 hy
    calc
      d' = D.connectedComponentMk y.1 := hycomp.symm
      _ = D.connectedComponentMk w := congrArg D.connectedComponentMk hyw
      _ = d := rfl

/-- The defect component through which the unique common neighbor of `x,z`
is routed. -/
def crossIntermediateComponent
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    {c e : (secondOrderDefectGraph G).ConnectedComponent}
    (hce : c ≠ e) (x : c.supp) (z : e.supp) :
    (secondOrderDefectGraph G).ConnectedComponent :=
  Classical.choose
    (existsUnique_component_existsUnique_commonNeighbor G hfree hce x z)

/-- The routing component contains a unique common neighbor. -/
theorem crossIntermediateComponent_spec
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    {c e : (secondOrderDefectGraph G).ConnectedComponent}
    (hce : c ≠ e) (x : c.supp) (z : e.supp) :
    ∃! y : (crossIntermediateComponent G hfree hce x z).supp,
      G.Adj x.1 y.1 ∧ G.Adj z.1 y.1 :=
  (Classical.choose_spec
    (existsUnique_component_existsUnique_commonNeighbor G hfree hce x z)).1

private theorem transpose_cross_mul_cross_apply
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (d c e : (secondOrderDefectGraph G).ConnectedComponent)
    (x : c.supp) (z : e.supp) :
    ((defectComponentCrossIncidenceMatrix (K := ℤ) G d c).transpose *
        defectComponentCrossIncidenceMatrix (K := ℤ) G d e) x z =
      (((Finset.univ : Finset d.supp).filter fun y =>
        G.Adj x.1 y.1 ∧ G.Adj z.1 y.1).card : ℤ) := by
  rw [Matrix.mul_apply]
  simp only [Matrix.transpose_apply, defectComponentCrossIncidenceMatrix,
    defectComponentNeighborIncidenceMatrix, ite_mul, one_mul, zero_mul]
  calc
    (∑ y : d.supp,
      if G.Adj y.1 x.1 then if G.Adj y.1 z.1 then (1 : ℤ) else 0 else 0) =
        ∑ y : d.supp,
          if G.Adj x.1 y.1 ∧ G.Adj z.1 y.1 then (1 : ℤ) else 0 := by
      apply Finset.sum_congr rfl
      intro y _hy
      by_cases hxy : G.Adj x.1 y.1 <;>
        by_cases hzy : G.Adj z.1 y.1 <;> simp [hxy, hzy, adj_comm]
    _ = (((Finset.univ : Finset d.supp).filter fun y =>
        G.Adj x.1 y.1 ∧ G.Adj z.1 y.1).card : ℤ) := by
      rw [Finset.sum_boole]

/-- Each entry of the resolved Gram sum is routed to exactly one intermediate
component: its summand is one there and zero at every other component. -/
theorem transpose_cross_mul_cross_apply_eq_ite_intermediate
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    {c e : (secondOrderDefectGraph G).ConnectedComponent}
    (hce : c ≠ e) (x : c.supp) (z : e.supp)
    (d : (secondOrderDefectGraph G).ConnectedComponent) :
    ((defectComponentCrossIncidenceMatrix (K := ℤ) G d c).transpose *
        defectComponentCrossIncidenceMatrix (K := ℤ) G d e) x z =
      if d = crossIntermediateComponent G hfree hce x z then 1 else 0 := by
  rw [transpose_cross_mul_cross_apply]
  let r := crossIntermediateComponent G hfree hce x z
  obtain ⟨y, hy, hyuniq⟩ := crossIntermediateComponent_spec G hfree hce x z
  by_cases hdr : d = r
  · subst d
    rw [if_pos rfl]
    norm_cast
    apply Finset.card_eq_one.mpr
    refine ⟨y, ?_⟩
    ext w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    exact ⟨fun hw => hyuniq w hw, fun h => h ▸ hy⟩
  · rw [if_neg hdr]
    norm_cast
    apply Finset.card_eq_zero.mpr
    apply Finset.not_nonempty_iff_eq_empty.mp
    rintro ⟨w, hw⟩
    have hwdata := Finset.mem_filter.mp hw |>.2
    have hwy : w.1 = y.1 := by
      obtain ⟨u, hu, huuniq⟩ :=
        existsUnique_common_neighbor_of_mem_distinct_secondOrderDefect_components
          G hfree hce x z
      exact (huuniq w.1 hwdata).trans (huuniq y.1 hy).symm
    apply hdr
    have hwcomp : (secondOrderDefectGraph G).connectedComponentMk w.1 = d :=
      (ConnectedComponent.mem_supp_iff d w.1).mp w.2
    have hycomp : (secondOrderDefectGraph G).connectedComponentMk y.1 = r :=
      (ConnectedComponent.mem_supp_iff r y.1).mp y.2
    rw [← hwcomp, ← hycomp, hwy]

end

end Erdos85
