import Proofs.Erdos85CrossDefectComponentCommonNeighbor

/-! # Routing common neighbors across a defect-component cut -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- A vertex in a defect component and a vertex outside it have one common
neighbor, and the inside/outside pieces of that singleton partition have
total cardinality one.  This is the pointwise combinatorial content of the
cross-block equation `H B + B C = J`. -/
theorem card_insideCommon_add_card_outsideCommon_eq_one
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (u : c.supp) (z : V) (hz : z ∉ c.supp) :
    (((G.neighborFinset u.1 ∩ G.neighborFinset z).filter
        fun w ↦ w ∈ c.supp).card +
      ((G.neighborFinset u.1 ∩ G.neighborFinset z).filter
        fun w ↦ w ∉ c.supp).card) = 1 := by
  classical
  let D := secondOrderDefectGraph G
  let e := D.connectedComponentMk z
  have hce : c ≠ e := by
    intro h
    apply hz
    apply (ConnectedComponent.mem_supp_iff c z).mpr
    exact h.symm
  let ze : e.supp := ⟨z, (ConnectedComponent.mem_supp_iff e z).mpr rfl⟩
  have htotal :=
    card_common_eq_one_of_mem_distinct_secondOrderDefect_components
      G hfree hce u ze
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := G.neighborFinset u.1 ∩ G.neighborFinset z)
    (fun w ↦ w ∈ c.supp)
  rw [htotal] at hsplit
  exact hsplit

/-- Equivalently, the unique common neighbor of an inside vertex `u` and an
outside vertex `z` is routed to exactly one side of the cut. -/
theorem existsUnique_insideCommon_or_existsUnique_outsideCommon
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (u : c.supp) (z : V) (hz : z ∉ c.supp) :
    (∃! w : c.supp, G.Adj u.1 w.1 ∧ G.Adj z w.1) ∨
      (∃! y : {x : V // x ∉ c.supp},
        G.Adj u.1 y.1 ∧ G.Adj z y.1) := by
  classical
  let D := secondOrderDefectGraph G
  let e := D.connectedComponentMk z
  have hce : c ≠ e := by
    intro h
    apply hz
    apply (ConnectedComponent.mem_supp_iff c z).mpr
    exact h.symm
  let ze : e.supp := ⟨z, (ConnectedComponent.mem_supp_iff e z).mpr rfl⟩
  obtain ⟨w, hw, hwuniq⟩ :=
    existsUnique_common_neighbor_of_mem_distinct_secondOrderDefect_components
      G hfree hce u ze
  by_cases hwin : w ∈ c.supp
  · left
    refine ⟨⟨w, hwin⟩, hw, ?_⟩
    intro w' hw'
    apply Subtype.ext
    exact hwuniq w'.1 hw'
  · right
    refine ⟨⟨w, hwin⟩, hw, ?_⟩
    intro y hy
    apply Subtype.ext
    exact hwuniq y.1 hy

/-- If no inside common neighbor exists, the outside service vertex exists
uniquely.  For an outside vertex viewed as an edge of the exterior-pair
graph, these unique service vertices are the endpoints supplied by its six
neighbors in the outside graph. -/
theorem existsUnique_outsideCommon_of_no_insideCommon
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (u : c.supp) (z : V) (hz : z ∉ c.supp)
    (hno : ¬∃ w : c.supp, G.Adj u.1 w.1 ∧ G.Adj z w.1) :
    ∃! y : {x : V // x ∉ c.supp},
      G.Adj u.1 y.1 ∧ G.Adj z y.1 := by
  rcases existsUnique_insideCommon_or_existsUnique_outsideCommon
      G hfree c u z hz with hin | hout
  · rcases hin with ⟨w, hw, _huniq⟩
    exact False.elim (hno ⟨w, hw⟩)
  · exact hout

/-- Conversely, an inside common neighbor excludes every outside service
vertex. -/
theorem not_exists_outsideCommon_of_exists_insideCommon
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (u : c.supp) (z : V) (hz : z ∉ c.supp)
    (hin : ∃ w : c.supp, G.Adj u.1 w.1 ∧ G.Adj z w.1) :
    ¬∃ y : {x : V // x ∉ c.supp},
      G.Adj u.1 y.1 ∧ G.Adj z y.1 := by
  rintro ⟨y, hy⟩
  obtain ⟨w, hw⟩ := hin
  have hwy : w.1 = y.1 := by
    let D := secondOrderDefectGraph G
    let e := D.connectedComponentMk z
    have hce : c ≠ e := by
      intro h
      apply hz
      apply (ConnectedComponent.mem_supp_iff c z).mpr
      exact h.symm
    let ze : e.supp := ⟨z, (ConnectedComponent.mem_supp_iff e z).mpr rfl⟩
    obtain ⟨_x, _hx, huniq⟩ :=
      existsUnique_common_neighbor_of_mem_distinct_secondOrderDefect_components
        G hfree hce u ze
    exact (huniq w.1 hw).trans (huniq y.1 hy).symm
  exact y.2 (hwy ▸ w.2)

end

end Erdos85
