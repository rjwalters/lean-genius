import Proofs.Erdos85BinarySquareRegularParity

/-!
# Unique cross-coordinate selector incidence

Points in two distinct defect components have a unique common ambient owner.
Equivalently, the rectangles supplied by ambient component selectors partition
the cross-product of any two defect components.  In the all-size-two branch
this is the shared-indexing constraint coupling the complement graphs `L_c`.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Every pair of points in distinct defect components belongs to the
selectors of a unique ambient vertex. -/
theorem existsUnique_mem_cross_componentNeighborFinsets
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (c d : (secondOrderDefectGraph G).ConnectedComponent) (hcd : c ≠ d)
    (u : c.supp) (v : d.supp) :
    ∃! x : V,
      u.1 ∈ componentNeighborFinset G (secondOrderDefectGraph G) c x ∧
      v.1 ∈ componentNeighborFinset G (secondOrderDefectGraph G) d x := by
  let D := secondOrderDefectGraph G
  have huc : D.connectedComponentMk u.1 = c :=
    (SimpleGraph.ConnectedComponent.mem_supp_iff c u.1).mp u.2
  have hvd : D.connectedComponentMk v.1 = d :=
    (SimpleGraph.ConnectedComponent.mem_supp_iff d v.1).mp v.2
  have huv : u.1 ≠ v.1 := by
    intro huv
    apply hcd
    calc
      c = D.connectedComponentMk u.1 := huc.symm
      _ = D.connectedComponentMk v.1 := by rw [huv]
      _ = d := hvd
  have hnotD : ¬D.Adj u.1 v.1 := by
    intro hadj
    have hcomp : D.connectedComponentMk u.1 = D.connectedComponentMk v.1 :=
      SimpleGraph.ConnectedComponent.sound hadj.reachable
    exact hcd (huc.symm.trans (hcomp.trans hvd))
  have hnotMem : v.1 ∉ D.neighborFinset u.1 := by
    simpa [SimpleGraph.mem_neighborFinset] using hnotD
  have hcommon := card_common_eq_if_secondOrderDefect G hfree u.1 v.1 huv
  rw [if_neg hnotMem] at hcommon
  obtain ⟨x, hxsingleton⟩ := Finset.card_eq_one.mp hcommon
  have hxcommon : x ∈ G.neighborFinset u.1 ∩ G.neighborFinset v.1 := by
    rw [hxsingleton]
    simp
  have hxdata := Finset.mem_inter.mp hxcommon
  have hxselectors :
      u.1 ∈ componentNeighborFinset G D c x ∧
      v.1 ∈ componentNeighborFinset G D d x := by
    constructor
    · rw [componentNeighborFinset]
      exact Finset.mem_filter.mpr
        ⟨(G.mem_neighborFinset x u.1).mpr
            ((G.mem_neighborFinset u.1 x).mp hxdata.1).symm,
          huc⟩
    · rw [componentNeighborFinset]
      exact Finset.mem_filter.mpr
        ⟨(G.mem_neighborFinset x v.1).mpr
            ((G.mem_neighborFinset v.1 x).mp hxdata.2).symm,
          hvd⟩
  refine ⟨x, hxselectors, ?_⟩
  intro y hy
  have hyu : y ∈ G.neighborFinset u.1 := by
    have hydata := Finset.mem_filter.mp hy.1
    exact (G.mem_neighborFinset u.1 y).mpr
      ((G.mem_neighborFinset y u.1).mp hydata.1).symm
  have hyv : y ∈ G.neighborFinset v.1 := by
    have hydata := Finset.mem_filter.mp hy.2
    exact (G.mem_neighborFinset v.1 y).mpr
      ((G.mem_neighborFinset y v.1).mp hydata.1).symm
  have hycommon : y ∈ G.neighborFinset u.1 ∩ G.neighborFinset v.1 :=
    Finset.mem_inter.mpr ⟨hyu, hyv⟩
  rw [hxsingleton] at hycommon
  simpa using hycommon

end

end Erdos85
