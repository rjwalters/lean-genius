import Proofs.Erdos85ExcessDefectRegular

/-! # Common neighbors across second-order defect components -/

open SimpleGraph

namespace Erdos85

/-- Vertices in distinct connected components of the second-order defect
graph have exactly one common neighbor in the original C4-free graph. -/
theorem card_common_eq_one_of_mem_distinct_secondOrderDefect_components
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    {c e : (secondOrderDefectGraph G).ConnectedComponent}
    (hce : c ≠ e) (x : c.supp) (y : e.supp) :
    (G.neighborFinset x.1 ∩ G.neighborFinset y.1).card = 1 := by
  let D := secondOrderDefectGraph G
  have hxc : D.connectedComponentMk x.1 = c :=
    (ConnectedComponent.mem_supp_iff c x.1).mp x.2
  have hye : D.connectedComponentMk y.1 = e :=
    (ConnectedComponent.mem_supp_iff e y.1).mp y.2
  have hxy : x.1 ≠ y.1 := by
    intro h
    apply hce
    rw [← hxc, ← hye, h]
  have hnotAdj : ¬ D.Adj x.1 y.1 := by
    intro hAdj
    apply hce
    rw [← hxc, ← hye]
    exact ConnectedComponent.connectedComponentMk_eq_of_adj hAdj
  rw [card_common_eq_if_secondOrderDefect G hfree x.1 y.1 hxy]
  simp [D, hnotAdj]

end Erdos85
