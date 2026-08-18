import Proofs.Erdos85BinarySquareRegularParity

/-!
# Order-16 exterior-component fibers in the order-64 grid

The regular square-order equitable law immediately says that every vertex
has exactly two ambient neighbours in each order-16 defect component.  In
the μ=3 grid coordinates, vertices of the distinguished component are the
row and column labels, so this is the exact two-cells-per-fiber input for the
`[2,2,2,2]` stratum.
-/

open SimpleGraph

namespace Erdos85

/-- At order 64 and degree 8, every vertex has exactly two neighbours in an
order-16 defect component. -/
theorem orderSixtyFour_regular_componentNeighbor_card_eq_two
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (hreg : ∀ x, G.degree x = 8)
    (hcard : Fintype.card V = 64)
    (e c : (secondOrderDefectGraph G).ConnectedComponent)
    (hc : c.supp.ncard = 16) {x : V} (hx : x ∈ e.supp) :
    (componentNeighborFinset G (secondOrderDefectGraph G) c x).card = 2 := by
  have h := binarySquare_regular_mul_componentNeighborCard_eq_componentCard
    G hfree (q := 8) (by omega) hreg (by omega) e c hx
  rw [hc] at h
  omega

/-- Defect adjacency cannot leave a connected component. -/
theorem secondOrderDefectGraph_adj_mem_component
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    {x y : V} (hx : x ∈ c.supp)
    (hxy : (secondOrderDefectGraph G).Adj x y) : y ∈ c.supp := by
  rw [ConnectedComponent.mem_supp_iff] at hx ⊢
  exact (ConnectedComponent.connectedComponentMk_eq_of_adj hxy).symm.trans hx

end Erdos85

#print axioms Erdos85.orderSixtyFour_regular_componentNeighbor_card_eq_two
#print axioms Erdos85.secondOrderDefectGraph_adj_mem_component
