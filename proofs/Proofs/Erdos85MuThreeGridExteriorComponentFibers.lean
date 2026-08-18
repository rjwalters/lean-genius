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

noncomputable section

/-- The cells of defect component `c` lying in coordinate row `x`. -/
def defectComponentCoordinateRowFiber
    {V X Y : Type*} [Fintype V] [DecidableEq V] [DecidableEq X]
    (D : SimpleGraph V) [DecidableEq D.ConnectedComponent]
    (φ : V ≃ X × Y) (c : D.ConnectedComponent) (x : X) : Finset V :=
  Finset.univ.filter fun z => D.connectedComponentMk z = c ∧ (φ z).1 = x

/-- Ordered defect edges of component `c` between two coordinate rows. -/
def defectComponentCoordinateRowPairs
    {V X Y : Type*} [Fintype V] [DecidableEq V] [DecidableEq X]
    (D : SimpleGraph V) [DecidableRel D.Adj]
    [DecidableEq D.ConnectedComponent]
    (φ : V ≃ X × Y) (c : D.ConnectedComponent) (x x' : X) :
    Finset (V × V) :=
  ((defectComponentCoordinateRowFiber D φ c x).product
    (defectComponentCoordinateRowFiber D φ c x')).filter
      fun p => D.Adj p.1 p.2

/-- Two cells in each of two rows give capacity at most four for the
component's ordered cross-row defect pairs. -/
theorem defectComponentCoordinateRowPairs_card_le_four
    {V X Y : Type*} [Fintype V] [DecidableEq V] [DecidableEq X]
    (D : SimpleGraph V) [DecidableRel D.Adj]
    [DecidableEq D.ConnectedComponent]
    (φ : V ≃ X × Y) (c : D.ConnectedComponent) (x x' : X)
    (hx : (defectComponentCoordinateRowFiber D φ c x).card = 2)
    (hx' : (defectComponentCoordinateRowFiber D φ c x').card = 2) :
    (defectComponentCoordinateRowPairs D φ c x x').card ≤ 4 := by
  calc
    (defectComponentCoordinateRowPairs D φ c x x').card ≤
        ((defectComponentCoordinateRowFiber D φ c x).product
          (defectComponentCoordinateRowFiber D φ c x')).card :=
      Finset.card_filter_le _ _
    _ = 4 := by simp [hx, hx']

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

/-- Coordinate form: whenever the first coordinate records adjacency from
the row-label component, every order-16 target component occupies exactly
two cells of that row. -/
theorem orderSixtyFour_regular_coordinate_componentRowFiber_card_eq_two
    {V Y : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (hreg : ∀ z, G.degree z = 8)
    (hcard : Fintype.card V = 64)
    (e c : (secondOrderDefectGraph G).ConnectedComponent)
    (hc : c.supp.ncard = 16)
    (φ : V ≃ e.supp × Y)
    (hrow : ∀ z (x : e.supp), G.Adj x.1 z ↔ (φ z).1 = x)
    (x : e.supp) :
    (defectComponentCoordinateRowFiber
      (secondOrderDefectGraph G) φ c x).card = 2 := by
  have hneighbor := orderSixtyFour_regular_componentNeighbor_card_eq_two
    G hfree hreg hcard e c hc x.2
  have heq :
      defectComponentCoordinateRowFiber
        (secondOrderDefectGraph G) φ c x =
      componentNeighborFinset G (secondOrderDefectGraph G) c x.1 := by
    ext z
    simp [defectComponentCoordinateRowFiber, componentNeighborFinset,
      hrow z x, eq_comm, and_comm]
  rw [heq, hneighbor]

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

end

end Erdos85

#print axioms Erdos85.orderSixtyFour_regular_componentNeighbor_card_eq_two
#print axioms Erdos85.defectComponentCoordinateRowPairs_card_le_four
#print axioms
  Erdos85.orderSixtyFour_regular_coordinate_componentRowFiber_card_eq_two
#print axioms Erdos85.secondOrderDefectGraph_adj_mem_component
