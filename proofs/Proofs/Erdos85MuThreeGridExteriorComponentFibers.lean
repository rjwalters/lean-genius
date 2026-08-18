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

/-- Cross-row component loads are symmetric because defect adjacency is
undirected. -/
theorem defectComponentCoordinateRowPairs_card_comm
    {V X Y : Type*} [Fintype V] [DecidableEq V] [DecidableEq X]
    (D : SimpleGraph V) [DecidableRel D.Adj]
    [DecidableEq D.ConnectedComponent]
    (φ : V ≃ X × Y) (c : D.ConnectedComponent) (x x' : X) :
    (defectComponentCoordinateRowPairs D φ c x x').card =
      (defectComponentCoordinateRowPairs D φ c x' x).card := by
  apply Finset.card_bij (fun p _ => (p.2, p.1))
  · intro p hp
    have hp' := Finset.mem_filter.mp hp
    have hpProd := Finset.mem_product.mp hp'.1
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_product.mpr ⟨hpProd.2, hpProd.1⟩, D.adj_symm hp'.2⟩
  · intro p hp q hq heq
    exact Prod.ext (congrArg Prod.snd heq) (congrArg Prod.fst heq)
  · intro q hq
    refine ⟨(q.2, q.1), ?_, by simp⟩
    have hq' := Finset.mem_filter.mp hq
    have hqProd := Finset.mem_product.mp hq'.1
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_product.mpr ⟨hqProd.2, hqProd.1⟩, D.adj_symm hq'.2⟩

/-- If `D` has no edge inside coordinate row `x`, the diagonal load at `x`
is zero. -/
theorem defectComponentCoordinateRowPairs_self_card_eq_zero
    {V X Y : Type*} [Fintype V] [DecidableEq V] [DecidableEq X]
    (D : SimpleGraph V) [DecidableRel D.Adj]
    [DecidableEq D.ConnectedComponent]
    (φ : V ≃ X × Y) (c : D.ConnectedComponent) (x : X)
    (hrow : ∀ u v : V, (φ u).1 = x → (φ v).1 = x → ¬ D.Adj u v) :
    (defectComponentCoordinateRowPairs D φ c x x).card = 0 := by
  apply Finset.card_eq_zero.mpr
  ext p
  constructor
  · intro hp
    have hp' := Finset.mem_filter.mp hp
    have hpProd := Finset.mem_product.mp hp'.1
    have hu := (Finset.mem_filter.mp hpProd.1).2.2
    have hv := (Finset.mem_filter.mp hpProd.2).2.2
    exact (hrow p.1 p.2 hu hv hp'.2).elim
  · simp

/-- In a 7-regular component with two cells in each row, the ordered
cross-row loads from a fixed row sum to `2 * 7 = 14`. -/
theorem sum_defectComponentCoordinateRowPairs_card_eq_fourteen
    {V X Y : Type*} [Fintype V] [Fintype X] [Fintype Y]
    [DecidableEq V] [DecidableEq X]
    (D : SimpleGraph V) [DecidableRel D.Adj]
    [DecidableEq D.ConnectedComponent]
    (φ : V ≃ X × Y) (c : D.ConnectedComponent) (x : X)
    (hx : (defectComponentCoordinateRowFiber D φ c x).card = 2)
    (hdeg : ∀ u : V, u ∈ c.supp → D.degree u = 7) :
    (∑ x' : X,
      (defectComponentCoordinateRowPairs D φ c x x').card) = 14 := by
  let A := defectComponentCoordinateRowFiber D φ c x
  let P := ((A.product (Finset.univ : Finset V)).filter fun p =>
    p.2 ∈ c.supp ∧ D.Adj p.1 p.2)
  have hP_by_row : P.card =
      ∑ x' : X, (defectComponentCoordinateRowPairs D φ c x x').card := by
    have hmaps : ∀ p ∈ P, (φ p.2).1 ∈ (Finset.univ : Finset X) := by
      intro p _
      exact Finset.mem_univ _
    rw [Finset.card_eq_sum_card_fiberwise hmaps]
    apply Finset.sum_congr rfl
    intro x' _
    congr 1
    ext p
    simp [P, A, defectComponentCoordinateRowPairs,
      defectComponentCoordinateRowFiber, and_assoc, and_left_comm, and_comm]
  have hP_by_source : P.card = 14 := by
    have hmaps : ∀ p ∈ P, p.1 ∈ A := by
      intro p hp
      have hp' : p ∈ (A.product (Finset.univ : Finset V)).filter
          (fun q => q.2 ∈ c.supp ∧ D.Adj q.1 q.2) := by simpa [P] using hp
      exact (Finset.mem_product.mp (Finset.mem_filter.mp hp').1).1
    rw [Finset.card_eq_sum_card_fiberwise hmaps]
    have hfiber : ∀ u ∈ A,
        ((P.filter fun p => p.1 = u).card) = 7 := by
      intro u hu
      have huc : u ∈ c.supp := by
        exact (Finset.mem_filter.mp hu).2.1
      have heq : (P.filter fun p => p.1 = u) =
          (({u} : Finset V).product (D.neighborFinset u)) := by
        ext p
        constructor
        · intro hp
          have hpOuter := Finset.mem_filter.mp hp
          have hpP : p ∈ (A.product (Finset.univ : Finset V)).filter
              (fun q => q.2 ∈ c.supp ∧ D.Adj q.1 q.2) := by
            simpa [P] using hpOuter.1
          have hpPred := (Finset.mem_filter.mp hpP).2
          apply Finset.mem_product.mpr
          exact ⟨Finset.mem_singleton.mpr hpOuter.2,
            by simpa [hpOuter.2] using
              (D.mem_neighborFinset p.1 p.2).mpr hpPred.2⟩
        · intro hp
          have hpProd := Finset.mem_product.mp hp
          have hpu := Finset.mem_singleton.mp hpProd.1
          have hadj_u : D.Adj u p.2 :=
            (D.mem_neighborFinset u p.2).mp hpProd.2
          have hadj : D.Adj p.1 p.2 := by simpa [hpu] using hadj_u
          have hpc : p.2 ∈ c.supp := by
            rw [ConnectedComponent.mem_supp_iff] at huc ⊢
            rw [hpu] at hadj
            exact (ConnectedComponent.connectedComponentMk_eq_of_adj hadj).symm.trans huc
          apply Finset.mem_filter.mpr
          constructor
          · show p ∈ P
            change p ∈ (A.product (Finset.univ : Finset V)).filter
              (fun q => q.2 ∈ c.supp ∧ D.Adj q.1 q.2)
            exact Finset.mem_filter.mpr
              ⟨Finset.mem_product.mpr
                ⟨by simpa [hpu] using hu, Finset.mem_univ _⟩, hpc, hadj⟩
          · exact hpu
      rw [heq]
      simp [D.card_neighborFinset_eq_degree, hdeg u huc]
    calc
      (∑ u ∈ A, (P.filter fun p => p.1 = u).card) =
          ∑ u ∈ A, 7 := by apply Finset.sum_congr rfl hfiber
      _ = A.card * 7 := by simp
      _ = 14 := by simp [A, hx]
  omega

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
#print axioms Erdos85.defectComponentCoordinateRowPairs_card_comm
#print axioms Erdos85.defectComponentCoordinateRowPairs_self_card_eq_zero
#print axioms
  Erdos85.sum_defectComponentCoordinateRowPairs_card_eq_fourteen
#print axioms
  Erdos85.orderSixtyFour_regular_coordinate_componentRowFiber_card_eq_two
#print axioms Erdos85.secondOrderDefectGraph_adj_mem_component
