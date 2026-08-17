import Proofs.Erdos85HoffmanEqualityPartition

/-!
# Cross-color factors induced by Hoffman cells

Order-`q` defect components are equitable cells in every owner graph.  This
file records the complementary cross-color fact: distinct owner colors give
disjoint neighbor slices.  Thus the restrictions to two order-`q` defect
components form edge-disjoint regular bipartite factors; colors of normalized
size one give perfect matchings.
-/

open SimpleGraph

namespace Erdos85

/-- Distinct owner colors give disjoint neighbor slices in every defect
component.  This is the local, finset-valued form of unique ownership. -/
theorem componentOwnerGraph_componentNeighborFinset_disjoint
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (c d e : (secondOrderDefectGraph G).ConnectedComponent) (hcd : c ≠ d)
    (x : V) :
    Disjoint
      (componentNeighborFinset
        (componentOwnerGraph G (secondOrderDefectGraph G) c)
        (secondOrderDefectGraph G) e x)
      (componentNeighborFinset
        (componentOwnerGraph G (secondOrderDefectGraph G) d)
        (secondOrderDefectGraph G) e x) := by
  rw [Finset.disjoint_left]
  intro y hyc hyd
  have hycData := Finset.mem_filter.mp hyc
  have hydData := Finset.mem_filter.mp hyd
  have hcEdge :=
    ((componentOwnerGraph G (secondOrderDefectGraph G) c).mem_neighborFinset x y).mp
      hycData.1
  have hdEdge :=
    ((componentOwnerGraph G (secondOrderDefectGraph G) d).mem_neighborFinset x y).mp
      hydData.1
  have hcAdj :=
    (componentOwnerGraph_adj G (secondOrderDefectGraph G) c x y).mp hcEdge
  have hdAdj :=
    (componentOwnerGraph_adj G (secondOrderDefectGraph G) d x y).mp hdEdge
  obtain ⟨z, hz⟩ := hcAdj.2
  have hzData := Finset.mem_inter.mp hz
  have hnotD : ¬ (secondOrderDefectGraph G).Adj x y := by
    have hzx := (Finset.mem_filter.mp hzData.1).1
    have hzy := (Finset.mem_filter.mp hzData.2).1
    exact not_secondOrderDefect_adj_of_commonNeighbor G hfree hcAdj.1
      ((G.mem_neighborFinset x z).mp hzx)
      ((G.mem_neighborFinset y z).mp hzy)
  obtain ⟨owner, howner, huniq⟩ :=
    (not_secondOrderDefect_adj_iff_existsUnique_componentOwnerGraph_adj
      G hfree hcAdj.1).mp hnotD
  have hceq : c = owner := huniq c hcEdge
  have hdeq : d = owner := huniq d hdEdge
  exact hcd (hceq.trans hdeq.symm)

/-- On an order-`q` Hoffman cell `e`, every outside vertex has exactly `m_c`
neighbors of owner color `c`.  This is the cardinal form of the equitable
indicator equation. -/
theorem binarySquare_regular_sizeQ_component_ownerNeighborSlice_card
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (e c : (secondOrderDefectGraph G).ConnectedComponent) {m_c : ℕ}
    (hc : c.supp.ncard = q * m_c) (he : e.supp.ncard = q)
    (x : V) (hx : x ∉ e.supp) :
    (componentNeighborFinset
      (componentOwnerGraph G (secondOrderDefectGraph G) c)
      (secondOrderDefectGraph G) e x).card = m_c := by
  let O := componentOwnerGraph G (secondOrderDefectGraph G) c
  let S := e.supp.toFinite.toFinset
  have hmul := binarySquare_regular_sizeQ_component_ownerIndicator_mulVec
    G hfree hq hreg hcard e c hc he x
  rw [if_neg hx] at hmul
  have hsum : (O.adjMatrix ℤ).mulVec (finsetIndicatorInt S) x =
      ((componentNeighborFinset O (secondOrderDefectGraph G) e x).card : ℤ) := by
    rw [Matrix.mulVec, dotProduct]
    simp only [SimpleGraph.adjMatrix_apply, finsetIndicatorInt]
    calc
      (∑ y, (if O.Adj x y then (1 : ℤ) else 0) *
          if y ∈ S then 1 else 0) =
          ∑ y, if O.Adj x y ∧ y ∈ S then (1 : ℤ) else 0 := by
            apply Finset.sum_congr rfl
            intro y _hy
            by_cases hxy : O.Adj x y <;> by_cases hyS : y ∈ S <;>
              simp [hxy, hyS]
      _ = (((Finset.univ : Finset V).filter fun y => O.Adj x y ∧ y ∈ S).card : ℤ) := by
            rw [Finset.sum_boole]
      _ = ((componentNeighborFinset O (secondOrderDefectGraph G) e x).card : ℤ) := by
            have hfin : (Finset.univ : Finset V).filter
                (fun y => O.Adj x y ∧ y ∈ S) =
                componentNeighborFinset O (secondOrderDefectGraph G) e x := by
              ext y
              simp [componentNeighborFinset, SimpleGraph.mem_neighborFinset, S,
                SimpleGraph.ConnectedComponent.mem_supp_iff]
            rw [hfin]
  change (O.adjMatrix ℤ).mulVec (finsetIndicatorInt S) x = (m_c : ℤ) at hmul
  rw [hsum] at hmul
  exact_mod_cast hmul

end Erdos85
