import Proofs.Erdos85OrderSixtyFourRegularPartitionShapes

/-! # Owner-graph density in the connected-defect stratum -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Inclusion-exclusion lower bound for common neighborhoods in a finite
regular graph. -/
theorem regular_commonNeighbor_card_add_order_ge_two_mul_degree
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (k : ℕ)
    (hreg : ∀ x, H.degree x = k) (x y : V) :
    (H.neighborFinset x ∩ H.neighborFinset y).card + Fintype.card V ≥
      2 * k := by
  have hx : (H.neighborFinset x).card = k := by
    rw [H.card_neighborFinset_eq_degree, hreg]
  have hy : (H.neighborFinset y).card = k := by
    rw [H.card_neighborFinset_eq_degree, hreg]
  have hunion : (H.neighborFinset x ∪ H.neighborFinset y).card ≤
      Fintype.card V := Finset.card_le_card (Finset.subset_univ _)
  have hinc := Finset.card_union_add_card_inter
    (H.neighborFinset x) (H.neighborFinset y)
  omega

/-- In the order-64 connected-defect stratum, the unique owner graph is
56-regular.  Consequently every two ambient vertices have at least 48 common
owner neighbors.  This is the first graph-facing algebraic constraint on the
previously untouched `[8]` stratum. -/
theorem orderSixtyFour_regular_oneComponent_ownerDensity
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hreg : ∀ x, G.degree x = 8)
    (hcount : Fintype.card
      (secondOrderDefectGraph G).ConnectedComponent = 1) :
    ∃ a : (secondOrderDefectGraph G).ConnectedComponent,
      (∀ x,
        (componentOwnerGraph G (secondOrderDefectGraph G) a).degree x = 56) ∧
      (∀ x y,
        48 ≤ ((componentOwnerGraph G (secondOrderDefectGraph G) a).neighborFinset x ∩
          (componentOwnerGraph G (secondOrderDefectGraph G) a).neighborFinset y).card) := by
  obtain ⟨m, E, hm, hma⟩ :=
    orderSixtyFour_regular_one_defectComponent_partition_shape
      G hfree hreg hcount
  let a := E.symm 0
  let A := componentOwnerGraph G (secondOrderDefectGraph G) a
  have hAreg : ∀ x, A.degree x = 56 := by
    intro x
    have h := binarySquare_regular_componentOwnerGraph_degree
      G hfree (q := 8) (by norm_num) hreg (by norm_num) a (hm a) x
    simpa [A, a, hma] using h
  refine ⟨a, hAreg, ?_⟩
  intro x y
  have hcommon := regular_commonNeighbor_card_add_order_ge_two_mul_degree
    A 56 hAreg x y
  change 48 ≤ (A.neighborFinset x ∩ A.neighborFinset y).card
  norm_num at hcommon
  omega

end

end Erdos85

#print axioms Erdos85.regular_commonNeighbor_card_add_order_ge_two_mul_degree
#print axioms Erdos85.orderSixtyFour_regular_oneComponent_ownerDensity
