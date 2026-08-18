import Proofs.Erdos85FifthMomentBridge
import Proofs.Erdos85OrderSixtyFourAllTwoTriangleLedger

/-!
# Triangle-free edges are forced at the order-64 degree-eight boundary

The cubic color partition has right-hand side `64 * 8 = 512`.  Since the
ambient cubic trace is six times a triangle count, the total triangle-free
degree is congruent to two modulo six.  In particular the triangle-free edge
graph is nonempty.  This is independent of the defect-component stratum.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Exact cubic expression for the total triangle-free degree at order 64. -/
theorem orderSixtyFour_regular_sum_triangleFreeDegrees_eq
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hreg : ∀ x, G.degree x = 8) :
    (∑ x : Fin 64, ((triangleFreeEdgeGraph G).degree x : ℤ)) =
      512 - 6 * (adjacencyTriangleMinorFinset G).card := by
  have hcolor :=
    trace_adjMatrix_cube_add_colorTrace_eq_card_mul_degree_of_regular
      G hfree hreg
  rw [trace_adjMatrix_mul_secondOrderDefect_eq_sum_triangleFreeDegrees]
    at hcolor
  have htri := trace_adjMatrix_cube_eq_six_mul_triangleMinorCount
    G (by norm_num)
  rw [htri] at hcolor
  norm_num at hcolor ⊢
  omega

/-- The total triangle-free degree is `2 mod 6`; equivalently it has the
form `6z + 2` over the integers. -/
theorem orderSixtyFour_regular_sum_triangleFreeDegrees_eq_six_mul_add_two
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hreg : ∀ x, G.degree x = 8) :
    ∃ z : ℤ,
      (∑ x : Fin 64, ((triangleFreeEdgeGraph G).degree x : ℤ)) = 6 * z + 2 := by
  refine ⟨85 - (adjacencyTriangleMinorFinset G).card, ?_⟩
  rw [orderSixtyFour_regular_sum_triangleFreeDegrees_eq G hfree hreg]
  ring

/-- Equivalently, the number of triangle-free edges is one modulo three. -/
theorem orderSixtyFour_regular_triangleFreeEdge_card_eq_three_mul_add_one
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hreg : ∀ x, G.degree x = 8) :
    ∃ z : ℤ,
      ((triangleFreeEdgeGraph G).edgeFinset.card : ℤ) = 3 * z + 1 := by
  obtain ⟨z, hz⟩ :=
    orderSixtyFour_regular_sum_triangleFreeDegrees_eq_six_mul_add_two
      G hfree hreg
  have hhand := (triangleFreeEdgeGraph G).sum_degrees_eq_twice_card_edges
  have hhandZ :
      (∑ x : Fin 64, ((triangleFreeEdgeGraph G).degree x : ℤ)) =
        2 * ((triangleFreeEdgeGraph G).edgeFinset.card : ℤ) := by
    exact_mod_cast hhand
  refine ⟨z, ?_⟩
  omega

theorem orderSixtyFour_regular_triangleFreeEdge_card_mod_three_eq_one
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hreg : ∀ x, G.degree x = 8) :
    ((triangleFreeEdgeGraph G).edgeFinset.card : ℤ) % 3 = 1 := by
  obtain ⟨z, hz⟩ :=
    orderSixtyFour_regular_triangleFreeEdge_card_eq_three_mul_add_one
      G hfree hreg
  rw [hz]
  omega

/-- Every order-64 degree-eight candidate contains a triangle-free ambient
edge.  Thus no defect stratum can consist solely of antipodal edges. -/
theorem orderSixtyFour_regular_exists_triangleFreeEdge
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hreg : ∀ x, G.degree x = 8) :
    ∃ x y : Fin 64, (triangleFreeEdgeGraph G).Adj x y := by
  obtain ⟨z, hz⟩ :=
    orderSixtyFour_regular_sum_triangleFreeDegrees_eq_six_mul_add_two
      G hfree hreg
  by_contra hnone
  push Not at hnone
  have hdegree : ∀ x : Fin 64, (triangleFreeEdgeGraph G).degree x = 0 := by
    intro x
    rw [← (triangleFreeEdgeGraph G).card_neighborFinset_eq_degree,
      Finset.card_eq_zero]
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro y hy
    exact hnone x y ((triangleFreeEdgeGraph G).mem_neighborFinset x y |>.mp hy)
  simp_rw [hdegree] at hz
  norm_num at hz
  omega

end

end Erdos85

#print axioms Erdos85.orderSixtyFour_regular_sum_triangleFreeDegrees_eq
#print axioms
  Erdos85.orderSixtyFour_regular_sum_triangleFreeDegrees_eq_six_mul_add_two
#print axioms
  Erdos85.orderSixtyFour_regular_triangleFreeEdge_card_eq_three_mul_add_one
#print axioms
  Erdos85.orderSixtyFour_regular_triangleFreeEdge_card_mod_three_eq_one
#print axioms Erdos85.orderSixtyFour_regular_exists_triangleFreeEdge
