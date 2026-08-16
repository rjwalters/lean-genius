import Proofs.Erdos85SquareOrderDefectIncidence

/-!
# Global defect-edge budget at square order

Summing the local defect/incidence conservation law gives an exact relation
between the number `h` of degree-`d+1` vertices and the edge count of the
second-order defect graph:

`2 |E(D)| + 2 d h = d^2 (d-1)`.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- A single identity covering both vertex strata.  Low vertices spend
their `d-1` budget between defect degree and high incidence; high vertices
spend it in the final indicator term. -/
theorem squareOrder_defect_incidence_indicator_budget
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    {d : Nat} (hd : 2 ≤ d) (hmin : ∀ x : V, d ≤ G.degree x)
    (hcover : ∀ {u v}, G.Adj u v → G.degree u = d ∨ G.degree v = d)
    (hcard : Fintype.card V = d * d) (x : V) :
    (secondOrderDefectGraph G).degree x +
        (G.neighborFinset x ∩ squareOrderHighVertices G d).card +
        (if x ∈ squareOrderHighVertices G d then d - 1 else 0) = d - 1 := by
  by_cases hxHigh : x ∈ squareOrderHighVertices G d
  · have hxdegree : G.degree x = d + 1 :=
      (Finset.mem_filter.mp hxHigh).2
    have hDzero := squareOrder_high_defectDegree_eq_zero
      G hfree hd hmin hcard hxdegree
    have hkzero := squareOrder_highNeighborCount_eq_zero_of_high
      G hcover hxHigh
    simp [hxHigh, hDzero, hkzero]
  · have hxdegree : G.degree x = d := by
      rcases squareOrder_degree_eq_or_succ_of_tightEdgeCover
          G hfree hd hmin hcover hcard x with hx | hx
      · exact hx
      · exact (hxHigh (Finset.mem_filter.mpr ⟨by simp, hx⟩)).elim
    have hbudget :=
      squareOrder_defectDegree_add_highNeighborCount_eq_sub_one
        G hfree hd hmin hcover hcard hxdegree
    simpa [hxHigh] using hbudget

/-- **Exact global defect-edge budget.** -/
theorem squareOrder_two_mul_defectEdges_add_two_mul_degree_mul_high_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    {d : Nat} (hd : 2 ≤ d) (hmin : ∀ x : V, d ≤ G.degree x)
    (hcover : ∀ {u v}, G.Adj u v → G.degree u = d ∨ G.degree v = d)
    (hcard : Fintype.card V = d * d) :
    2 * (secondOrderDefectGraph G).edgeFinset.card +
        2 * d * (squareOrderHighVertices G d).card =
      d * d * (d - 1) := by
  classical
  let D := secondOrderDefectGraph G
  let H := squareOrderHighVertices G d
  let k : V → Nat := fun x => (G.neighborFinset x ∩ H).card
  have hpoint : ∀ x : V,
      D.degree x + k x + (if x ∈ H then d - 1 else 0) = d - 1 := by
    intro x
    simpa [D, H, k] using squareOrder_defect_incidence_indicator_budget
      G hfree hd hmin hcover hcard x
  have hsum :
      (∑ x : V, (D.degree x + k x +
        (if x ∈ H then d - 1 else 0))) = ∑ _x : V, (d - 1) := by
    apply Finset.sum_congr rfl
    intro x _hx
    exact hpoint x
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at hsum
  have hfirst : (∑ x : V, k x) = (d + 1) * H.card := by
    simpa [H, k] using squareOrder_sum_highNeighborCount_eq G d
  have hindicator :
      (∑ x : V, if x ∈ H then d - 1 else 0) = H.card * (d - 1) := by
    simp [H]
  have hconstant : (∑ _x : V, (d - 1)) = (d * d) * (d - 1) := by
    simp [hcard]
  rw [hfirst, hindicator, hconstant] at hsum
  rw [D.sum_degrees_eq_twice_card_edges] at hsum
  have hdrep : d = (d - 1) + 1 := by omega
  have hcombine :
      (d + 1) * H.card + H.card * (d - 1) = 2 * d * H.card := by
    rw [hdrep, Nat.add_sub_cancel]
    ring
  calc
    2 * D.edgeFinset.card + 2 * d * H.card =
        2 * D.edgeFinset.card +
          ((d + 1) * H.card + H.card * (d - 1)) := by rw [hcombine]
    _ = d * d * (d - 1) := by simpa only [Nat.add_assoc] using hsum

end

end Erdos85
