import Proofs.Erdos85OrderFortyNineOrdinaryAdjacencyConnectivityBridge
import Proofs.Erdos85C4FreeFourthMoment
import Proofs.Erdos85TriangleFreeCommutatorGap

/-!
# Exact moments of the order-49 ordinary adjacency block

In the no-triple three-high profile the 46 ordinary vertices have degrees
`7^25, 6^18, 5^3`.  Consequently the second and fourth adjacency moments
are fixed.  These are the first two residual-square moments used by the
modular characteristic-polynomial obstruction.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

local instance ordinaryGraphDecidableAdj
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj] :
    DecidableRel (orderFortyNineOrdinaryGraph G).Adj :=
  Classical.decRel _

private theorem orderFortyNineOrdinary_sum_profile_value
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    (hrange : ∀ i,
      orderFortyNineOrdinaryHighSupportCountInt G i = 0 ∨
      orderFortyNineOrdinaryHighSupportCountInt G i = 1 ∨
      orderFortyNineOrdinaryHighSupportCountInt G i = 2)
    (f : ℤ → ℤ) :
    (∑ i : Fin 46, f (orderFortyNineOrdinaryHighSupportCountInt G i)) =
      f 0 * (orderFortyNineOrdinarySupportFiber G Finset.univ 0).card +
      f 1 * (orderFortyNineOrdinarySupportFiber G Finset.univ 1).card +
      f 2 * (orderFortyNineOrdinarySupportFiber G Finset.univ 2).card := by
  let s : Fin 46 → ℤ := orderFortyNineOrdinaryHighSupportCountInt G
  have hpoint (i : Fin 46) :
      f (s i) = if s i = 0 then f 0 else if s i = 1 then f 1 else f 2 := by
    rcases hrange i with hi | hi | hi <;> simp [s, hi]
  have hsum (k c : ℤ) :
      (∑ i : Fin 46, if s i = k then c else 0) =
        c * (orderFortyNineOrdinarySupportFiber G Finset.univ k).card := by
    simp_rw [show ∀ i : Fin 46, (if s i = k then c else 0) =
        c * (if s i = k then 1 else 0) by
      intro i
      split_ifs <;> simp]
    rw [← Finset.mul_sum, Finset.sum_boole]
    simp [s, orderFortyNineOrdinarySupportFiber]
  calc
    (∑ i : Fin 46, f (orderFortyNineOrdinaryHighSupportCountInt G i)) =
        ∑ i : Fin 46, if s i = 0 then f 0 else if s i = 1 then f 1 else f 2 := by
      apply Finset.sum_congr rfl
      intro i _
      simpa [s] using hpoint i
    _ =
        (∑ i : Fin 46, if s i = 0 then f 0 else 0) +
        (∑ i : Fin 46, if s i = 1 then f 1 else 0) +
        (∑ i : Fin 46, if s i = 2 then f 2 else 0) := by
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      rcases hrange i with hi | hi | hi <;> simp [s, hi]
    _ = _ := by rw [hsum 0 (f 0), hsum 1 (f 1), hsum 2 (f 2)]

theorem orderFortyNineOrdinary_degree_moments
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x, 7 ≤ G.degree x)
    (hhigh : ∀ y : Fin 49, G.degree y = 8 ↔ y.val < 3)
    (hrange : ∀ i,
      orderFortyNineOrdinaryHighSupportCountInt G i = 0 ∨
      orderFortyNineOrdinaryHighSupportCountInt G i = 1 ∨
      orderFortyNineOrdinaryHighSupportCountInt G i = 2)
    (hzero : (orderFortyNineOrdinarySupportFiber G Finset.univ 0).card = 25)
    (hone : (orderFortyNineOrdinarySupportFiber G Finset.univ 1).card = 18)
    (htwo : (orderFortyNineOrdinarySupportFiber G Finset.univ 2).card = 3) :
    (∑ i : Fin 46, ((orderFortyNineOrdinaryGraph G).degree i : ℤ)) = 298 ∧
    (∑ i : Fin 46, ((orderFortyNineOrdinaryGraph G).degree i : ℤ) ^ 2) = 1948 := by
  have hdeg (i : Fin 46) :
      ((orderFortyNineOrdinaryGraph G).degree i : ℤ) =
        7 - orderFortyNineOrdinaryHighSupportCountInt G i :=
    orderFortyNineOrdinaryGraph_degree_int G hfree hmin hhigh i
  constructor
  · simp_rw [hdeg]
    rw [orderFortyNineOrdinary_sum_profile_value G hrange (fun z => 7 - z),
      hzero, hone, htwo]
    norm_num
  · simp_rw [hdeg]
    rw [orderFortyNineOrdinary_sum_profile_value G hrange (fun z => (7 - z) ^ 2),
      hzero, hone, htwo]
    norm_num

theorem orderFortyNineOrdinary_adjacency_second_fourth_moments
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x, 7 ≤ G.degree x)
    (hhigh : ∀ y : Fin 49, G.degree y = 8 ↔ y.val < 3)
    (hrange : ∀ i,
      orderFortyNineOrdinaryHighSupportCountInt G i = 0 ∨
      orderFortyNineOrdinaryHighSupportCountInt G i = 1 ∨
      orderFortyNineOrdinaryHighSupportCountInt G i = 2)
    (hzero : (orderFortyNineOrdinarySupportFiber G Finset.univ 0).card = 25)
    (hone : (orderFortyNineOrdinarySupportFiber G Finset.univ 1).card = 18)
    (htwo : (orderFortyNineOrdinarySupportFiber G Finset.univ 2).card = 3) :
    Matrix.trace ((orderFortyNineOrdinaryGraph G).adjMatrix ℤ ^ 2) = 298 ∧
    Matrix.trace ((orderFortyNineOrdinaryGraph G).adjMatrix ℤ ^ 4) = 3598 := by
  obtain ⟨hdeg, hdegSq⟩ := orderFortyNineOrdinary_degree_moments
    G hfree hmin hhigh hrange hzero hone htwo
  constructor
  · simpa [pow_two] using
      (trace_adjMatrix_sq_eq_sum_degrees (orderFortyNineOrdinaryGraph G)).trans hdeg
  · rw [show (orderFortyNineOrdinaryGraph G).adjMatrix ℤ ^ 4 =
        ((orderFortyNineOrdinaryGraph G).adjMatrix ℤ *
          (orderFortyNineOrdinaryGraph G).adjMatrix ℤ) *
        ((orderFortyNineOrdinaryGraph G).adjMatrix ℤ *
          (orderFortyNineOrdinaryGraph G).adjMatrix ℤ) by noncomm_ring]
    rw [trace_adjMatrix_fourth_of_not_containsC4 _
      (orderFortyNineOrdinaryGraph_not_containsC4 G hfree), hdegSq, hdeg]
    norm_num

end

end Erdos85

#print axioms Erdos85.orderFortyNineOrdinary_degree_moments
#print axioms Erdos85.orderFortyNineOrdinary_adjacency_second_fourth_moments
