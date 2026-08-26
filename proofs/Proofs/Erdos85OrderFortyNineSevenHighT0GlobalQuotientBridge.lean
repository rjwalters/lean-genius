import Proofs.Erdos85OrderFortyNineSevenHighT0LocalQuotientBridge

/-!
# Global quotient sums in the seven-high empty-triple case

This file sums the graph-valid pointwise law `P = E + k` over each low
high-support fiber.  The resulting constants `42`, `14`, and `0` are the
three balance rows consumed by the one-parameter quotient arithmetic.
-/

namespace Erdos85

open SimpleGraph

noncomputable section

def sevenHighT0LowSupportFiber
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj] (k : Nat) :
    Finset (Fin 49) :=
  (orderFortyNineLowVertices G).filter fun y =>
    (orderFortyNineHighSupport G y).card = k

def sevenHighT0PairNeighborCount
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj] (y : Fin 49) : Nat :=
  ((G.neighborFinset y).filter fun x =>
    (orderFortyNineHighSupport G x).card = 2).card

def sevenHighT0LowEmptyNeighborCount
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj] (y : Fin 49) : Nat :=
  (((G.neighborFinset y).filter fun x =>
    (orderFortyNineHighSupport G x).card = 0).filter fun x =>
      x ∉ orderFortyNineHighVertices G).card

private theorem degree_eq_seven_of_mem_lowSupportFiber
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    {k : Nat} {y : Fin 49} (hy : y ∈ sevenHighT0LowSupportFiber G k) :
    G.degree y = 7 := by
  have hyLow := (Finset.mem_filter.mp hy).1
  have hyNotHigh := (Finset.mem_sdiff.mp hyLow).2
  rcases orderFortyNine_degree_eq_seven_or_eight
      G hfree hmin (Fintype.card_fin 49) y with hy7 | hy8
  · exact hy7
  · exact False.elim (hyNotHigh (by
      simp [orderFortyNineHighVertices, hy8]))

/-- Sum of the pointwise `P = E + k` law over an arbitrary support fiber. -/
theorem sevenHigh_t0_sum_pairNeighborCount_eq_sum_lowEmpty_add
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (hHigh : (orderFortyNineHighVertices G).card = 7)
    (hzero : orderFortyNineHighIncidenceCount G 3 = 0)
    (k : Nat) :
    (∑ y ∈ sevenHighT0LowSupportFiber G k,
      sevenHighT0PairNeighborCount G y) =
      (∑ y ∈ sevenHighT0LowSupportFiber G k,
        sevenHighT0LowEmptyNeighborCount G y) +
        k * (sevenHighT0LowSupportFiber G k).card := by
  have hpoint : ∀ y ∈ sevenHighT0LowSupportFiber G k,
      sevenHighT0PairNeighborCount G y =
        sevenHighT0LowEmptyNeighborCount G y + k := by
    intro y hy
    have hyDegree := degree_eq_seven_of_mem_lowSupportFiber
      G hfree hmin hy
    have hySupport := (Finset.mem_filter.mp hy).2
    have hlocal :=
      sevenHigh_t0_pairNeighborCount_eq_lowEmptyNeighborCount_add_support
        G hfree hmin hHigh hzero hyDegree
    simpa [sevenHighT0PairNeighborCount,
      sevenHighT0LowEmptyNeighborCount, hySupport] using hlocal
  calc
    (∑ y ∈ sevenHighT0LowSupportFiber G k,
        sevenHighT0PairNeighborCount G y) =
        ∑ y ∈ sevenHighT0LowSupportFiber G k,
          (sevenHighT0LowEmptyNeighborCount G y + k) := by
            apply Finset.sum_congr rfl
            intro y hy
            exact hpoint y hy
    _ = (∑ y ∈ sevenHighT0LowSupportFiber G k,
          sevenHighT0LowEmptyNeighborCount G y) +
          k * (sevenHighT0LowSupportFiber G k).card := by
            rw [Finset.sum_add_distrib]
            simp [Nat.mul_comm]

/-- Pair-support roots contribute the constant `2 · 21 = 42`. -/
theorem sevenHigh_t0_pairFiber_global_balance
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (hHigh : (orderFortyNineHighVertices G).card = 7)
    (hzero : orderFortyNineHighIncidenceCount G 3 = 0) :
    (∑ y ∈ sevenHighT0LowSupportFiber G 2,
      sevenHighT0PairNeighborCount G y) =
      (∑ y ∈ sevenHighT0LowSupportFiber G 2,
        sevenHighT0LowEmptyNeighborCount G y) + 42 := by
  have hcensus := sevenHigh_t0_global_incidence G hfree hmin hHigh hzero
  have hcard : (sevenHighT0LowSupportFiber G 2).card = 21 := by
    simpa [sevenHighT0LowSupportFiber, orderFortyNineHighSupport,
      orderFortyNineHighIncidenceCount] using hcensus.2.2
  have hsum := sevenHigh_t0_sum_pairNeighborCount_eq_sum_lowEmpty_add
    G hfree hmin hHigh hzero 2
  rw [hcard] at hsum
  norm_num at hsum ⊢
  exact hsum

/-- Singleton-support roots contribute the constant `1 · 14 = 14`. -/
theorem sevenHigh_t0_singletonFiber_global_balance
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (hHigh : (orderFortyNineHighVertices G).card = 7)
    (hzero : orderFortyNineHighIncidenceCount G 3 = 0) :
    (∑ y ∈ sevenHighT0LowSupportFiber G 1,
      sevenHighT0PairNeighborCount G y) =
      (∑ y ∈ sevenHighT0LowSupportFiber G 1,
        sevenHighT0LowEmptyNeighborCount G y) + 14 := by
  have hcensus := sevenHigh_t0_global_incidence G hfree hmin hHigh hzero
  have hcard : (sevenHighT0LowSupportFiber G 1).card = 14 := by
    simpa [sevenHighT0LowSupportFiber, orderFortyNineHighSupport,
      orderFortyNineHighIncidenceCount] using hcensus.2.1
  have hsum := sevenHigh_t0_sum_pairNeighborCount_eq_sum_lowEmpty_add
    G hfree hmin hHigh hzero 1
  rw [hcard] at hsum
  norm_num at hsum ⊢
  exact hsum

/-- Empty-support roots have equal aggregate pair and low-empty counts. -/
theorem sevenHigh_t0_emptyFiber_global_balance
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (hHigh : (orderFortyNineHighVertices G).card = 7)
    (hzero : orderFortyNineHighIncidenceCount G 3 = 0) :
    (∑ y ∈ sevenHighT0LowSupportFiber G 0,
      sevenHighT0PairNeighborCount G y) =
      ∑ y ∈ sevenHighT0LowSupportFiber G 0,
        sevenHighT0LowEmptyNeighborCount G y := by
  have hsum := sevenHigh_t0_sum_pairNeighborCount_eq_sum_lowEmpty_add
    G hfree hmin hHigh hzero 0
  simpa using hsum

end

end Erdos85

#print axioms Erdos85.sevenHigh_t0_sum_pairNeighborCount_eq_sum_lowEmpty_add
#print axioms Erdos85.sevenHigh_t0_pairFiber_global_balance
#print axioms Erdos85.sevenHigh_t0_singletonFiber_global_balance
#print axioms Erdos85.sevenHigh_t0_emptyFiber_global_balance
