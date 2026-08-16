import Proofs.Erdos85SquareOrderHighIncidenceCap
import Proofs.Erdos85DegreeExcessStratification

/-!
# Defect/incidence conservation at square order

At order `d^2`, degree excess above `d` is the indicator of the high sector.
The general local excess budget therefore says that a low vertex with `k`
high neighbors has second-order defect degree exactly `d-1-k`.  High
vertices have defect degree zero.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- At square order, neighbor degree excess is precisely high-neighbor
incidence. -/
theorem squareOrder_neighborDegreeExcess_eq_highNeighborCount
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    {d : Nat} (hd : 2 ≤ d) (hmin : ∀ x : V, d ≤ G.degree x)
    (hcover : ∀ {u v}, G.Adj u v → G.degree u = d ∨ G.degree v = d)
    (hcard : Fintype.card V = d * d) (x : V) :
    neighborDegreeExcess G d x =
      (G.neighborFinset x ∩ squareOrderHighVertices G d).card := by
  rw [neighborDegreeExcess_eq_sum_neighborFinset]
  have hterm : ∀ y ∈ G.neighborFinset x,
      G.degree y - d = if G.degree y = d + 1 then 1 else 0 := by
    intro y _hy
    rcases squareOrder_degree_eq_or_succ_of_tightEdgeCover
        G hfree hd hmin hcover hcard y with hy | hy
    · simp [hy]
    · simp [hy]
  calc
    (∑ y ∈ G.neighborFinset x, (G.degree y - d)) =
        ∑ y ∈ G.neighborFinset x,
          if G.degree y = d + 1 then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro y hy
      exact hterm y hy
    _ = ((G.neighborFinset x).filter
        fun y => G.degree y = d + 1).card := by
      rw [Finset.card_filter]
    _ = (G.neighborFinset x ∩ squareOrderHighVertices G d).card := by
      congr 1
      ext y
      simp [squareOrderHighVertices, and_comm]

/-- **Uniform defect/PBD conservation law.** A degree-`d` vertex of
high-incidence `k` has second-order defect degree `d-1-k`. -/
theorem squareOrder_defectDegree_add_highNeighborCount_eq_sub_one
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    {d : Nat} (hd : 2 ≤ d) (hmin : ∀ x : V, d ≤ G.degree x)
    (hcover : ∀ {u v}, G.Adj u v → G.degree u = d ∨ G.degree v = d)
    (hcard : Fintype.card V = d * d)
    {x : V} (hx : G.degree x = d) :
    (secondOrderDefectGraph G).degree x +
      (G.neighborFinset x ∩ squareOrderHighVertices G d).card = d - 1 := by
  have hcardBudget :
      Fintype.card V = d * (d - 1) + 1 + (d - 1) := by
    rw [hcard]
    have hd1 : 1 ≤ d := by omega
    calc
      d * d = d * ((d - 1) + 1) := by rw [Nat.sub_add_cancel hd1]
      _ = d * (d - 1) + d := by ring
      _ = d * (d - 1) + 1 + (d - 1) := by omega
  have hbudget :=
    secondOrderDefect_degree_add_weightedExcess_add_neighborExcess
      G hfree (d := d) (q := d - 1) (by omega) hmin hcardBudget x
  rw [hx] at hbudget
  simp only [Nat.sub_self, zero_mul, add_zero] at hbudget
  rwa [squareOrder_neighborDegreeExcess_eq_highNeighborCount
    G hfree hd hmin hcover hcard x] at hbudget

/-- The high side of the same profile: every degree-`d+1` vertex is
isolated in the second-order defect graph. -/
theorem squareOrder_high_defectDegree_eq_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    {d : Nat} (hd : 2 ≤ d) (hmin : ∀ x : V, d ≤ G.degree x)
    (hcard : Fintype.card V = d * d)
    {x : V} (hx : G.degree x = d + 1) :
    (secondOrderDefectGraph G).degree x = 0 :=
  (squareOrder_degree_succ_highRoot_structure
    G hfree hd hmin hcard hx).1

end

end Erdos85
