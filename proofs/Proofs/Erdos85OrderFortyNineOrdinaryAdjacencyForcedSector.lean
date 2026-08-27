import Proofs.Erdos85OrderFortyNineDefectForcedSector
import Proofs.Erdos85OrderFortyNineLowNeighborhoodPartition

/-! # The forced sector of the order-49 ordinary adjacency block -/

open SimpleGraph

namespace Erdos85

noncomputable section

def orderFortyNineOrdinaryAdjInt
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj] :
    Matrix (Fin 46) (Fin 46) ℤ :=
  fun i j => G.adjMatrix ℤ
    (orderFortyNineOrdinaryVertex i) (orderFortyNineOrdinaryVertex j)

/-- Each high-neighborhood incidence column is sent to the all-ones vector
by the ordinary adjacency block. -/
theorem orderFortyNineOrdinaryAdjInt_mulVec_highIncidence
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x, 7 ≤ G.degree x)
    (hhigh : ∀ y : Fin 49, G.degree y = 8 ↔ y.val < 3)
    {h : Fin 49} (hh : G.degree h = 8) :
    (orderFortyNineOrdinaryAdjInt G).mulVec
        (orderFortyNineOrdinaryHighIncidenceInt G h) = fun _ => 1 := by
  funext i
  have hi7 : G.degree (orderFortyNineOrdinaryVertex i) = 7 := by
    rcases orderFortyNine_degree_eq_seven_or_eight G hfree hmin (by decide)
        (orderFortyNineOrdinaryVertex i) with hi | hi
    · exact hi
    · have := (hhigh _).1 hi
      simp [orderFortyNineOrdinaryVertex] at this
  have hcount := orderFortyNine_low_high_card_common_eq_one
    G hfree hmin (by decide) hi7 hh
  have hmul := adjMatrix_mulVec_adjRow_eq_card_mixed
    G G h (orderFortyNineOrdinaryVertex i)
  rw [Finset.inter_comm] at hcount
  rw [hcount] at hmul
  simp only [Matrix.mulVec, dotProduct] at hmul ⊢
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ] at hmul
  have hroot (k : Fin 3) : ¬ G.Adj h (Fin.castAdd 46 k) := by
    have hk8 : G.degree (Fin.castAdd 46 k) = 8 :=
      (hhigh _).2 (by simp)
    exact orderFortyNine_not_adj_degreeEight_degreeEight
      G hfree hmin (by decide) hh hk8
  have hn0 : ¬ G.Adj h 0 := by simpa using hroot 0
  have hn1 : ¬ G.Adj h 1 := by simpa using hroot 1
  have hn2 : ¬ G.Adj h 2 := by simpa using hroot 2
  have h0 : G.adjMatrix ℤ h 0 = 0 := by
    simp [SimpleGraph.adjMatrix_apply, hn0]
  have h1 : G.adjMatrix ℤ h 1 = 0 := by
    simp [SimpleGraph.adjMatrix_apply, hn1]
  have h2 : G.adjMatrix ℤ h 2 = 0 := by
    simp [SimpleGraph.adjMatrix_apply, hn2]
  have he1 : (Fin.succ 0 : Fin 49) = 1 := by decide
  have he2 : ((Fin.succ 0).succ : Fin 49) = 2 := by decide
  rw [he1, he2, h0, h1, h2] at hmul
  simp only [mul_zero] at hmul
  have hsucc (j : Fin 46) :
      j.succ.succ.succ = orderFortyNineOrdinaryVertex j := by
    apply Fin.ext
    simp [orderFortyNineOrdinaryVertex]
    omega
  simp_rw [hsucc] at hmul
  simpa [orderFortyNineOrdinaryAdjInt,
    orderFortyNineOrdinaryHighIncidenceInt,
    SimpleGraph.adjMatrix_apply, G.adj_comm] using hmul

/-- Summing the three incidence columns gives `C s = 3·1`. -/
theorem orderFortyNineOrdinaryAdjInt_mulVec_highSupportCount
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x, 7 ≤ G.degree x)
    (hhigh : ∀ y : Fin 49, G.degree y = 8 ↔ y.val < 3) :
    (orderFortyNineOrdinaryAdjInt G).mulVec
        (orderFortyNineOrdinaryHighSupportCountInt G) = fun _ => 3 := by
  have hh (h : Fin 3) : G.degree (Fin.castAdd 46 h) = 8 :=
    (hhigh _).2 (by simp)
  have heq (h : Fin 3) := orderFortyNineOrdinaryAdjInt_mulVec_highIncidence
    G hfree hmin hhigh (hh h)
  funext i
  simp only [Matrix.mulVec, dotProduct,
    orderFortyNineOrdinaryHighSupportCountInt]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Eq.trans (Finset.sum_congr rfl fun h _ => congrFun (heq h) i)
  simp

end

end Erdos85

#print axioms Erdos85.orderFortyNineOrdinaryAdjInt_mulVec_highIncidence
#print axioms Erdos85.orderFortyNineOrdinaryAdjInt_mulVec_highSupportCount
