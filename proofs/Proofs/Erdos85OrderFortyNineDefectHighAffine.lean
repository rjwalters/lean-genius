import Proofs.Erdos85OrderFortyNineDefectModSevenKernel

/-! # Absolute high-incidence equations for the ordinary defect graph -/

open SimpleGraph

namespace Erdos85

noncomputable section

def orderFortyNineOrdinaryDefectAdjInt
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj] :
    Matrix (Fin 46) (Fin 46) ℤ :=
  fun i j => (secondOrderDefectGraph G).adjMatrix ℤ
    (orderFortyNineOrdinaryVertex i) (orderFortyNineOrdinaryVertex j)

def orderFortyNineOrdinaryHighIncidenceInt
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    (h : Fin 49) : Fin 46 → ℤ :=
  fun i => G.adjMatrix ℤ h (orderFortyNineOrdinaryVertex i)

/-- Each absolute high-incidence column satisfies `D₀ x_h = 1 - x_h`.
The previously used `-1` eigenvectors are the differences of these three
affine equations. -/
theorem orderFortyNineOrdinaryDefectAdjInt_mulVec_highIncidence
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x, 7 ≤ G.degree x)
    (hhigh : ∀ y : Fin 49, G.degree y = 8 ↔ y.val < 3)
    {h : Fin 49} (hh : G.degree h = 8) :
    (orderFortyNineOrdinaryDefectAdjInt G).mulVec
        (orderFortyNineOrdinaryHighIncidenceInt G h) =
      fun i => 1 - orderFortyNineOrdinaryHighIncidenceInt G h i := by
  funext i
  have hi7 : G.degree (orderFortyNineOrdinaryVertex i) = 7 := by
    rcases orderFortyNine_degree_eq_seven_or_eight G hfree hmin (by decide)
        (orderFortyNineOrdinaryVertex i) with hi | hi
    · exact hi
    · have := (hhigh _).1 hi
      simp [orderFortyNineOrdinaryVertex] at this
  have hmixed := adjMatrix_mulVec_adjRow_eq_card_mixed
    G (secondOrderDefectGraph G) h (orderFortyNineOrdinaryVertex i)
  have hcard := orderFortyNine_card_highNeighbors_inter_defectNeighbors
    G hfree hmin (by decide) hh hi7
  rw [hcard] at hmixed
  simp only [Matrix.mulVec, dotProduct] at hmixed ⊢
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ] at hmixed
  have hDzero (k : Fin 3) : ¬ (secondOrderDefectGraph G).Adj
      (orderFortyNineOrdinaryVertex i) (Fin.castAdd 46 k) := by
    have hk8 : G.degree (Fin.castAdd 46 k) = 8 :=
      (hhigh _).2 (by simp)
    intro hadj
    have hzero := (orderFortyNine_degreeEight_defectDegree_and_neighborExcess_zero
      G hfree hmin (by decide) hk8).1
    have hmem : orderFortyNineOrdinaryVertex i ∈
        (secondOrderDefectGraph G).neighborFinset (Fin.castAdd 46 k) := by
      exact ((secondOrderDefectGraph G).mem_neighborFinset _ _).mpr hadj.symm
    have hpos : 0 < (secondOrderDefectGraph G).degree (Fin.castAdd 46 k) := by
      rw [← (secondOrderDefectGraph G).card_neighborFinset_eq_degree]
      exact Finset.card_pos.mpr ⟨_, hmem⟩
    omega
  have h0 : ¬ (secondOrderDefectGraph G).Adj
      (orderFortyNineOrdinaryVertex i) 0 := by simpa using hDzero 0
  have h1 : ¬ (secondOrderDefectGraph G).Adj
      (orderFortyNineOrdinaryVertex i) 1 := by simpa using hDzero 1
  have h2 : ¬ (secondOrderDefectGraph G).Adj
      (orderFortyNineOrdinaryVertex i) 2 := by simpa using hDzero 2
  have hm0 : (secondOrderDefectGraph G).adjMatrix ℤ
      (orderFortyNineOrdinaryVertex i) 0 = 0 := by
    simp [SimpleGraph.adjMatrix_apply, h0]
  have hm1 : (secondOrderDefectGraph G).adjMatrix ℤ
      (orderFortyNineOrdinaryVertex i) 1 = 0 := by
    simp [SimpleGraph.adjMatrix_apply, h1]
  have hm2 : (secondOrderDefectGraph G).adjMatrix ℤ
      (orderFortyNineOrdinaryVertex i) 2 = 0 := by
    simp [SimpleGraph.adjMatrix_apply, h2]
  have he1 : (Fin.succ 0 : Fin 49) = 1 := by decide
  have he2 : ((Fin.succ 0).succ : Fin 49) = 2 := by decide
  rw [he1, he2, hm0, hm1, hm2] at hmixed
  simp only [zero_mul, zero_add] at hmixed
  have hsucc (j : Fin 46) : j.succ.succ.succ = orderFortyNineOrdinaryVertex j := by
    apply Fin.ext
    simp [orderFortyNineOrdinaryVertex]
    omega
  simp_rw [hsucc] at hmixed
  simp [orderFortyNineOrdinaryDefectAdjInt,
    orderFortyNineOrdinaryHighIncidenceInt,
    SimpleGraph.adjMatrix_apply] at hmixed ⊢
  by_cases hadj : G.Adj h (orderFortyNineOrdinaryVertex i)
  · simp [hadj] at hmixed ⊢
    exact hmixed
  · simp [hadj] at hmixed ⊢
    exact hmixed

end

end Erdos85

#print axioms Erdos85.orderFortyNineOrdinaryDefectAdjInt_mulVec_highIncidence
