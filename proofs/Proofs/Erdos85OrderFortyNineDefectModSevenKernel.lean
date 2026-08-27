import Proofs.Erdos85OrderFortyNineAutomaticDefectNonsingular
import Proofs.Erdos85OrderFortyNineDefectEigenvectors

/-! # Canonical mod-seven kernel vectors of the ordinary defect block -/

open SimpleGraph

namespace Erdos85

noncomputable section

def orderFortyNineOrdinaryDefectLInt
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj] :
    Matrix (Fin 46) (Fin 46) ℤ :=
  fun i j => 6 * (1 : Matrix (Fin 46) (Fin 46) ℤ) i j -
    (secondOrderDefectGraph G).adjMatrix ℤ
      (orderFortyNineOrdinaryVertex i) (orderFortyNineOrdinaryVertex j)

def orderFortyNineOrdinaryHighRowDifference
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    (x z : Fin 49) : Fin 46 → ℤ :=
  fun i => orderFortyNineHighRowDifference G x z
    (orderFortyNineOrdinaryVertex i)

private theorem orderFortyNine_not_defectAdj_of_high
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x, 7 ≤ G.degree x)
    {x y : Fin 49} (hx : G.degree x = 8) :
    ¬ (secondOrderDefectGraph G).Adj x y := by
  intro hxy
  have hzero := (orderFortyNine_degreeEight_defectDegree_and_neighborExcess_zero
    G hfree hmin (by decide) hx).1
  have hy : y ∈ (secondOrderDefectGraph G).neighborFinset x := by
    simpa [SimpleGraph.mem_neighborFinset] using hxy
  have hpos : 0 < (secondOrderDefectGraph G).degree x := by
    rw [← (secondOrderDefectGraph G).card_neighborFinset_eq_degree]
    exact Finset.card_pos.mpr ⟨y, hy⟩
  omega

/-- An ordinary restriction of a high-row difference is an exact
eigenvector of the integral defect block with eigenvalue seven.  Reduction
modulo seven therefore gives a kernel vector. -/
theorem orderFortyNineOrdinaryDefectLInt_mulVec_highRowDifference
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x, 7 ≤ G.degree x)
    (hhigh : ∀ y : Fin 49, G.degree y = 8 ↔ y.val < 3)
    {x z : Fin 49} (hx : G.degree x = 8) (hz : G.degree z = 8) :
    (orderFortyNineOrdinaryDefectLInt G).mulVec
        (orderFortyNineOrdinaryHighRowDifference G x z) =
      7 • orderFortyNineOrdinaryHighRowDifference G x z := by
  funext i
  have hfull := congrFun (orderFortyNine_defect_mulVec_highRowDifference
    G hfree hmin (by decide) hx hz) (orderFortyNineOrdinaryVertex i)
  simp only [Matrix.mulVec, dotProduct] at hfull ⊢
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ] at hfull
  have h0 : ¬ (secondOrderDefectGraph G).Adj (orderFortyNineOrdinaryVertex i) 0 := by
    simpa [(secondOrderDefectGraph G).adj_comm] using
      (orderFortyNine_not_defectAdj_of_high G hfree hmin
        (y := orderFortyNineOrdinaryVertex i) ((hhigh (0 : Fin 49)).2 (by decide)))
  have h1 : ¬ (secondOrderDefectGraph G).Adj (orderFortyNineOrdinaryVertex i) 1 := by
    simpa [(secondOrderDefectGraph G).adj_comm] using
      (orderFortyNine_not_defectAdj_of_high G hfree hmin
        (y := orderFortyNineOrdinaryVertex i) ((hhigh (1 : Fin 49)).2 (by decide)))
  have h2 : ¬ (secondOrderDefectGraph G).Adj (orderFortyNineOrdinaryVertex i) 2 := by
    simpa [(secondOrderDefectGraph G).adj_comm] using
      (orderFortyNine_not_defectAdj_of_high G hfree hmin
        (y := orderFortyNineOrdinaryVertex i) ((hhigh (2 : Fin 49)).2 (by decide)))
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
  rw [he1, he2] at hfull
  rw [hm0, hm1, hm2] at hfull
  simp only [zero_mul, zero_add] at hfull
  have hsucc (j : Fin 46) : j.succ.succ.succ = orderFortyNineOrdinaryVertex j := by
    apply Fin.ext
    simp [orderFortyNineOrdinaryVertex]
    omega
  simp_rw [hsucc] at hfull
  have hsum : (∑ j : Fin 46,
      (secondOrderDefectGraph G).adjMatrix ℤ
          (orderFortyNineOrdinaryVertex i) (orderFortyNineOrdinaryVertex j) *
        orderFortyNineOrdinaryHighRowDifference G x z j) =
      - orderFortyNineOrdinaryHighRowDifference G x z i := by
    simpa [orderFortyNineOrdinaryHighRowDifference,
      SimpleGraph.adjMatrix_apply] using hfull
  calc
    (∑ j, orderFortyNineOrdinaryDefectLInt G i j *
        orderFortyNineOrdinaryHighRowDifference G x z j) =
        6 * orderFortyNineOrdinaryHighRowDifference G x z i -
          ∑ j, (secondOrderDefectGraph G).adjMatrix ℤ
              (orderFortyNineOrdinaryVertex i) (orderFortyNineOrdinaryVertex j) *
            orderFortyNineOrdinaryHighRowDifference G x z j := by
      simp only [orderFortyNineOrdinaryDefectLInt, sub_mul,
        Finset.sum_sub_distrib]
      rw [Finset.sum_eq_single i]
      · simp
      · intro b _ hbi
        simp [Matrix.one_apply, Ne.symm hbi]
      · simp
    _ = 7 * orderFortyNineOrdinaryHighRowDifference G x z i := by rw [hsum]; ring
    _ = (7 • orderFortyNineOrdinaryHighRowDifference G x z) i := by simp

def orderFortyNineOrdinaryDefectLModSeven
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj] :
    Matrix (Fin 46) (Fin 46) (ZMod 7) :=
  (Int.castRingHom (ZMod 7)).mapMatrix (orderFortyNineOrdinaryDefectLInt G)

def orderFortyNineOrdinaryHighRowDifferenceModSeven
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    (x z : Fin 49) : Fin 46 → ZMod 7 :=
  fun i => (orderFortyNineOrdinaryHighRowDifference G x z i : ZMod 7)

theorem orderFortyNineOrdinaryDefectLModSeven_mulVec_highRowDifference_eq_zero
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x, 7 ≤ G.degree x)
    (hhigh : ∀ y : Fin 49, G.degree y = 8 ↔ y.val < 3)
    {x z : Fin 49} (hx : G.degree x = 8) (hz : G.degree z = 8) :
    (orderFortyNineOrdinaryDefectLModSeven G).mulVec
        (orderFortyNineOrdinaryHighRowDifferenceModSeven G x z) = 0 := by
  have hint := orderFortyNineOrdinaryDefectLInt_mulVec_highRowDifference
    G hfree hmin hhigh hx hz
  funext i
  have hi := congrFun hint i
  have hi' := congrArg (Int.castRingHom (ZMod 7)) hi
  simp [orderFortyNineOrdinaryDefectLModSeven,
    orderFortyNineOrdinaryHighRowDifferenceModSeven,
    Matrix.mulVec, dotProduct, RingHom.mapMatrix_apply] at hi' ⊢
  have hseven : (7 : ZMod 7) = 0 := by decide
  rw [hseven, zero_mul] at hi'
  exact hi'

end

end Erdos85

#print axioms Erdos85.orderFortyNineOrdinaryDefectLInt_mulVec_highRowDifference
#print axioms Erdos85.orderFortyNineOrdinaryDefectLModSeven_mulVec_highRowDifference_eq_zero
