import Proofs.Erdos85OrderFortyNineDefectHighAffine

/-! # The forced four-dimensional sector of the order-49 defect block -/

open SimpleGraph

namespace Erdos85

noncomputable section

local instance orderFortyNineOrdinaryDefectGraph_decidableAdj_forcedSector
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj] :
    DecidableRel (orderFortyNineOrdinaryDefectGraph G).Adj :=
  Classical.decRel _

/-- The number (over the integers) of the three high roots adjacent to an
ordinary vertex. -/
def orderFortyNineOrdinaryHighSupportCountInt
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj] : Fin 46 → ℤ :=
  fun i => ∑ h : Fin 3,
    G.adjMatrix ℤ (Fin.castAdd 46 h) (orderFortyNineOrdinaryVertex i)

theorem orderFortyNineOrdinaryHighSupportCountInt_eq_card
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    (hhigh : ∀ y : Fin 49, G.degree y = 8 ↔ y.val < 3)
    (i : Fin 46) :
    orderFortyNineOrdinaryHighSupportCountInt G i =
      ((G.neighborFinset (orderFortyNineOrdinaryVertex i) ∩
        orderFortyNineHighVertices G).card : ℤ) := by
  have hH : orderFortyNineHighVertices G = {0, 1, 2} := by
    ext y
    simp [orderFortyNineHighVertices, hhigh]
    omega
  rw [hH]
  simp only [orderFortyNineOrdinaryHighSupportCountInt,
    SimpleGraph.adjMatrix_apply, Finset.sum_ite,
    Finset.sum_const_zero, Finset.sum_const, nsmul_eq_mul, mul_one]
  simp only [add_zero]
  norm_cast
  change ((Finset.univ : Finset (Fin 3)).filter fun h =>
      G.Adj (Fin.castAdd 46 h) (orderFortyNineOrdinaryVertex i)).card = _
  apply Finset.card_bij (fun h _ => Fin.castAdd 46 h)
  · intro h hh
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hh
    simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset,
      Finset.mem_insert, Finset.mem_singleton]
    refine ⟨hh.symm, ?_⟩
    fin_cases h <;> simp
  · intro a ha b hb hab
    apply Fin.ext
    have hv := congrArg Fin.val hab
    simpa using hv
  · intro y hy
    simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset,
      Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy.2 with rfl | rfl | rfl
    · refine ⟨0, ?_, by decide⟩
      simpa using hy.1.symm
    · refine ⟨1, ?_, by decide⟩
      simpa using hy.1.symm
    · refine ⟨2, ?_, by decide⟩
      simpa using hy.1.symm

/-- Summing the three absolute perfect-code equations gives `D₀ s = 3·1-s`.
This is one half of the forced invariant sector used in the determinant
quotient. -/
theorem orderFortyNineOrdinaryDefectAdjInt_mulVec_highSupportCount
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x, 7 ≤ G.degree x)
    (hhigh : ∀ y : Fin 49, G.degree y = 8 ↔ y.val < 3) :
    (orderFortyNineOrdinaryDefectAdjInt G).mulVec
        (orderFortyNineOrdinaryHighSupportCountInt G) =
      fun i => 3 - orderFortyNineOrdinaryHighSupportCountInt G i := by
  have hh (h : Fin 3) : G.degree (Fin.castAdd 46 h) = 8 :=
    (hhigh _).2 (by simp)
  have heq (h : Fin 3) :=
    orderFortyNineOrdinaryDefectAdjInt_mulVec_highIncidence
      G hfree hmin hhigh (hh h)
  funext i
  simp only [Matrix.mulVec, dotProduct,
    orderFortyNineOrdinaryHighSupportCountInt]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Eq.trans (Finset.sum_congr rfl fun h _ => congrFun (heq h) i)
  simp [orderFortyNineOrdinaryHighIncidenceInt]

theorem orderFortyNineOrdinaryDefectGraph_degree_eq_full
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x, 7 ≤ G.degree x)
    (hhigh : ∀ y : Fin 49, G.degree y = 8 ↔ y.val < 3)
    (i : Fin 46) :
    (orderFortyNineOrdinaryDefectGraph G).degree i =
      (secondOrderDefectGraph G).degree (orderFortyNineOrdinaryVertex i) := by
  apply Nat.le_antisymm (orderFortyNineOrdinaryDefectGraph_degree_le_full G i)
  rw [← (secondOrderDefectGraph G).card_neighborFinset_eq_degree,
    ← (orderFortyNineOrdinaryDefectGraph G).card_neighborFinset_eq_degree]
  have hord {y : Fin 49}
      (hy : y ∈ (secondOrderDefectGraph G).neighborFinset
        (orderFortyNineOrdinaryVertex i)) : 3 ≤ y.val := by
    by_contra hylt
    have hy8 : G.degree y = 8 := (hhigh y).2 (by omega)
    have hzero := (orderFortyNine_degreeEight_defectDegree_and_neighborExcess_zero
      G hfree hmin (by decide) hy8).1
    have hadj : (secondOrderDefectGraph G).Adj
        (orderFortyNineOrdinaryVertex i) y := by
      simpa [SimpleGraph.mem_neighborFinset] using hy
    have hpos : 0 < (secondOrderDefectGraph G).degree y := by
      rw [← (secondOrderDefectGraph G).card_neighborFinset_eq_degree]
      exact Finset.card_pos.mpr ⟨_, by
        simpa [SimpleGraph.mem_neighborFinset,
          (secondOrderDefectGraph G).adj_comm] using hadj⟩
    omega
  let f : Fin 49 → Fin 46 := fun y => ⟨y.val - 3, by omega⟩
  apply Finset.card_le_card_of_injOn f
  · intro y hy
    have hadj : (secondOrderDefectGraph G).Adj
        (orderFortyNineOrdinaryVertex i) y := by
      simpa [SimpleGraph.mem_neighborFinset] using hy
    have hfy : orderFortyNineOrdinaryVertex (f y) = y := by
      apply Fin.ext
      simp [f, orderFortyNineOrdinaryVertex]
      have hy3 : 3 ≤ y.val := hord hy
      omega
    simpa [SimpleGraph.mem_neighborFinset, orderFortyNineOrdinaryDefectGraph,
      hfy] using hadj
  · intro y hy z hz hyz
    apply Fin.ext
    have := congrArg Fin.val hyz
    dsimp [f] at this
    have hy3 : 3 ≤ y.val := hord hy
    have hz3 : 3 ≤ z.val := hord hz
    omega

/-- The other half of the forced invariant sector: the row sum of the
ordinary defect adjacency matrix is `6-s`. -/
theorem orderFortyNineOrdinaryDefectAdjInt_mulVec_one
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x, 7 ≤ G.degree x)
    (hhigh : ∀ y : Fin 49, G.degree y = 8 ↔ y.val < 3) :
    (orderFortyNineOrdinaryDefectAdjInt G).mulVec (fun _ => 1) =
      fun i => 6 - orderFortyNineOrdinaryHighSupportCountInt G i := by
  funext i
  have hi7 : G.degree (orderFortyNineOrdinaryVertex i) = 7 := by
    rcases orderFortyNine_degree_eq_seven_or_eight G hfree hmin (by decide)
        (orderFortyNineOrdinaryVertex i) with hi | hi
    · exact hi
    · have := (hhigh _).1 hi
      simp [orderFortyNineOrdinaryVertex] at this
  have hbudget := orderFortyNine_defectDegree_add_highNeighborCount_eq_six
    G hfree hmin (by decide) hi7
  have hbudgetInt :
      ((secondOrderDefectGraph G).degree
          (orderFortyNineOrdinaryVertex i) : ℤ) +
        ((G.neighborFinset (orderFortyNineOrdinaryVertex i) ∩
          orderFortyNineHighVertices G).card : ℤ) = 6 := by
    exact_mod_cast hbudget
  rw [← orderFortyNineOrdinaryHighSupportCountInt_eq_card G hhigh i,
    ← orderFortyNineOrdinaryDefectGraph_degree_eq_full
      G hfree hmin hhigh i] at hbudgetInt
  change ((orderFortyNineOrdinaryDefectGraph G).adjMatrix ℤ).mulVec
      (fun _ => 1) i = _
  rw [SimpleGraph.adjMatrix_mulVec_apply]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [(orderFortyNineOrdinaryDefectGraph G).card_neighborFinset_eq_degree]
  omega

end

end Erdos85

#print axioms Erdos85.orderFortyNineOrdinaryDefectAdjInt_mulVec_highSupportCount
#print axioms Erdos85.orderFortyNineOrdinaryDefectAdjInt_mulVec_one
