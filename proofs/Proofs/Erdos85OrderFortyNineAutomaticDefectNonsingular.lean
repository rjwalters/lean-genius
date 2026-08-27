import Proofs.Erdos85OrderFortyNineGroundedDefectNonsingular
import Proofs.Erdos85OrderFortyNineHighIncidenceCensus

/-! # Automatic nonsingularity of the canonical order-49 defect block -/

open SimpleGraph

namespace Erdos85

noncomputable section

local instance orderFortyNineOrdinaryDefectGraph_decidableAdj_auto
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj] :
    DecidableRel (orderFortyNineOrdinaryDefectGraph G).Adj :=
  Classical.decRel _

theorem orderFortyNineOrdinaryDefectGraph_degree_le_full
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (i : Fin 46) :
    (orderFortyNineOrdinaryDefectGraph G).degree i ≤
      (secondOrderDefectGraph G).degree (orderFortyNineOrdinaryVertex i) := by
  rw [← (orderFortyNineOrdinaryDefectGraph G).card_neighborFinset_eq_degree,
    ← (secondOrderDefectGraph G).card_neighborFinset_eq_degree]
  apply Finset.card_le_card_of_injOn orderFortyNineOrdinaryVertex
  · intro j hj
    have hadj : (orderFortyNineOrdinaryDefectGraph G).Adj i j := by
      simpa [SimpleGraph.mem_neighborFinset] using hj
    simpa [orderFortyNineOrdinaryDefectGraph,
      SimpleGraph.mem_neighborFinset] using hadj
  · intro j hj k hk hjk
    exact (Fin.natAdd_inj 3).mp hjk

theorem orderFortyNineOrdinaryDefectGraph_degree_le_six
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x, 7 ≤ G.degree x)
    (hhigh : ∀ x : Fin 49, G.degree x = 8 ↔ x.val < 3)
    (i : Fin 46) :
    (orderFortyNineOrdinaryDefectGraph G).degree i ≤ 6 := by
  let f := orderFortyNineOrdinaryVertex
  have hi7 : G.degree (f i) = 7 := by
    rcases orderFortyNine_degree_eq_seven_or_eight
        G hfree hmin (by decide) (f i) with hi | hi
    · exact hi
    · have := (hhigh (f i)).1 hi
      simp [f, orderFortyNineOrdinaryVertex] at this
  have hfull := orderFortyNine_defectDegree_add_highNeighborCount_eq_six
    G hfree hmin (by decide) hi7
  have hsub := orderFortyNineOrdinaryDefectGraph_degree_le_full G i
  have hfullle0 : (secondOrderDefectGraph G).degree
      (orderFortyNineOrdinaryVertex i) ≤ 6 := by
    change (secondOrderDefectGraph G).degree (orderFortyNineOrdinaryVertex i) +
      (G.neighborFinset (orderFortyNineOrdinaryVertex i) ∩
        orderFortyNineHighVertices G).card = 6 at hfull
    omega
  exact hsub.trans hfullle0

theorem orderFortyNineOrdinary_highNeighborCount_eq_zero_of_defectDegree_six
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x, 7 ≤ G.degree x)
    (hhigh : ∀ x : Fin 49, G.degree x = 8 ↔ x.val < 3)
    {i : Fin 46}
    (hi : (orderFortyNineOrdinaryDefectGraph G).degree i = 6) :
    (G.neighborFinset (orderFortyNineOrdinaryVertex i) ∩
      orderFortyNineHighVertices G).card = 0 := by
  have hi7 : G.degree (orderFortyNineOrdinaryVertex i) = 7 := by
    rcases orderFortyNine_degree_eq_seven_or_eight
        G hfree hmin (by decide) (orderFortyNineOrdinaryVertex i) with h | h
    · exact h
    · have hh := (hhigh _).1 h
      simp [orderFortyNineOrdinaryVertex] at hh
  have hbudget := orderFortyNine_defectDegree_add_highNeighborCount_eq_six
    G hfree hmin (by decide) hi7
  have hle := orderFortyNineOrdinaryDefectGraph_degree_le_full G i
  omega

theorem orderFortyNineOrdinaryDefectGraph_grounded
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x, 7 ≤ G.degree x)
    (hhigh : ∀ x : Fin 49, G.degree x = 8 ↔ x.val < 3) :
    ∀ i, ∃ j, (orderFortyNineOrdinaryDefectGraph G).Reachable i j ∧
      (orderFortyNineOrdinaryDefectGraph G).degree j < 6 := by
  let D0 := orderFortyNineOrdinaryDefectGraph G
  let D := secondOrderDefectGraph G
  let f := orderFortyNineOrdinaryVertex
  intro i
  by_contra hnone
  push_neg at hnone
  let c := D0.connectedComponentMk i
  let C0 : Finset (Fin 46) := c.supp.toFinset
  let C : Finset (Fin 49) := C0.image f
  let H : Finset (Fin 49) := Finset.univ.filter fun x => x.val < 3
  have hreach_of_mem {j : Fin 46} (hj : j ∈ C0) : D0.Reachable i j := by
    have hjc : D0.connectedComponentMk j = c := by
      exact (ConnectedComponent.mem_supp_iff c j).mp (by simpa [C0] using hj)
    exact ConnectedComponent.exact hjc.symm
  have hdeg6 {j : Fin 46} (hj : j ∈ C0) : D0.degree j = 6 := by
    have hle := orderFortyNineOrdinaryDefectGraph_degree_le_six
      G hfree hmin hhigh j
    change D0.degree j ≤ 6 at hle
    have hnlt : 6 ≤ D0.degree j := hnone j (hreach_of_mem hj)
    omega
  have hHcard : H.card = 3 := by
    dsimp [H]
    decide
  have hiC0 : i ∈ C0 := by
    simp [C0, c, ConnectedComponent.mem_supp_iff]
  have hCpos : 0 < C.card := by
    rw [Finset.card_pos]
    exact ⟨f i, Finset.mem_image.mpr ⟨i, hiC0, rfl⟩⟩
  apply false_of_threeHigh_ungrounded_sixRegular_defect_set
    G hfree (by decide) H C hHcard hCpos
  · intro x hx
    rw [Finset.card_eq_zero]
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro y hy
    have hxy := (Finset.mem_inter.mp hy).1
    obtain ⟨j, hjC0, rfl⟩ := Finset.mem_image.mp (Finset.mem_inter.mp hy).2
    have hz := orderFortyNineOrdinary_highNeighborCount_eq_zero_of_defectDegree_six
      G hfree hmin hhigh (hdeg6 hjC0)
    have hxmem : x ∈ G.neighborFinset (f j) ∩ orderFortyNineHighVertices G := by
      apply Finset.mem_inter.mpr
      constructor
      · have hAdj : G.Adj x (f j) := (G.mem_neighborFinset x (f j)).mp hxy
        exact (G.mem_neighborFinset (f j) x).mpr hAdj.symm
      · have hxlt : x.val < 3 := (Finset.mem_filter.mp hx).2
        simp [orderFortyNineHighVertices, (hhigh x).2 hxlt]
    have hzpos : 0 < (G.neighborFinset (f j) ∩
        orderFortyNineHighVertices G).card := Finset.card_pos.mpr ⟨x, hxmem⟩
    change (G.neighborFinset (f j) ∩ orderFortyNineHighVertices G).card = 0 at hz
    omega
  · intro y hy
    obtain ⟨j, hjC0, rfl⟩ := Finset.mem_image.mp hy
    rcases orderFortyNine_degree_eq_seven_or_eight
        G hfree hmin (by decide) (f j) with h | h
    · exact h
    · have hh := (hhigh (f j)).1 h
      simp [f, orderFortyNineOrdinaryVertex] at hh
  · intro y hy
    obtain ⟨j, hjC0, rfl⟩ := Finset.mem_image.mp hy
    have hj6 := hdeg6 hjC0
    have hzero := orderFortyNineOrdinary_highNeighborCount_eq_zero_of_defectDegree_six
      G hfree hmin hhigh hj6
    have hj7 : G.degree (f j) = 7 := by
      rcases orderFortyNine_degree_eq_seven_or_eight
          G hfree hmin (by decide) (f j) with h | h
      · exact h
      · have hh := (hhigh (f j)).1 h
        simp [f, orderFortyNineOrdinaryVertex] at hh
    have hbudget := orderFortyNine_defectDegree_add_highNeighborCount_eq_six
      G hfree hmin (by decide) hj7
    have hDdegree : D.degree (f j) = 6 := by
      dsimp [D, f] at hbudget ⊢
      omega
    apply Nat.le_antisymm
    · calc
        ((D.neighborFinset (f j) ∩ C).card) ≤ (D.neighborFinset (f j)).card :=
          Finset.card_le_card Finset.inter_subset_left
        _ = D.degree (f j) := D.card_neighborFinset_eq_degree (f j)
        _ = 6 := hDdegree
    · rw [← hj6, ← D0.card_neighborFinset_eq_degree]
      apply Finset.card_le_card_of_injOn f
      · intro k hk
        have hjk : D0.Adj j k := (D0.mem_neighborFinset j k).mp hk
        apply Finset.mem_inter.mpr
        constructor
        · exact (D.mem_neighborFinset (f j) (f k)).mpr (by
            simpa [D0, D, orderFortyNineOrdinaryDefectGraph, f] using hjk)
        · apply Finset.mem_image.mpr
          refine ⟨k, ?_, rfl⟩
          have hjSupp : j ∈ c.supp := by simpa [C0] using hjC0
          have hkSupp : k ∈ c.supp :=
            (c.mem_supp_congr_adj hjk).mp hjSupp
          simpa [C0] using hkSupp
      · intro k hk l hl hkl
        exact (Fin.natAdd_inj 3).mp hkl

theorem orderFortyNineOrdinaryDefectL_isUnit
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x, 7 ≤ G.degree x)
    (hhigh : ∀ x : Fin 49, G.degree x = 8 ↔ x.val < 3) :
    IsUnit (orderFortyNineOrdinaryDefectL G).det := by
  apply orderFortyNineOrdinaryDefectL_isUnit_of_grounded G
  · exact orderFortyNineOrdinaryDefectGraph_degree_le_six G hfree hmin hhigh
  · exact orderFortyNineOrdinaryDefectGraph_grounded G hfree hmin hhigh

/-- The exact Schur expression is automatically forty-nine times an integer
square: the former nonsingularity hypothesis is discharged by groundedness. -/
theorem orderFortyNine_threeHigh_defect_T_eq_fortyNine_mul_intSquare_auto
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x, 7 ≤ G.degree x)
    (hcover : ∀ {u v}, G.Adj u v → G.degree u = 7 ∨ G.degree v = 7)
    (hhigh : ∀ x : Fin 49, G.degree x = 8 ↔ x.val < 3) :
    ∃ q : ℤ,
      10 * (orderFortyNineOrdinaryDefectL G).det +
          7 * dotProduct orderFortyNineOneVector
            ((orderFortyNineOrdinaryDefectL G).adjugate.mulVec
              orderFortyNineOneVector) =
        49 * (q : ℚ) ^ 2 := by
  apply orderFortyNine_threeHigh_defect_T_eq_fortyNine_mul_intSquare
    G hfree hmin hcover hhigh
  exact orderFortyNineOrdinaryDefectL_isUnit G hfree hmin hhigh

end

end Erdos85

#print axioms Erdos85.orderFortyNineOrdinaryDefectGraph_degree_le_six
#print axioms Erdos85.orderFortyNineOrdinaryDefectGraph_degree_le_full
#print axioms Erdos85.orderFortyNineOrdinary_highNeighborCount_eq_zero_of_defectDegree_six
#print axioms Erdos85.orderFortyNineOrdinaryDefectGraph_grounded
#print axioms Erdos85.orderFortyNineOrdinaryDefectL_isUnit
#print axioms Erdos85.orderFortyNine_threeHigh_defect_T_eq_fortyNine_mul_intSquare_auto
