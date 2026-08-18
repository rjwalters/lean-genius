import Proofs.Erdos85SevenRegularCodegreeFourCommutingBalance
import Proofs.Erdos85AlternatingFourthMoment
import Proofs.Erdos85BinarySquareRegularParity

/-! # Unit-three owner overlap bound for codegree-four pairs -/

open SimpleGraph

namespace Erdos85

noncomputable section

private theorem adjMatrix_sum_le_card_codegreeFour
    {V : Type*} [Fintype V] [DecidableEq V]
    (R : SimpleGraph V) [DecidableRel R.Adj]
    (S : Finset V) (z : V) :
    0 ≤ ∑ s ∈ S, R.adjMatrix ℤ s z ∧
      (∑ s ∈ S, R.adjMatrix ℤ s z) ≤ S.card := by
  constructor
  · apply Finset.sum_nonneg
    intro s _hs
    rw [SimpleGraph.adjMatrix_apply]
    split <;> norm_num
  · calc
      (∑ s ∈ S, R.adjMatrix ℤ s z) ≤ ∑ _s ∈ S, (1 : ℤ) := by
        apply Finset.sum_le_sum
        intro s _hs
        rw [SimpleGraph.adjMatrix_apply]
        split <;> norm_num
      _ = S.card := by simp

/-- Every graph commuting with `D` has overlap imbalance at most three on a
codegree-four pair. -/
theorem sevenRegular_codegreeFour_commutingGraph_overlapDifference_le_three
    {V : Type*} [Fintype V] [DecidableEq V]
    (D R : SimpleGraph V) [DecidableRel D.Adj] [DecidableRel R.Adj]
    (hreg : ∀ v, D.degree v = 7)
    {x y : V}
    (hcommon : (D.neighborFinset x ∩ D.neighborFinset y).card = 4)
    (hcomm : D.adjMatrix ℤ * R.adjMatrix ℤ =
      R.adjMatrix ℤ * D.adjMatrix ℤ) :
    ∀ z : V,
      |((R.neighborFinset x ∩ D.neighborFinset z).card : ℤ) -
        ((R.neighborFinset y ∩ D.neighborFinset z).card : ℤ)| ≤ 3 := by
  obtain ⟨P, Q, hP, hQ, _hdisj, hbalance⟩ :=
    sevenRegular_codegreeFour_commuting_privateSums D hreg hcommon
  intro z
  have h := hbalance (R.adjMatrix ℤ) hcomm z
  have hsum :
      (∑ w : V,
        (R.adjMatrix ℤ x w - R.adjMatrix ℤ y w) * D.adjMatrix ℤ w z) =
      ((R.neighborFinset x ∩ D.neighborFinset z).card : ℤ) -
        ((R.neighborFinset y ∩ D.neighborFinset z).card : ℤ) := by
    calc
      _ = (R.adjMatrix ℤ * D.adjMatrix ℤ) x z -
          (R.adjMatrix ℤ * D.adjMatrix ℤ) y z := by
        rw [Matrix.mul_apply, Matrix.mul_apply, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro w _hw
        rw [sub_mul]
      _ = _ := by
        rw [adjMatrix_mul_subgraph_apply_eq_card_mixed,
          adjMatrix_mul_subgraph_apply_eq_card_mixed]
  rw [hsum] at h
  have hPb := adjMatrix_sum_le_card_codegreeFour R P z
  have hQb := adjMatrix_sum_le_card_codegreeFour R Q z
  rw [hP] at hPb
  rw [hQ] at hQb
  rw [← h]
  apply abs_le.mpr
  constructor <;> omega

/-- Direct order-64 owner specialization. -/
theorem orderSixtyFour_codegreeFour_ownerGraph_overlapDifference_le_three
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hreg : ∀ x, G.degree x = 8)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hc : c.supp.ncard = 16)
    {x y : Fin 64}
    (hcommon : ((secondOrderDefectGraph G).neighborFinset x ∩
      (secondOrderDefectGraph G).neighborFinset y).card = 4) :
    ∀ z : Fin 64,
      |(((componentOwnerGraph G (secondOrderDefectGraph G) c).neighborFinset x ∩
          (secondOrderDefectGraph G).neighborFinset z).card : ℤ) -
        (((componentOwnerGraph G (secondOrderDefectGraph G) c).neighborFinset y ∩
          (secondOrderDefectGraph G).neighborFinset z).card : ℤ)| ≤ 3 := by
  let D := secondOrderDefectGraph G
  let R := componentOwnerGraph G D c
  have hcensus : Fintype.card (Fin 64) = 8 * (8 - 1) + 3 + (8 - 3) := by
    norm_num
  have hDreg : ∀ z : Fin 64, D.degree z = 7 := by
    intro z
    have h := secondOrderDefectGraph_degree_eq_excess_add_two
      G hfree hreg hcensus z
    change D.degree z = (8 - 3) + 2 at h
    norm_num at h ⊢
    exact h
  have hcomm : D.adjMatrix ℤ * R.adjMatrix ℤ =
      R.adjMatrix ℤ * D.adjMatrix ℤ := by
    symm
    exact binarySquare_regular_componentOwnerGraph_adjMatrix_comm_defect
      G hfree (q := 8) (by omega) hreg (by norm_num) c (m_c := 2) (by
        norm_num
        exact hc)
  exact sevenRegular_codegreeFour_commutingGraph_overlapDifference_le_three
    D R hDreg hcommon hcomm

end

end Erdos85
