import Proofs.Erdos85SevenRegularNearTwinLiteCommutingBalance
import Proofs.Erdos85AlternatingFourthMoment

/-! # Unit-two owner overlap bound for codegree-five pairs -/

open SimpleGraph

namespace Erdos85

noncomputable section

private theorem adjMatrix_sum_le_card
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

/-- For a codegree-five pair, every graph commuting with `D` has owner-overlap
imbalance at most two on every defect neighborhood. -/
theorem sevenRegular_codegreeFive_commutingGraph_overlapDifference_le_two
    {V : Type*} [Fintype V] [DecidableEq V]
    (D R : SimpleGraph V) [DecidableRel D.Adj] [DecidableRel R.Adj]
    (hreg : ∀ v, D.degree v = 7)
    {x y : V}
    (hcommon : (D.neighborFinset x ∩ D.neighborFinset y).card = 5)
    (hcomm : D.adjMatrix ℤ * R.adjMatrix ℤ =
      R.adjMatrix ℤ * D.adjMatrix ℤ) :
    ∀ z : V,
      |((R.neighborFinset x ∩ D.neighborFinset z).card : ℤ) -
        ((R.neighborFinset y ∩ D.neighborFinset z).card : ℤ)| ≤ 2 := by
  obtain ⟨P, Q, hP, hQ, _hdisj, hbalance⟩ :=
    sevenRegular_codegreeFive_commuting_privateSums D hreg hcommon
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
  have hPb := adjMatrix_sum_le_card R P z
  have hQb := adjMatrix_sum_le_card R Q z
  rw [hP] at hPb
  rw [hQ] at hQb
  rw [← h]
  apply abs_le.mpr
  constructor <;> omega

end

end Erdos85
