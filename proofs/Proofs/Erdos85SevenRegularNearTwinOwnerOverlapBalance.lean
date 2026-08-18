import Proofs.Erdos85SevenRegularNearTwinCommutingGraphBalance
import Proofs.Erdos85AlternatingFourthMoment

/-! # Near twins force unit overlap imbalance in every commuting graph -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Combinatorial form of near-twin commutation.  For every target `z`, the
difference between the numbers of `R`-neighbors of `x` and `y` lying in the
defect neighborhood of `z` is exactly the difference of two Boolean entries,
at the private neighbors `p,q`.  In particular its absolute size is at most
one. -/
theorem sevenRegular_nearTwin_commutingGraph_overlapDifference_eq_private
    {V : Type*} [Fintype V] [DecidableEq V]
    (D R : SimpleGraph V) [DecidableRel D.Adj] [DecidableRel R.Adj]
    (hreg : ∀ v, D.degree v = 7)
    {x y : V}
    (hcommon : (D.neighborFinset x ∩ D.neighborFinset y).card = 6)
    (hcomm : D.adjMatrix ℤ * R.adjMatrix ℤ =
      R.adjMatrix ℤ * D.adjMatrix ℤ) :
    ∃ p q : V, p ≠ q ∧ ∀ z : V,
      ((R.neighborFinset x ∩ D.neighborFinset z).card : ℤ) -
          ((R.neighborFinset y ∩ D.neighborFinset z).card : ℤ) =
        R.adjMatrix ℤ p z - R.adjMatrix ℤ q z := by
  obtain ⟨p, q, hpq, hbalance⟩ :=
    sevenRegular_nearTwin_commutingGraph_signed_balance
      D R hreg hcommon hcomm
  refine ⟨p, q, hpq, ?_⟩
  intro z
  have h := hbalance z
  have hsum :
      (∑ w : V,
        (R.adjMatrix ℤ x w - R.adjMatrix ℤ y w) * D.adjMatrix ℤ w z) =
      (R.adjMatrix ℤ * D.adjMatrix ℤ) x z -
        (R.adjMatrix ℤ * D.adjMatrix ℤ) y z := by
    rw [Matrix.mul_apply, Matrix.mul_apply, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro w _hw
    rw [sub_mul]
  rw [hsum, adjMatrix_mul_subgraph_apply_eq_card_mixed,
    adjMatrix_mul_subgraph_apply_eq_card_mixed] at h
  exact h.symm

/-- The corresponding overlap-cardinality difference lies in `[-1,1]`. -/
theorem sevenRegular_nearTwin_commutingGraph_overlapDifference_le_one
    {V : Type*} [Fintype V] [DecidableEq V]
    (D R : SimpleGraph V) [DecidableRel D.Adj] [DecidableRel R.Adj]
    (hreg : ∀ v, D.degree v = 7)
    {x y : V}
    (hcommon : (D.neighborFinset x ∩ D.neighborFinset y).card = 6)
    (hcomm : D.adjMatrix ℤ * R.adjMatrix ℤ =
      R.adjMatrix ℤ * D.adjMatrix ℤ) :
    ∀ z : V,
      |((R.neighborFinset x ∩ D.neighborFinset z).card : ℤ) -
        ((R.neighborFinset y ∩ D.neighborFinset z).card : ℤ)| ≤ 1 := by
  obtain ⟨p, q, _hpq, hbalance⟩ :=
    sevenRegular_nearTwin_commutingGraph_overlapDifference_eq_private
      D R hreg hcommon hcomm
  intro z
  rw [hbalance z]
  rw [SimpleGraph.adjMatrix_apply, SimpleGraph.adjMatrix_apply]
  split_ifs <;> norm_num

/-- Direct order-64 owner-color form of the unit overlap imbalance. -/
theorem orderSixtyFour_nearTwin_ownerGraph_overlapDifference_le_one
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
      (secondOrderDefectGraph G).neighborFinset y).card = 6) :
    ∀ z : Fin 64,
      |(((componentOwnerGraph G (secondOrderDefectGraph G) c).neighborFinset x ∩
          (secondOrderDefectGraph G).neighborFinset z).card : ℤ) -
        (((componentOwnerGraph G (secondOrderDefectGraph G) c).neighborFinset y ∩
          (secondOrderDefectGraph G).neighborFinset z).card : ℤ)| ≤ 1 := by
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
  exact sevenRegular_nearTwin_commutingGraph_overlapDifference_le_one
    D R hDreg hcommon hcomm

end

end Erdos85
