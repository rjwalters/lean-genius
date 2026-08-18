import Proofs.Erdos85SevenRegularNearTwinCommutingGraphBalance

/-! # Owner-row collisions propagate across a defect near-twin -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- If a commuting graph gives identical rows to a near-twin pair, it also
gives identical rows to the two private neighbors of that pair. -/
theorem sevenRegular_nearTwin_commutingGraph_rowCollision_propagates
    {V : Type*} [Fintype V] [DecidableEq V]
    (D R : SimpleGraph V) [DecidableRel D.Adj] [DecidableRel R.Adj]
    (hreg : ∀ v, D.degree v = 7)
    {x y : V}
    (hcommon : (D.neighborFinset x ∩ D.neighborFinset y).card = 6)
    (hcomm : D.adjMatrix ℤ * R.adjMatrix ℤ =
      R.adjMatrix ℤ * D.adjMatrix ℤ)
    (hxy : ∀ w : V, R.adjMatrix ℤ x w = R.adjMatrix ℤ y w) :
    ∃ p q : V, p ≠ q ∧
      ∀ z : V, R.adjMatrix ℤ p z = R.adjMatrix ℤ q z := by
  obtain ⟨p, q, hpq, hbalance⟩ :=
    sevenRegular_nearTwin_commutingGraph_signed_balance
      D R hreg hcommon hcomm
  refine ⟨p, q, hpq, ?_⟩
  intro z
  have h := hbalance z
  have hzero :
      (∑ w : V,
        (R.adjMatrix ℤ x w - R.adjMatrix ℤ y w) * D.adjMatrix ℤ w z) = 0 := by
    apply Finset.sum_eq_zero
    intro w _hw
    rw [hxy w, sub_self, zero_mul]
  rw [hzero] at h
  omega

/-- Order-64 component-owner specialization of collision propagation. -/
theorem orderSixtyFour_nearTwin_ownerGraph_rowCollision_propagates
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
      (secondOrderDefectGraph G).neighborFinset y).card = 6)
    (hxy : ∀ w : Fin 64,
      (componentOwnerGraph G (secondOrderDefectGraph G) c).adjMatrix ℤ x w =
      (componentOwnerGraph G (secondOrderDefectGraph G) c).adjMatrix ℤ y w) :
    ∃ p q : Fin 64, p ≠ q ∧ ∀ z : Fin 64,
      (componentOwnerGraph G (secondOrderDefectGraph G) c).adjMatrix ℤ p z =
      (componentOwnerGraph G (secondOrderDefectGraph G) c).adjMatrix ℤ q z := by
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
  exact sevenRegular_nearTwin_commutingGraph_rowCollision_propagates
    D R hDreg hcommon hcomm hxy

end

end Erdos85
