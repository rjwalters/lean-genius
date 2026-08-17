import Proofs.Erdos85SevenRegularNearTwinCommutingPropagation
import Proofs.Erdos85BinarySquareRegularParity

/-! # Commuting graph balance forced by a near-twin pair -/

open SimpleGraph

namespace Erdos85

noncomputable section

private theorem sum_signed_two_singletons
    {V : Type*} [Fintype V] [DecidableEq V]
    (f : V → ℤ) (p q : V) :
    (∑ w : V, ((if w = p then 1 else 0) - (if w = q then 1 else 0)) * f w) =
      f p - f q := by
  classical
  simp_rw [sub_mul]
  rw [Finset.sum_sub_distrib]
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ,
    if_true]

/-- If a graph `R` commutes with a seven-regular graph `D`, then a six-common-
neighbor pair `x,y` of `D` forces a signed balance identity in every column of
`R`.  The left side only sees the two private neighbors `p,q`; the right side
is supported on the `D`-neighbors of the column vertex. -/
theorem sevenRegular_nearTwin_commutingGraph_signed_balance
    {V : Type*} [Fintype V] [DecidableEq V]
    (D R : SimpleGraph V) [DecidableRel D.Adj] [DecidableRel R.Adj]
    (hreg : ∀ v, D.degree v = 7)
    {x y : V}
    (hcommon : (D.neighborFinset x ∩ D.neighborFinset y).card = 6)
    (hcomm : D.adjMatrix ℤ * R.adjMatrix ℤ =
      R.adjMatrix ℤ * D.adjMatrix ℤ) :
    ∃ p q : V, p ≠ q ∧ ∀ z : V,
      R.adjMatrix ℤ p z - R.adjMatrix ℤ q z =
        ∑ w : V,
          (R.adjMatrix ℤ x w - R.adjMatrix ℤ y w) * D.adjMatrix ℤ w z := by
  obtain ⟨p, q, hpq, hbalance⟩ :=
    sevenRegular_nearTwin_commuting_signed_balance D hreg hcommon
  refine ⟨p, q, hpq, ?_⟩
  intro z
  have h := hbalance (R.adjMatrix ℤ) hcomm z
  rw [sum_signed_two_singletons (fun w => R.adjMatrix ℤ w z) p q] at h
  exact h

/-- Actual order-64 owner-color specialization.  A near-twin pair in the
seven-regular second-order defect graph imposes the signed balance on every
size-sixteen component owner graph. -/
theorem orderSixtyFour_nearTwin_ownerGraph_signed_balance
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
    ∃ p q : Fin 64, p ≠ q ∧ ∀ z : Fin 64,
      (componentOwnerGraph G (secondOrderDefectGraph G) c).adjMatrix ℤ p z -
          (componentOwnerGraph G (secondOrderDefectGraph G) c).adjMatrix ℤ q z =
        ∑ w : Fin 64,
          ((componentOwnerGraph G (secondOrderDefectGraph G) c).adjMatrix ℤ x w -
            (componentOwnerGraph G (secondOrderDefectGraph G) c).adjMatrix ℤ y w) *
              (secondOrderDefectGraph G).adjMatrix ℤ w z := by
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
  exact sevenRegular_nearTwin_commutingGraph_signed_balance
    D R hDreg hcommon hcomm

end

end Erdos85
