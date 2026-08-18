import Proofs.Erdos85OrderSixtyFourAllTwoTriangleLedger

/-!
# Coupling the four owner residuals to the defect polynomial

In the order-64 all-two stratum, the four owner residual third coefficients
and the defect characteristic polynomial's third coefficient have a fixed,
graph-independent sum.  This eliminates the intermediate triangle counts.
-/

open SimpleGraph Polynomial

namespace Erdos85

noncomputable section

/-- **Owner/defect third-coefficient coupling.**  Simultaneously choose the
four monic degree-16 owner residuals.  Besides their individual leading
coefficients, their degree-13 coefficients and the defect's degree-61
characteristic coefficient sum to the constant `-463232`. -/
theorem orderSixtyFour_all_sizeSixteen_exists_ownerResiduals_coupled_to_defect
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (hreg : ∀ x, G.degree x = 8)
    (hcard : Fintype.card V = 64)
    (hm : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      c.supp.ncard = 16) :
    ∃ r : (secondOrderDefectGraph G).ConnectedComponent → ℝ[X],
      (∀ c, (r c).Monic ∧ (r c).natDegree = 16 ∧
        ((componentOwnerGraph G
          (secondOrderDefectGraph G) c).adjMatrix ℝ).charpoly =
            (X + C (2 : ℝ)) ^ 48 * r c ∧
        (r c).coeff 15 = -96 ∧ (r c).coeff 14 = 4256 ∧
        (r c).coeff 13 = -113792 - 2 *
          (adjacencyTriangleMinorFinset
            (componentOwnerGraph G (secondOrderDefectGraph G) c)).card) ∧
      (∑ c, (r c).coeff 13) +
        ((secondOrderDefectGraph G).adjMatrix ℚ).charpoly.coeff 61 =
          -463232 := by
  let D := secondOrderDefectGraph G
  have hres : ∀ c : D.ConnectedComponent, ∃ r : ℝ[X],
      r.Monic ∧ r.natDegree = 16 ∧
      ((componentOwnerGraph G D c).adjMatrix ℝ).charpoly =
        (X + C (2 : ℝ)) ^ 48 * r ∧
      r.coeff 15 = -96 ∧ r.coeff 14 = 4256 ∧
      r.coeff 13 = -113792 - 2 *
        (adjacencyTriangleMinorFinset (componentOwnerGraph G D c)).card := by
    intro c
    exact orderSixtyFour_sizeSixteen_componentOwnerGraph_exists_residual_thirdCoefficient
      G hfree hreg hcard c (hm c)
  choose r hr using hres
  refine ⟨r, hr, ?_⟩
  have hccard : Fintype.card D.ConnectedComponent = 4 :=
    orderSixtyFour_card_defectComponents_eq_four_of_all_sizeSixteen
      D hcard hm
  have htri :=
    orderSixtyFour_all_sizeSixteen_owner_defect_triangleMinorCount_eq
      G hfree hreg hcard hm
  have hDcoeff : (D.adjMatrix ℚ).charpoly.coeff 61 =
      -2 * (adjacencyTriangleMinorFinset D).card := by
    have h := adjMatrix_charpoly_thirdCoeff_eq_neg_two_mul_triangleMinorCount
      D (by simpa [hcard] : 3 ≤ Fintype.card V)
    rw [hcard] at h
    norm_num at h
    ring_nf at h ⊢
    exact h
  have hsum : (∑ c, (r c).coeff 13) =
      -455168 - 2 *
        (∑ c : D.ConnectedComponent,
          (adjacencyTriangleMinorFinset (componentOwnerGraph G D c)).card) := by
    simp_rw [(hr _).2.2.2.2.2]
    rw [Finset.sum_sub_distrib]
    simp only [Finset.sum_const, Finset.card_univ, hccard]
    rw [← Finset.mul_sum]
    norm_num
  have htriR :
      ((∑ c : D.ConnectedComponent,
        (adjacencyTriangleMinorFinset (componentOwnerGraph G D c)).card : ℕ) : ℝ) +
        ((adjacencyTriangleMinorFinset D).card : ℝ) = 4032 := by
    exact_mod_cast htri
  dsimp [D] at hr ⊢
  rw [hsum, hDcoeff]
  push_cast
  dsimp [D] at htriR
  push_cast at htriR
  linarith

end

end Erdos85
