import Proofs.Erdos85OrderSixtyFourAllTwoTriangleLedger
import Proofs.Erdos85OrderSixtyFourRegularPartition

/-! # Triangle ledger for an order-64 defect component and its complement -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- A 7-regular graph on 16 vertices and its complement have complementary
cube traces summing to `672`. -/
theorem trace_adjMatrix_cube_add_compl_eq_672
    {W : Type*} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj]
    [DecidableRel Hᶜ.Adj]
    (hcard : Fintype.card W = 16)
    (hreg : ∀ x, H.degree x = 7) :
    Matrix.trace (H.adjMatrix ℤ * H.adjMatrix ℤ * H.adjMatrix ℤ) +
      Matrix.trace (Hᶜ.adjMatrix ℤ * Hᶜ.adjMatrix ℤ * Hᶜ.adjMatrix ℤ) =
        672 := by
  let A := H.adjMatrix ℤ
  let C := Hᶜ.adjMatrix ℤ
  let J : Matrix W W ℤ := Matrix.of fun _ _ => 1
  have hC : C = J - 1 - A := by
    ext x y
    by_cases hxy : x = y
    · subst y
      simp [A, C, J, SimpleGraph.adjMatrix_apply]
    · by_cases hAdj : H.Adj x y
      · simp [A, C, J, SimpleGraph.adjMatrix_apply, hxy, hAdj]
      · simp [A, C, J, SimpleGraph.adjMatrix_apply, hxy, hAdj]
  have hAJ : A * J = (7 : ℤ) • J := by
    ext x y
    rw [Matrix.mul_apply]
    simp only [A, J, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, mul_one]
    have hx := SimpleGraph.adjMatrix_mulVec_const_apply
      (G := H) (α := ℤ) (a := (1 : ℤ)) (v := x)
    rw [hreg x] at hx
    simpa [Matrix.mulVec, dotProduct] using hx
  have hJA : J * A = (7 : ℤ) • J := by
    have ht := congrArg Matrix.transpose hAJ
    have hAT : A.transpose = A := H.isSymm_adjMatrix.eq
    have hJT : J.transpose = J := by rfl
    simpa only [Matrix.transpose_mul, hAT, hJT, Matrix.transpose_smul] using ht
  have hJJ : J * J = (16 : ℤ) • J := by
    ext x y
    simp [J, Matrix.mul_apply, hcard]
  have hAAJ : A * A * J = (49 : ℤ) • J := by
    rw [Matrix.mul_assoc, hAJ, Matrix.mul_smul, hAJ, smul_smul]
    norm_num
  have hJAA : J * A * A = (49 : ℤ) • J := by
    rw [hJA, Matrix.smul_mul, hJA, smul_smul]
    norm_num
  have hcube : C * C * C =
      (64 : ℤ) • J - (1 : Matrix W W ℤ) -
        (3 : ℤ) • A - (3 : ℤ) • (A * A) - A * A * A := by
    rw [hC]
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one]
    rw [hAJ, hJA, hJJ]
    simp only [hJA, hJJ, hAAJ, Matrix.smul_mul, smul_smul]
    module
  have htrA : Matrix.trace A = 0 := SimpleGraph.trace_adjMatrix ℤ H
  have htrA2 : Matrix.trace (A * A) = 112 := by
    have h := FriendshipTheoremOQ01.trace_adjMatrix_sq H 7 hreg
    rw [hcard] at h
    norm_num at h
    simpa [A] using h
  have htrJ : Matrix.trace J = 16 := by
    simp [J, Matrix.trace, Matrix.diag, hcard]
  have htrI : Matrix.trace (1 : Matrix W W ℤ) = 16 := by
    simp [Matrix.trace, Matrix.diag, hcard]
  rw [hcube, Matrix.trace_sub, Matrix.trace_sub, Matrix.trace_sub,
    Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_smul,
    Matrix.trace_smul, htrJ, htrI, htrA, htrA2]
  ring

/-- Every size-16 defect component in the order-64 regular four-component
branch and its graph complement contain exactly `112` triangles in total. -/
theorem orderSixtyFour_defectComponent_compl_triangleMinorCount_sum
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hreg : ∀ x, G.degree x = 8)
    (hcount : Fintype.card
      (secondOrderDefectGraph G).ConnectedComponent = 4)
    (c : (secondOrderDefectGraph G).ConnectedComponent) :
    let H := (secondOrderDefectGraph G).induce c.supp
    (adjacencyTriangleMinorFinset H).card +
      (adjacencyTriangleMinorFinset Hᶜ).card = 112 := by
  classical
  let H := (secondOrderDefectGraph G).induce c.supp
  change (adjacencyTriangleMinorFinset H).card +
    (adjacencyTriangleMinorFinset Hᶜ).card = 112
  have hc := orderSixtyFour_regular_four_defectComponents_all_orderSixteen
    G hfree hreg hcount c
  have hcardH : Fintype.card c.supp = 16 := by
    rw [show Fintype.card c.supp = c.supp.ncard by
      simpa [Nat.card_eq_fintype_card] using Nat.card_coe_set_eq c.supp]
    exact hc
  have hregH : ∀ x, H.degree x = 7 := by
    intro x
    change ((secondOrderDefectGraph G).induce c.supp).degree x = 7
    exact binarySquare_regular_inducedDefectComponent_degree
      G hfree (q := 8) (by omega) hreg (by decide) c x
  have htrace := trace_adjMatrix_cube_add_compl_eq_672 H hcardH hregH
  have hH := trace_adjMatrix_cube_eq_six_mul_triangleMinorCount H (by omega)
  have hC := trace_adjMatrix_cube_eq_six_mul_triangleMinorCount Hᶜ (by omega)
  rw [hH, hC] at htrace
  norm_cast at htrace
  omega

end

end Erdos85
