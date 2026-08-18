import Proofs.Erdos85OrderSixtyFourOwnerResidualExact
import Proofs.Erdos85LaplacianCofactorBridge

/-!
# Cofactor value of the exact owner residual

Evaluating the canonical degree-16 owner residual at `-2` gives the
determinant of the component Gram `L+J`.  The Laplacian cofactor identity
then supplies the exact factor `16² = 256`.
-/

open SimpleGraph Polynomial

namespace Erdos85

noncomputable section

/-- The canonical owner residual evaluated at `-2` is `256` times every
principal reduced-Laplacian determinant of the size-16 defect component. -/
theorem orderSixtyFour_sizeSixteen_ownerResidual_eval_negTwo_eq_cofactor
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hc : c.supp.ncard = 16)
    (root : c.supp) :
    Polynomial.eval (-2 : ℝ)
        ((((secondOrderDefectGraph G).induce c.supp).lapMatrix ℝ +
          Matrix.of (fun _ _ => (1 : ℝ))).charpoly.comp
            (X + C (2 : ℝ))) =
      256 *
        (Matrix.det
          ((((secondOrderDefectGraph G).induce c.supp).lapMatrix ℚ).submatrix
            (fun x : rootReduced root => x.1)
            (fun x : rootReduced root => x.1)) : ℚ) := by
  let H := (secondOrderDefectGraph G).induce c.supp
  let LQ := H.lapMatrix ℚ
  let LR := H.lapMatrix ℝ
  let JQ : Matrix c.supp c.supp ℚ := Matrix.of fun _ _ => 1
  let JR : Matrix c.supp c.supp ℝ := Matrix.of fun _ _ => 1
  have hcs : Fintype.card c.supp = 16 := by
    rw [Set.fintypeCard_eq_ncard]
    exact hc
  have hrow : ∀ i, ∑ j, LQ i j = 0 := by
    intro i
    have hz := congrFun (H.lapMatrix_mulVec_const_eq_zero (R := ℚ)) i
    simpa [LQ, Matrix.mulVec, dotProduct] using hz
  have hcol : ∀ j, ∑ i, LQ i j = 0 := by
    intro j
    calc
      ∑ i, LQ i j = ∑ i, LQ j i := by
        apply Finset.sum_congr rfl
        intro i _
        simpa [LQ] using (H.isSymm_lapMatrix ℚ).apply i j |>.symm
      _ = 0 := hrow j
  have hcofactor :=
    det_laplacian_add_ones_eq_card_sq_mul_minor root LQ hrow hcol
  rw [hcs] at hcofactor
  norm_num at hcofactor
  have hmapL : LQ.map (Rat.castHom ℝ) = LR := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [LQ, LR, SimpleGraph.lapMatrix, SimpleGraph.degMatrix,
        SimpleGraph.adjMatrix_apply]
    · by_cases hadj : H.Adj i j <;>
        simp [LQ, LR, SimpleGraph.lapMatrix, SimpleGraph.degMatrix,
          SimpleGraph.adjMatrix_apply, hij, hadj]
  have hmapQ : (LQ + JQ).map (Rat.castHom ℝ) = LR + JR := by
    ext i j
    have hij := congrArg (fun M : Matrix c.supp c.supp ℝ => M i j) hmapL
    simp only [Matrix.map_apply] at hij
    change ((LQ i j : ℚ) : ℝ) = LR i j at hij
    change (((LQ i j + 1 : ℚ) : ℝ)) = LR i j + 1
    norm_num
    rw [hij]
  have hdetCast : Matrix.det (LR + JR) =
      ((Matrix.det (LQ + JQ) : ℚ) : ℝ) := by
    rw [← hmapQ]
    simpa using (RingHom.map_det (Rat.castHom ℝ) (LQ + JQ)).symm
  have hevalZero : Polynomial.eval (0 : ℝ) (LR + JR).charpoly =
      Matrix.det (LR + JR) := by
    have hdet := Matrix.det_eq_sign_charpoly_coeff (LR + JR)
    rw [hcs] at hdet
    norm_num at hdet
    simpa [Polynomial.coeff_zero_eq_eval_zero] using hdet.symm
  change Polynomial.eval (-2 : ℝ)
      ((LR + JR).charpoly.comp (X + C (2 : ℝ))) = _
  rw [Polynomial.eval_comp]
  norm_num
  rw [hevalZero, hdetCast]
  exact_mod_cast hcofactor

end

end Erdos85
