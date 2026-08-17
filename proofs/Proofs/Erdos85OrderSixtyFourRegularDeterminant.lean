import Proofs.Erdos85OrderSixtyFourRegularKernel

/-! # Determinant identities at the order-64 regular endpoint -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- At the endpoint the square of the adjacency determinant is exactly the
determinant of the rank-one lift of the defect Laplacian. -/
theorem orderSixtyFour_adj_det_sq_eq_defect_rank_one_det
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hmin : ∀ x : Fin 64, 8 ≤ G.degree x)
    (hcover : ∀ {u v}, G.Adj u v →
      G.degree u = 8 ∨ G.degree v = 8) :
    Matrix.det (G.adjMatrix ℤ) ^ 2 =
      Matrix.det
        ((7 : ℤ) • (1 : Matrix (Fin 64) (Fin 64) ℤ) +
          FriendshipTheoremOQ01.onesMatrix (Fin 64) -
            (secondOrderDefectGraph G).adjMatrix ℤ) := by
  have hkernel := orderSixtyFour_regular_defect_kernel
    G hfree hmin hcover
  rw [pow_two, ← Matrix.det_mul, hkernel.2.2.2]

/-- The unlifted defect Laplacian `7I-D` is singular: its kernel contains
the all-ones vector.  Thus the endpoint lies exactly on the singular
boundary where strict diagonal dominance ceases. -/
theorem orderSixtyFour_defect_laplacian_det_eq_zero
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hmin : ∀ x : Fin 64, 8 ≤ G.degree x)
    (hcover : ∀ {u v}, G.Adj u v →
      G.degree u = 8 ∨ G.degree v = 8) :
    Matrix.det
      ((7 : ℤ) • (1 : Matrix (Fin 64) (Fin 64) ℤ) -
        (secondOrderDefectGraph G).adjMatrix ℤ) = 0 := by
  let D := secondOrderDefectGraph G
  let B := (7 : ℤ) • (1 : Matrix (Fin 64) (Fin 64) ℤ) - D.adjMatrix ℤ
  have hkernel := orderSixtyFour_regular_defect_kernel
    G hfree hmin hcover
  have hDreg : ∀ x : Fin 64, D.degree x = 7 := hkernel.2.2.1
  have hBones : B.mulVec (fun _ => (1 : ℤ)) = 0 := by
    dsimp only [B]
    funext x
    simp only [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
      Pi.sub_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul, mul_one,
      sub_eq_zero]
    change (7 : ℤ) =
      (D.adjMatrix ℤ).mulVec (Function.const (Fin 64) (1 : ℤ)) x
    rw [SimpleGraph.adjMatrix_mulVec_const_apply, mul_one, hDreg x]
    norm_num
  have hones_ne : (fun _ : Fin 64 => (1 : ℤ)) ≠ 0 := by
    intro h
    have := congrFun h 0
    norm_num at this
  change B.det = 0
  exact Matrix.exists_mulVec_eq_zero_iff.mp ⟨_, hones_ne, hBones⟩

end

end Erdos85
