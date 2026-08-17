import Proofs.Erdos85OrderSixtyFourDisconnectedDefect
import Proofs.Erdos85LaplacianCofactorBridge
import Mathlib.NumberTheory.PythagoreanTriples

/-! # Arithmetic payoff of the order-64 cofactor bridge -/

open SimpleGraph

namespace Erdos85

/-- If `a² = 64² q` over the integers, then `q` is an integer square.
The key integral step is that divisibility of the squares forces
`64 ∣ a`. -/
theorem isSquare_of_sq_eq_sixtyFour_sq_mul
    (a q : ℤ) (h : a ^ 2 = (64 : ℤ) ^ 2 * q) :
    IsSquare q := by
  have hpow : (64 : ℤ) ^ 2 ∣ a ^ 2 := by
    exact ⟨q, h⟩
  have hdiv : (64 : ℤ) ∣ a :=
    (Int.pow_dvd_pow_iff (by norm_num : (2 : ℕ) ≠ 0)).mp hpow
  obtain ⟨b, rfl⟩ := hdiv
  refine ⟨b, ?_⟩
  nlinarith

/-- Once the rank-one defect determinant has been identified as
`64² q` (in particular when `q` is a common Laplacian cofactor), the
adjacency square identity forces `q` to be a square. -/
theorem orderSixtyFour_defect_rank_one_quotient_isSquare
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hmin : ∀ x : Fin 64, 8 ≤ G.degree x)
    (hcover : ∀ {u v}, G.Adj u v →
      G.degree u = 8 ∨ G.degree v = 8)
    (q : ℤ)
    (hq :
      Matrix.det
        ((7 : ℤ) • (1 : Matrix (Fin 64) (Fin 64) ℤ) +
          FriendshipTheoremOQ01.onesMatrix (Fin 64) -
            (secondOrderDefectGraph G).adjMatrix ℤ) =
        (64 : ℤ) ^ 2 * q) :
    IsSquare q := by
  apply isSquare_of_sq_eq_sixtyFour_sq_mul
    (Matrix.det (G.adjMatrix ℤ)) q
  rw [orderSixtyFour_adj_det_sq_eq_defect_rank_one_det
    G hfree hmin hcover]
  exact hq

/-- The abstract cofactor bridge specialized to the integral defect
Laplacian at order 64. -/
theorem orderSixtyFour_defect_laplacian_cofactor_identity
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hmin : ∀ x : Fin 64, 8 ≤ G.degree x)
    (hcover : ∀ {u v}, G.Adj u v →
      G.degree u = 8 ∨ G.degree v = 8)
    (r : Fin 64) :
    Matrix.det
        ((7 : ℤ) • (1 : Matrix (Fin 64) (Fin 64) ℤ) +
          FriendshipTheoremOQ01.onesMatrix (Fin 64) -
            (secondOrderDefectGraph G).adjMatrix ℤ) =
      (64 : ℤ) ^ 2 *
        Matrix.det (((secondOrderDefectGraph G).lapMatrix ℤ).submatrix
          (fun x : rootReduced r => x.1)
          (fun x : rootReduced r => x.1)) := by
  let D := secondOrderDefectGraph G
  let LZ := D.lapMatrix ℤ
  let LQ := D.lapMatrix ℚ
  have hkernel := orderSixtyFour_regular_defect_kernel
    G hfree hmin hcover
  have hDreg : ∀ x : Fin 64, D.degree x = 7 := hkernel.2.2.1
  have hrow : ∀ i, ∑ j, LQ i j = 0 := by
    intro i
    have hz := congrFun
      (D.lapMatrix_mulVec_const_eq_zero (R := ℚ)) i
    simpa [LQ, Matrix.mulVec, dotProduct] using hz
  have hcol : ∀ j, ∑ i, LQ i j = 0 := by
    intro j
    calc
      ∑ i, LQ i j = ∑ i, LQ j i := by
        apply Finset.sum_congr rfl
        intro i _
        simpa [LQ] using (D.isSymm_lapMatrix ℚ).apply i j |>.symm
      _ = 0 := hrow j
  have hq := det_laplacian_add_ones_eq_card_sq_mul_minor r LQ hrow hcol
  have hmapL : LZ.map (Int.castRingHom ℚ) = LQ := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [LZ, LQ, SimpleGraph.lapMatrix, SimpleGraph.degMatrix,
        SimpleGraph.adjMatrix_apply]
    · simp [LZ, LQ, SimpleGraph.lapMatrix, SimpleGraph.degMatrix,
        SimpleGraph.adjMatrix_apply, hij]
  have hmapMinor :
      (LZ.submatrix (fun x : rootReduced r => x.1)
          (fun x : rootReduced r => x.1)).map (Int.castRingHom ℚ) =
        LQ.submatrix (fun x : rootReduced r => x.1)
          (fun x : rootReduced r => x.1) := by
    ext i j
    exact congrArg (fun M : Matrix (Fin 64) (Fin 64) ℚ => M i.1 j.1) hmapL
  have hmapPlus :
      (LZ + Matrix.of (fun _ _ => (1 : ℤ))).map (Int.castRingHom ℚ) =
        LQ + Matrix.of (fun _ _ => (1 : ℚ)) := by
    ext i j
    have hijmap :=
      congrArg (fun M : Matrix (Fin 64) (Fin 64) ℚ => M i j) hmapL
    simp only [Matrix.map_apply, Matrix.add_apply, Matrix.of_apply] at hijmap ⊢
    norm_num at hijmap ⊢
    linarith
  have hdetMinor :
      ((Matrix.det (LZ.submatrix
          (fun x : rootReduced r => x.1)
          (fun x : rootReduced r => x.1)) : ℤ) : ℚ) =
        Matrix.det (LQ.submatrix
          (fun x : rootReduced r => x.1)
          (fun x : rootReduced r => x.1)) := by
    rw [← hmapMinor]
    exact RingHom.map_det (Int.castRingHom ℚ)
      (LZ.submatrix (fun x : rootReduced r => x.1)
        (fun x : rootReduced r => x.1))
  have hqcast :
      ((Matrix.det
          (LZ + Matrix.of (fun _ _ => (1 : ℤ))) : ℤ) : ℚ) =
        ((64 : ℤ) ^ 2 *
          Matrix.det (LZ.submatrix
            (fun x : rootReduced r => x.1)
            (fun x : rootReduced r => x.1)) : ℤ) := by
    calc
      ((Matrix.det
          (LZ + Matrix.of (fun _ _ => (1 : ℤ))) : ℤ) : ℚ) =
          Matrix.det ((LZ + Matrix.of (fun _ _ => (1 : ℤ))).map
            (Int.castRingHom ℚ)) :=
        RingHom.map_det (Int.castRingHom ℚ)
          (LZ + Matrix.of (fun _ _ => (1 : ℤ)))
      _ = Matrix.det (LQ + Matrix.of (fun _ _ => (1 : ℚ))) := by
        rw [hmapPlus]
      _ = (64 : ℚ) ^ 2 *
          Matrix.det (LQ.submatrix
            (fun x : rootReduced r => x.1)
            (fun x : rootReduced r => x.1)) := by simpa using hq
      _ = ((64 : ℤ) ^ 2 *
          Matrix.det (LZ.submatrix
            (fun x : rootReduced r => x.1)
            (fun x : rootReduced r => x.1)) : ℤ) := by
        rw [Int.cast_mul, Int.cast_pow, Int.cast_ofNat, hdetMinor]
  have hint :
      Matrix.det (LZ + Matrix.of (fun _ _ => (1 : ℤ))) =
        (64 : ℤ) ^ 2 *
          Matrix.det (LZ.submatrix
            (fun x : rootReduced r => x.1)
            (fun x : rootReduced r => x.1)) := by
    exact_mod_cast hqcast
  rw [← hint]
  congr 1
  ext i j
  simp only [LZ, SimpleGraph.lapMatrix, SimpleGraph.degMatrix,
    Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply,
    Matrix.one_apply, Matrix.diagonal_apply, Matrix.of_apply,
    FriendshipTheoremOQ01.onesMatrix, smul_eq_mul]
  by_cases hij : i = j
  · subst j
    simp [hDreg i, SimpleGraph.adjMatrix_apply]
  · by_cases hadj : D.Adj i j <;>
      simp [D, hij, hadj, SimpleGraph.adjMatrix_apply]

/-- Therefore every principal integral defect-Laplacian cofactor is a
square. -/
theorem orderSixtyFour_defect_laplacian_cofactor_isSquare
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hmin : ∀ x : Fin 64, 8 ≤ G.degree x)
    (hcover : ∀ {u v}, G.Adj u v →
      G.degree u = 8 ∨ G.degree v = 8)
    (r : Fin 64) :
    IsSquare
      (Matrix.det (((secondOrderDefectGraph G).lapMatrix ℤ).submatrix
        (fun x : rootReduced r => x.1)
        (fun x : rootReduced r => x.1))) := by
  apply orderSixtyFour_defect_rank_one_quotient_isSquare
    G hfree hmin hcover
  exact orderSixtyFour_defect_laplacian_cofactor_identity
    G hfree hmin hcover r

end Erdos85
