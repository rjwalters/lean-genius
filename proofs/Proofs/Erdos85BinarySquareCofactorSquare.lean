import Proofs.Erdos85BinarySquareCenteredAdjacencyRank
import Proofs.Erdos85LaplacianCofactorBridge
import Mathlib.NumberTheory.PythagoreanTriples

/-!
# Square-order defect cofactors are squares

At square order the defect Laplacian satisfies `L_D + J = A²`.  The
rank-one Laplacian determinant identity therefore makes every principal
cofactor of `L_D` an integer square.  This is the uniform version of the
previously order-64-only cofactor-square result.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Integral cancellation of a nonzero square factor. -/
theorem isSquare_of_sq_eq_sq_mul
    (a n c : ℤ) (hn : n ≠ 0) (h : a ^ 2 = n ^ 2 * c) :
    IsSquare c := by
  have hpow : n ^ 2 ∣ a ^ 2 := ⟨c, h⟩
  have hdiv : n ∣ a :=
    (Int.pow_dvd_pow_iff (by norm_num : (2 : ℕ) ≠ 0)).mp hpow
  obtain ⟨b, rfl⟩ := hdiv
  refine ⟨b, ?_⟩
  have hn2 : n ^ 2 ≠ 0 := pow_ne_zero 2 hn
  apply (mul_left_cancel₀ hn2)
  nlinarith

/-- For a regular C4-free graph on `q²` vertices, every principal cofactor of
the integral second-order-defect Laplacian is a square.  Equivalently, when
the defect graph is connected, its number of spanning trees is a square. -/
theorem binarySquare_defect_laplacian_cofactor_isSquare
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (r : V) :
    IsSquare
      (Matrix.det (((secondOrderDefectGraph G).lapMatrix ℤ).submatrix
        (fun x : rootReduced r => x.1)
        (fun x : rootReduced r => x.1))) := by
  letI : Nonempty V := ⟨r⟩
  let A := G.adjMatrix ℤ
  let D := secondOrderDefectGraph G
  let LZ := D.lapMatrix ℤ
  let LQ := D.lapMatrix ℚ
  let JZ : Matrix V V ℤ := Matrix.of fun _ _ => 1
  have hcensus : Fintype.card V = q * (q - 1) + 3 + (q - 3) := by
    rw [hcard]
    calc
      q * q = q * ((q - 1) + 1) := by
        rw [Nat.sub_add_cancel (by omega : 1 ≤ q)]
      _ = q * (q - 1) + q := by ring
      _ = q * (q - 1) + 3 + (q - 3) := by omega
  have hDreg : ∀ x, D.degree x = q - 1 := by
    intro x
    have h := secondOrderDefectGraph_degree_eq_excess_add_two
      G hfree hreg hcensus x
    change D.degree x = (q - 3) + 2 at h
    omega
  have hA2 : A * A = LZ + JZ := by
    rw [adjMatrix_sq_eq_sub_secondOrderDefect_of_regular G hfree hreg]
    ext i j
    simp only [LZ, JZ, D, SimpleGraph.lapMatrix, SimpleGraph.degMatrix,
      Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply,
      Matrix.one_apply, Matrix.diagonal_apply, Matrix.of_apply,
      FriendshipTheoremOQ01.onesMatrix, smul_eq_mul]
    by_cases hij : i = j
    · subst j
      simp only
      rw [hDreg i, Nat.cast_sub (by omega : 1 ≤ q)]
      norm_num
    · simp only [if_neg hij, mul_zero, zero_add]
      ring
  have hrow : ∀ i, ∑ j, LQ i j = 0 := by
    intro i
    have hz := congrFun (D.lapMatrix_mulVec_const_eq_zero (R := ℚ)) i
    simpa [LQ, Matrix.mulVec, dotProduct] using hz
  have hcol : ∀ j, ∑ i, LQ i j = 0 := by
    intro j
    calc
      ∑ i, LQ i j = ∑ i, LQ j i := by
        apply Finset.sum_congr rfl
        intro i _
        simpa [LQ] using (D.isSymm_lapMatrix ℚ).apply i j |>.symm
      _ = 0 := hrow j
  have hcofactor :=
    det_laplacian_add_ones_eq_card_sq_mul_minor r LQ hrow hcol
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
    exact congrArg (fun M : Matrix V V ℚ => M i.1 j.1) hmapL
  have hminorCast :
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
  have hmapPlus :
      (LZ + JZ).map (Int.castRingHom ℚ) =
        LQ + Matrix.of (fun _ _ => (1 : ℚ)) := by
    ext i j
    have hijmap := congrArg (fun M : Matrix V V ℚ => M i j) hmapL
    simp only [Matrix.map_apply, Matrix.add_apply, Matrix.of_apply,
      JZ] at hijmap ⊢
    norm_num at hijmap ⊢
    exact hijmap
  have hdetPlus :
      Matrix.det (LZ + JZ) =
        (Fintype.card V : ℤ) ^ 2 *
          Matrix.det (LZ.submatrix
            (fun x : rootReduced r => x.1)
            (fun x : rootReduced r => x.1)) := by
    have hcast :
        ((Matrix.det (LZ + JZ) : ℤ) : ℚ) =
          ((Fintype.card V : ℤ) ^ 2 *
            Matrix.det (LZ.submatrix
              (fun x : rootReduced r => x.1)
              (fun x : rootReduced r => x.1)) : ℤ) := by
      calc
        ((Matrix.det (LZ + JZ) : ℤ) : ℚ) =
            Matrix.det ((LZ + JZ).map (Int.castRingHom ℚ)) :=
          RingHom.map_det (Int.castRingHom ℚ) (LZ + JZ)
        _ = Matrix.det (LQ + Matrix.of (fun _ _ => (1 : ℚ))) := by
          rw [hmapPlus]
        _ = (Fintype.card V : ℚ) ^ 2 *
            Matrix.det (LQ.submatrix
              (fun x : rootReduced r => x.1)
              (fun x : rootReduced r => x.1)) := hcofactor
        _ = ((Fintype.card V : ℤ) ^ 2 *
            Matrix.det (LZ.submatrix
              (fun x : rootReduced r => x.1)
              (fun x : rootReduced r => x.1)) : ℤ) := by
          rw [Int.cast_mul, Int.cast_pow, hminorCast]
          norm_cast
    exact_mod_cast hcast
  apply isSquare_of_sq_eq_sq_mul
    (Matrix.det A) (Fintype.card V)
    (Matrix.det (LZ.submatrix
      (fun x : rootReduced r => x.1)
      (fun x : rootReduced r => x.1)))
  · exact_mod_cast (Fintype.card_ne_zero : Fintype.card V ≠ 0)
  · rw [pow_two, ← Matrix.det_mul, hA2, hdetPlus]

end

end Erdos85
