import Proofs.Erdos85NonregularDefectOperator

/-! Fifth-trace algebra with a nonconstant diagonal correction. The numerical
q7 specialization consumes the remaining graph degree/mixed-trace identities. -/
namespace Erdos85
open Matrix
variable {V : Type*} [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
/-- Reversing a symmetric triple preserves its trace. -/
theorem trace_symmetric_triple_swap (A B C : Matrix V V ℤ)
    (hA : A.transpose = A) (hB : B.transpose = B) (hC : C.transpose = C) :
    Matrix.trace (A * B * C) = Matrix.trace (A * C * B) := by
  calc
    _ = Matrix.trace ((A * B * C).transpose) := (Matrix.trace_transpose _).symm
    _ = Matrix.trace (C * (B * A)) := by
      rw [Matrix.transpose_mul, Matrix.transpose_mul, hA, hB, hC]
    _ = _ := by
      rw [Matrix.trace_mul_comm C (B * A), Matrix.mul_assoc,
        Matrix.trace_mul_comm B (A * C)]

/-- Unlike the regular formula, K may vary along the diagonal. -/
theorem trace_fifth_eq_of_nonregular_square
    (A K J D : Matrix V V ℤ) (n : ℤ)
    (hA : A.transpose = A) (hK : K.transpose = K)
    (hJ : J.transpose = J) (hD : D.transpose = D)
    (hsq : A * A = K + J - D)
    (hJJ : J * J = n • J)
    (hAKK : Matrix.trace (A * K * K) = 0) :
    Matrix.trace (A ^ 5) = n * Matrix.trace (A * J) +
      2 * Matrix.trace (A * K * J) - 2 * Matrix.trace (A * D * J) -
      2 * Matrix.trace (A * K * D) + Matrix.trace (A * D * D) := by
  have hword : A ^ 5 = A * ((A * A) * (A * A)) := by noncomm_ring
  have hraw : A * ((K + J - D) * (K + J - D)) =
      A * K * K + A * K * J + A * J * K + A * (J * J) -
      A * K * D - A * D * K - A * J * D - A * D * J + A * D * D := by
    noncomm_ring
  rw [hword, hsq, hraw, hJJ, Matrix.mul_smul]
  simp only [Matrix.trace_add, Matrix.trace_sub, Matrix.trace_smul, smul_eq_mul]
  rw [hAKK, trace_symmetric_triple_swap A J K hA hJ hK,
    trace_symmetric_triple_swap A D K hA hD hK,
    trace_symmetric_triple_swap A J D hA hJ hD]
  ring

/-- Numerical q7 specialization; graph facts supplying these traces remain
explicit hypotheses rather than a claimed graph-to-degree-count bridge. -/
theorem q7_fifth_trace_of_nonregular_trace_data
    (A K J D : Matrix V V ℤ) (h T R : ℤ)
    (hA : A.transpose = A) (hK : K.transpose = K)
    (hJ : J.transpose = J) (hD : D.transpose = D)
    (hsq : A * A = K + J - D) (hJJ : J * J = (49 : ℤ) • J)
    (hAKK : Matrix.trace (A * K * K) = 0)
    (hAJ : Matrix.trace (A * J) = 343 + h)
    (hAKJ : Matrix.trace (A * K * J) = 2058 + 14*h)
    (hADJ : Matrix.trace (A * D * J) = 2058 - 98*h)
    (hAKD : Matrix.trace (A * K * D) = 2058 - 138*h - 36*T)
    (hADD : Matrix.trace (A * D * D) = R) :
    Matrix.trace (A ^ 5) = 12691 + 549*h + 72*T + R := by
  rw [trace_fifth_eq_of_nonregular_square A K J D 49 hA hK hJ hD hsq hJJ hAKK,
    hAJ, hAKJ, hADJ, hAKD, hADD]
  ring
/-- Actual nonregular graph expansion, with degree sums exposed. -/
theorem c4Free_nonregular_fifth_trace_degree_expansion
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) :
    let A := G.adjMatrix ℤ
    let D := (secondOrderDefectGraph G).adjMatrix ℤ
    let K := degreePredDiagonal G
    Matrix.trace (A ^ 5) =
      (Fintype.card V : ℤ) * (∑ v, (G.degree v : ℤ)) +
      2 * (∑ v, (G.degree v : ℤ) * ((G.degree v : ℤ) - 1)) -
      2 * (∑ v, (G.degree v : ℤ) * ((secondOrderDefectGraph G).degree v : ℤ)) -
      2 * Matrix.trace (A * K * D) + Matrix.trace (A * D * D) := by
  classical
  let A := G.adjMatrix ℤ
  let D := (secondOrderDefectGraph G).adjMatrix ℤ
  let K := degreePredDiagonal G
  let J := FriendshipTheoremOQ01.onesMatrix V
  have hA : A.transpose = A := by
    ext i j
    simp [A, Matrix.transpose_apply, SimpleGraph.adjMatrix_apply, G.adj_comm]
  have hD : D.transpose = D := by
    ext i j
    simp [D, Matrix.transpose_apply, SimpleGraph.adjMatrix_apply, SimpleGraph.adj_comm]
  have hK : K.transpose = K := by simp [K, degreePredDiagonal]
  have hJ : J.transpose = J := by
    ext i j
    simp [J, FriendshipTheoremOQ01.onesMatrix, Matrix.transpose_apply]
  have hAKK : Matrix.trace (A * K * K) = 0 := by
    simp [Matrix.trace, Matrix.diag, K, degreePredDiagonal, Matrix.mul_diagonal,
      A, SimpleGraph.adjMatrix_apply]
  have hAJ : Matrix.trace (A * J) = ∑ v, (G.degree v : ℤ) := by
    simp only [Matrix.trace, Matrix.diag, A, J,
      adjMatrix_mul_onesMatrix_apply_eq_degree]
  have hAKJ : Matrix.trace (A * K * J) =
      ∑ v, (G.degree v : ℤ) * ((G.degree v : ℤ) - 1) := by
    rw [trace_symmetric_triple_swap A K J hA hK hJ]
    simp only [Matrix.trace, Matrix.diag, K, degreePredDiagonal, Matrix.mul_diagonal,
      A, J, adjMatrix_mul_onesMatrix_apply_eq_degree]
  have hADJ : Matrix.trace (A * D * J) =
      ∑ v, (G.degree v : ℤ) * ((secondOrderDefectGraph G).degree v : ℤ) := by
    rw [trace_symmetric_triple_swap A D J hA hD hJ]
    apply Finset.sum_congr rfl
    intro v _
    change (A * J * D) v v = _
    rw [Matrix.mul_apply]
    simp only [A, J, adjMatrix_mul_onesMatrix_apply_eq_degree]
    rw [← Finset.mul_sum]
    congr 1
    simpa [Matrix.mul_apply, FriendshipTheoremOQ01.onesMatrix, D] using
      (onesMatrix_mul_adjMatrix_apply_eq_degree (secondOrderDefectGraph G) v v)
  have hb := trace_fifth_eq_of_nonregular_square A K J D (Fintype.card V)
    hA hK hJ hD
    (adjMatrix_sq_eq_degreePredDiagonal_add_ones_sub_secondOrderDefect G hfree)
    FriendshipTheoremOQ01.onesMatrix_sq hAKK
  rw [hAJ, hAKJ, hADJ] at hb
  exact hb
end Erdos85
