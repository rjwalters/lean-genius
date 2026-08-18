import Proofs.Erdos85OrderSixtyFourDefectSecondMoment

/-! # Second moment of a six-shifted regular graph -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- On sixteen vertices, `6I` plus the adjacency matrix of a six-regular
simple graph has trace `96` and square trace `672`.  This is the spectral
ledger for an H16 exterior Gram matrix once its off-diagonal pair layer has
been identified as a six-regular simple graph. -/
theorem six_add_sixRegularAdj_trace_and_secondMoment
    {V : Type*} [Fintype V] [DecidableEq V]
    (R : SimpleGraph V) [DecidableRel R.Adj]
    (hcard : Fintype.card V = 16)
    (hreg : ∀ x, R.degree x = 6) :
    let Q := (6 : ℂ) • (1 : Matrix V V ℂ) + R.adjMatrix ℂ
    Matrix.trace Q = 96 ∧ Matrix.trace (Q * Q) = 672 := by
  let A := R.adjMatrix ℂ
  let Q := (6 : ℂ) • (1 : Matrix V V ℂ) + A
  have htraceA : Matrix.trace A = 0 := by
    simp [A, Matrix.trace, Matrix.diag, SimpleGraph.adjMatrix_apply]
  have htraceA2 : Matrix.trace (A * A) = 96 := by
    dsimp [A]
    rw [trace_adjMatrix_sq_complex_eq_sum_degrees]
    simp [hreg, hcard]
    norm_num
  have htraceI : Matrix.trace (1 : Matrix V V ℂ) = 16 := by
    simp [Matrix.trace_one, hcard]
  constructor
  · change Matrix.trace
      ((6 : ℂ) • (1 : Matrix V V ℂ) + A) = 96
    rw [Matrix.trace_add, Matrix.trace_smul, htraceI, htraceA]
    norm_num
  · have hQsq : Q * Q =
        (36 : ℂ) • (1 : Matrix V V ℂ) +
          (12 : ℂ) • A + A * A := by
      dsimp [Q]
      simp only [Matrix.mul_add, Matrix.add_mul, Matrix.smul_mul,
        Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]
      module
    rw [hQsq, Matrix.trace_add, Matrix.trace_add, Matrix.trace_smul,
      Matrix.trace_smul, htraceI, htraceA, htraceA2]
    norm_num

end

end Erdos85
