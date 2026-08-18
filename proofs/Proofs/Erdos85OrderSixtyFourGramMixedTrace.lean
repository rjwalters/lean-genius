import Proofs.Erdos85ComponentGramCommutation

/-! # The mixed cycle--Gram trace on H16 -/

namespace Erdos85

noncomputable section

/-- Expanding the corrected block identity fixes the mixed trace.  The
numerical hypotheses are precisely the full sixteen-dimensional H16 ledger:
the cycle block has square trace `32`, the defect block has square trace
`112`, and the exterior Gram matrix has moments `96,672`; the three `J`
traces encode their principal eigenvalues `2,7,12`. -/
theorem trace_cycleSq_mul_gram_eq_twoForty_sub_half_trace_four
    {n : Type*} [Fintype n] [DecidableEq n]
    (A D J Q : Matrix n n ℂ)
    (hid : A * A + Q = (7 : ℂ) • (1 : Matrix n n ℂ) + J - D)
    (hAJ : A * J = J * A) (hAQ : A * Q = Q * A)
    (hJQ : J * Q = Q * J)
    (hcard : Fintype.card n = 16)
    (htrJ : Matrix.trace J = 16)
    (htrJ2 : Matrix.trace (J * J) = 256)
    (htrA2 : Matrix.trace (A * A) = 32)
    (htrQ : Matrix.trace Q = 96)
    (htrQ2 : Matrix.trace (Q * Q) = 672)
    (htrD2 : Matrix.trace (D * D) = 112)
    (htrJA2 : Matrix.trace (J * (A * A)) = 64)
    (htrJQ : Matrix.trace (J * Q) = 192) :
    2 * Matrix.trace ((A * A) * Q) =
      480 - Matrix.trace ((A * A) * (A * A)) := by
  have hD : D = (7 : ℂ) • (1 : Matrix n n ℂ) + J - A * A - Q := by
    calc
      D = ((7 : ℂ) • (1 : Matrix n n ℂ) + J) - (A * A + Q) := by
        rw [hid]
        abel
      _ = _ := by abel
  have hA2Q : (A * A) * Q = Q * (A * A) := by
    calc
      (A * A) * Q = A * (A * Q) := by rw [Matrix.mul_assoc]
      _ = A * (Q * A) := by rw [hAQ]
      _ = (A * Q) * A := by rw [Matrix.mul_assoc]
      _ = (Q * A) * A := by rw [hAQ]
      _ = Q * (A * A) := by rw [Matrix.mul_assoc]
  have hJA2 : J * (A * A) = (A * A) * J := by
    calc
      J * (A * A) = (J * A) * A := by rw [Matrix.mul_assoc]
      _ = (A * J) * A := by rw [← hAJ]
      _ = A * (J * A) := by rw [Matrix.mul_assoc]
      _ = A * (A * J) := by rw [← hAJ]
      _ = (A * A) * J := by rw [Matrix.mul_assoc]
  have hsq : D * D =
      (49 : ℂ) • (1 : Matrix n n ℂ) + J * J +
        (A * A) * (A * A) + Q * Q +
        (14 : ℂ) • J - (14 : ℂ) • (A * A) - (14 : ℂ) • Q -
        (2 : ℂ) • (J * (A * A)) - (2 : ℂ) • (J * Q) +
        (2 : ℂ) • ((A * A) * Q) := by
    rw [hD]
    noncomm_ring [hJA2, hJQ, hA2Q]
    module
  have ht := congrArg Matrix.trace hsq
  simp only [Matrix.trace_add, Matrix.trace_sub, Matrix.trace_smul,
    Matrix.trace_one, hcard, htrJ, htrJ2, htrA2, htrQ, htrQ2,
    htrD2, htrJA2, htrJQ] at ht
  norm_num at ht ⊢
  linear_combination -ht

/-- Once the Gram matrix is recognized as `6I + A_R`, the C4-free
two-regular fourth moment `96` makes the residual mixed trace vanish.  Thus
the exterior-pair graph carries no edge seen by the distance-two walk matrix
of the internal cycle graph. -/
theorem trace_cycleSq_mul_pairAdj_eq_zero
    {n : Type*} [Fintype n] [DecidableEq n]
    (A AR Q : Matrix n n ℂ)
    (hQ : Q = (6 : ℂ) • (1 : Matrix n n ℂ) + AR)
    (htrA2 : Matrix.trace (A * A) = 32)
    (hmixed : 2 * Matrix.trace ((A * A) * Q) = 384) :
    Matrix.trace ((A * A) * AR) = 0 := by
  have hexpand : (A * A) * Q =
      (6 : ℂ) • (A * A) + (A * A) * AR := by
    rw [hQ]
    simp only [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_one]
  rw [hexpand, Matrix.trace_add, Matrix.trace_smul, htrA2] at hmixed
  norm_num at hmixed ⊢
  linear_combination hmixed / 2

end

end Erdos85
