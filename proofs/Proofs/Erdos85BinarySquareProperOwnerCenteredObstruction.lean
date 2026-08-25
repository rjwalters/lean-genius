import Proofs.Erdos85BinarySquareProperOwnerNotStronglyRegular

/-!
# The centered-owner projector obstruction

This is the normalization bridge between the integral centered owner matrix
and the idempotent trace/rank obstruction.  In the strongly-regular branch,
the parameter identities make the centered matrix `K` satisfy
`K² = q² K`.  Its already-banked rank is `q*m-1`, while its diagonal gives
trace `q²*m*(q-1)`.  Dividing by `q²` produces the forbidden projector.
-/

namespace Erdos85

private theorem rank_smul_ne_zero
    {M N : Type*} [Fintype M] [Fintype N]
    (A : Matrix M N ℝ) (a : ℝ) (ha : a ≠ 0) :
    (a • A).rank = A.rank := by
  rw [Matrix.rank, Matrix.rank]
  have hrange : LinearMap.range (a • A).mulVecLin =
      LinearMap.range A.mulVecLin := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨a • x, by simp⟩
    · rintro ⟨x, rfl⟩
      exact ⟨a⁻¹ • x, by simp [ha]⟩
  rw [hrange]

/-- A nonzero scalar multiple of a projector cannot have the centered-owner
rank and trace predicted by a proper normalized component. -/
theorem false_of_proper_owner_centered_quadratic_rank_trace
    {V : Type*} [Fintype V] [DecidableEq V]
    (K : Matrix V V ℝ) {q m : ℕ} (hq : 1 ≤ q) (hm : 2 ≤ m)
    (hquad : K * K = ((q * q : ℕ) : ℝ) • K)
    (hrank : K.rank = q * m - 1)
    (htrace : K.trace = ((q * q * (m * (q - 1)) : ℕ) : ℝ)) : False := by
  let a : ℝ := ((q * q : ℕ) : ℝ)⁻¹
  let P : Matrix V V ℝ := a • K
  have hq0 : (((q * q : ℕ) : ℝ)) ≠ 0 := by
    positivity
  have ha0 : a ≠ 0 := inv_ne_zero hq0
  have ha_mul : a * ((q * q : ℕ) : ℝ) = 1 := inv_mul_cancel₀ hq0
  have hidem : P * P = P := by
    dsimp [P]
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hquad, smul_smul]
    rw [mul_assoc, ha_mul]
    simp
  have hrankP : P.rank = q * m - 1 := by
    dsimp [P]
    rw [rank_smul_ne_zero K a ha0, hrank]
  have htraceP : P.trace = (m * (q - 1) : ℕ) := by
    calc
      P.trace = a * K.trace := by simp [P]
      _ = ((q * q : ℕ) : ℝ)⁻¹ *
          (((q * q : ℕ) : ℝ) * ((m * (q - 1) : ℕ) : ℝ)) := by
            dsimp [a]
            rw [htrace]
            push_cast
            rfl
      _ = (m * (q - 1) : ℕ) := by
        rw [← mul_assoc, inv_mul_cancel₀ hq0, one_mul]
  exact false_of_proper_owner_idempotent_trace_rank
    P hq hm hidem hrankP htraceP

#print axioms false_of_proper_owner_centered_quadratic_rank_trace

end Erdos85
