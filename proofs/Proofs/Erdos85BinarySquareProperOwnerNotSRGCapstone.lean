import Proofs.Erdos85BinarySquareProperOwnerCenteredObstruction
import Proofs.Erdos85BinarySquareProperOwnerSrgParameters

/-!
# Centering the strongly-regular owner identity

This file packages the last noncommutative matrix calculation in the proper
owner SRG branch.  Once the SRG parameters give
`M² = qM + m(m-1)J`, regularity gives `MJ = JM = qmJ`, and square order gives
`J² = q²J`.  Therefore `K = qM-mJ` satisfies `K²=q²K` and the centered-rank
obstruction applies.
-/

namespace Erdos85

/-- Centering a shifted strongly-regular adjacency matrix turns its quadratic
identity into a scalar projector identity. -/
theorem centered_quadratic_of_shifted_srg_quadratic
    {V : Type*} [Fintype V] [DecidableEq V]
    (M J : Matrix V V ℝ) (q m : ℕ) (hm : 1 ≤ m)
    (hM : M * M = (q : ℝ) • M + ((m * (m - 1) : ℕ) : ℝ) • J)
    (hMJ : M * J = ((q * m : ℕ) : ℝ) • J)
    (hJM : J * M = ((q * m : ℕ) : ℝ) • J)
    (hJJ : J * J = ((q * q : ℕ) : ℝ) • J) :
    let K := (q : ℝ) • M - (m : ℝ) • J
    K * K = ((q * q : ℕ) : ℝ) • K := by
  dsimp
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul]
  rw [hM, hMJ, hJM, hJJ]
  push_cast
  rw [Nat.cast_sub hm]
  module

/-- The shifted SRG identity, regular all-ones identities, and the exact
centered rank/trace data are jointly impossible for a proper owner part. -/
theorem false_of_proper_owner_shifted_srg_matrix_data
    {V : Type*} [Fintype V] [DecidableEq V]
    (M J : Matrix V V ℝ) {q m : ℕ} (hq : 1 ≤ q) (hm : 2 ≤ m)
    (hM : M * M = (q : ℝ) • M + ((m * (m - 1) : ℕ) : ℝ) • J)
    (hMJ : M * J = ((q * m : ℕ) : ℝ) • J)
    (hJM : J * M = ((q * m : ℕ) : ℝ) • J)
    (hJJ : J * J = ((q * q : ℕ) : ℝ) • J)
    (hrank : ((q : ℝ) • M - (m : ℝ) • J).rank = q * m - 1)
    (htrace : ((q : ℝ) • M - (m : ℝ) • J).trace =
      ((q * q * (m * (q - 1)) : ℕ) : ℝ)) : False := by
  apply false_of_proper_owner_centered_quadratic_rank_trace
    ((q : ℝ) • M - (m : ℝ) • J) hq hm
  · exact centered_quadratic_of_shifted_srg_quadratic M J q m
      (by omega) hM hMJ hJM hJJ
  · exact hrank
  · exact htrace

#print axioms centered_quadratic_of_shifted_srg_quadratic
#print axioms false_of_proper_owner_shifted_srg_matrix_data

end Erdos85
