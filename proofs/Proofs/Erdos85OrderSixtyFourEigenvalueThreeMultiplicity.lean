import Mathlib

/-!
# The eigenvalue-three multiplicity cap at order sixteen

The connected order-16 defect block in the order-64 seven-component branch
is 7-regular.  After removing its principal eigenvalue `7` and `m` copies of
the eigenvalue `3`, the remaining eigenvalues have fixed first and second
moments.  Cauchy--Schwarz makes `m ≥ 4` impossible.

This file packages the arithmetic terminal independently of a particular
matrix spectral-decomposition API.
-/

namespace Erdos85

/-- If `15-m` real numbers have the first and second moments left after
removing `7` and `m` copies of `3` from the spectrum of a 7-regular graph on
16 vertices, then `m ≤ 3`. -/
theorem orderSixteen_sevenRegular_eigenvalueThree_multiplicity_le_three
    (m : ℕ) (hm : m ≤ 15) (eigenvalue : Fin (15 - m) → ℝ)
    (hsum : ∑ i, eigenvalue i = -(7 : ℝ) - 3 * m)
    (hsq : ∑ i, eigenvalue i ^ 2 = 63 - 9 * m) :
    m ≤ 3 := by
  have hcauchy := sq_sum_le_card_mul_sum_sq
    (s := Finset.univ) (f := eigenvalue)
  rw [Finset.card_univ, Fintype.card_fin, hsum, hsq] at hcauchy
  have hcast : ((15 - m : ℕ) : ℝ) = 15 - m := by
    rw [Nat.cast_sub hm]
    norm_num
  rw [hcast] at hcauchy
  by_contra hnot
  have hm4 : 4 ≤ m := by omega
  have hm4R : (4 : ℝ) ≤ m := by exact_mod_cast hm4
  have hm15R : (m : ℝ) ≤ 15 := by exact_mod_cast hm
  nlinarith

end Erdos85
