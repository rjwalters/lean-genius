import Mathlib

/-! # Integer square-excess ledger for a cubic adjacency row -/

namespace Erdos85

open scoped BigOperators

/-- Exact square-mass decomposition for the 41 nonneighbor entries in an
h305 cubic adjacency row.  The correction vanishes precisely on entries
equal to three or four. -/
theorem fortyOne_sum_sq_eq_baseline_add_excess
    {ι : Type*} (s : Finset ι) (x : ι → ℤ) (q : ℤ)
    (hcard : s.card = 41) (hsum : ∑ i ∈ s, x i = 150 - q) :
    ∑ i ∈ s, x i ^ 2 =
      558 - 7 * q + ∑ i ∈ s, (x i - 3) * (x i - 4) := by
  calc
    ∑ i ∈ s, x i ^ 2 =
        ∑ i ∈ s, (7 * x i - 12 + (x i - 3) * (x i - 4)) := by
          apply Finset.sum_congr rfl
          intro i _
          ring
    _ = 7 * (∑ i ∈ s, x i) - 12 * s.card +
        ∑ i ∈ s, (x i - 3) * (x i - 4) := by
          simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib,
            Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
          ring
    _ = 558 - 7 * q + ∑ i ∈ s, (x i - 3) * (x i - 4) := by
          rw [hsum, hcard]
          norm_num
          ring

/-- Adding the six oriented-edge contributions `6*11²` and the diagonal
square gives the exact full-row baseline used in the sixth-moment ledger. -/
theorem h305_cubicRow_squareMass_eq_baseline_add_excess
    {ι : Type*} (s : Finset ι) (x : ι → ℤ) (q : ℤ)
    (hcard : s.card = 41) (hsum : ∑ i ∈ s, x i = 150 - q) :
    6 * 11 ^ 2 + q ^ 2 + ∑ i ∈ s, x i ^ 2 =
      1284 - 7 * q + q ^ 2 +
        ∑ i ∈ s, (x i - 3) * (x i - 4) := by
  rw [fortyOne_sum_sq_eq_baseline_add_excess s x q hcard hsum]
  ring

/-- There is no integer strictly between three and four, so every correction
term is nonnegative (indeed this does not require `x ≥ 0`). -/
theorem integer_three_four_excess_nonnegative (x : ℤ) :
    0 ≤ (x - 3) * (x - 4) := by
  rcases le_or_gt x 3 with hx | hx
  · exact mul_nonneg_of_nonpos_of_nonpos (by omega) (by omega)
  · have hx4 : 4 ≤ x := by omega
    exact mul_nonneg (by omega) (by omega)

theorem sum_integer_three_four_excess_nonnegative
    {ι : Type*} (s : Finset ι) (x : ι → ℤ) :
    0 ≤ ∑ i ∈ s, (x i - 3) * (x i - 4) := by
  apply Finset.sum_nonneg
  intro i hi
  exact integer_three_four_excess_nonnegative (x i)

end Erdos85

#print axioms Erdos85.fortyOne_sum_sq_eq_baseline_add_excess
#print axioms Erdos85.h305_cubicRow_squareMass_eq_baseline_add_excess
#print axioms Erdos85.sum_integer_three_four_excess_nonnegative
