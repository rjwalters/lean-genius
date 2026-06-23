/-
  Aristotle targets for ArithmeticSeriesOQ02OQ03 (Simplicial Face Counts)
  Routine supporting lemma for automated proof search.
  See ArithmeticSeriesOQ02OQ03.lean for the main formalization.

  Target:
  - euler_characteristic_ari: Euler characteristic of k-simplex = 1
    (alternating sum of face counts)

  Proof strategy:
  The key identity is ∑_{j=0}^{k} (-1)^j C(k+1, j+1) = 1.
  Reindex i = j + 1: the sum becomes -∑_{i=1}^{k+1} (-1)^i C(k+1, i).
  Use Int.alternating_sum_range_choose (k+1): ∑_{i=0}^{k+2} (-1)^i C(k+1,i) = 0
  for k+1 ≥ 1. Extract the i=0 term (= 1) to get the result.
-/
import Mathlib

open Finset BigOperators

namespace ArithmeticSeriesOQ02OQ03.Aristotle

/-
**Euler characteristic of Δ^k is 1** (Aristotle target).

    χ(Δ^k) = ∑_{j=0}^{k} (-1)^j f_j = 1, where f_j = C(k+1, j+1).

    Proof: ∑_{j=0}^k (-1)^j C(k+1, j+1) = 1.
    Reindex (i = j+1): ∑_{i=1}^{k+1} (-1)^{i-1} C(k+1, i) = 1.
    Use the alternating binomial identity ∑_{i=0}^{k+1} (-1)^i C(k+1,i) = 0
    (for k+1 ≥ 1), then extract the i=0 term.
-/
theorem euler_characteristic_ari (k : ℕ) :
    ∑ j ∈ range (k + 1), (-1 : ℤ) ^ j * (Nat.choose (k + 1) (j + 1) : ℤ) = 1 := by
  -- Consider the binomial expansion of $(1-1)^{k+1}$.
  have h_binom : ∑ j ∈ Finset.range (k+2), (-1 : ℤ) ^ j * Nat.choose (k+1) j = 0 := by
    exact mod_cast by erw [ Int.alternating_sum_range_choose ] ; norm_num;
  simp_all +decide [ Finset.sum_range_succ', pow_succ ];
  linarith

end ArithmeticSeriesOQ02OQ03.Aristotle