/-
  Aristotle targets for SumOfKthPowersOQ04

  Routine supporting lemmas for automated proof search.
  See SumOfKthPowersOQ04.lean for the main formalization.

  Targets:
  1. low_degree_poly_ratio_tendsto_zero: for q with deg(q) < d, q(n)/n^d → 0
  2. monic_sub_pow_natDegree_lt: if p has deg d and leading coeff 1,
     then deg(p - X^d) < d
-/
import Mathlib

open Filter Polynomial

namespace SumOfKthPowersAsymptotic

/-- For a polynomial q over ℚ with degree < d, q(n)/n^d → 0 as n → ∞. -/
lemma low_degree_poly_ratio_tendsto_zero (q : Polynomial ℚ) (d : ℕ)
    (hd : 0 < d) (hdeg : q.natDegree < d) :
    Tendsto (fun n : ℕ => q.eval (↑n : ℚ) / (↑n : ℚ) ^ d) atTop (nhds 0) := by
  sorry

/-- If p : Polynomial ℚ has natDegree = d and leadingCoeff = 1 and d > 0,
    then (p - X^d).natDegree < d. -/
lemma monic_sub_pow_natDegree_lt (p : Polynomial ℚ) (d : ℕ)
    (hd_deg : p.natDegree = d) (hlc : p.leadingCoeff = 1) (hd : 0 < d) :
    (p - Polynomial.X ^ d).natDegree < d := by
  sorry

end SumOfKthPowersAsymptotic
