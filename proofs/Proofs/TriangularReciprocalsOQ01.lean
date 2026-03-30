/-
  Triangular Reciprocals OQ-01: Figurate Number Reciprocal Sums

  Generalize ∑ 1/T(n) = 2 (where T(n) = n(n+1)/2 are triangular numbers)
  to higher figurate/polygonal numbers.

  The nth k-gonal number is P_k(n) = n((k-2)n - (k-4))/2.
  - k=3: T(n) = n(n+1)/2 (triangular), ∑ 1/T(n) = 2
  - k=4: Sq(n) = n² (square), ∑ 1/n² = π²/6 (Basel problem)
  - k=5: Pent(n) = n(3n-1)/2 (pentagonal), ∑ 2/Pent(n) has closed form
  - General k: ∑ 2/((k-2)n² - (k-4)n) can be evaluated by partial fractions
-/
import Mathlib

namespace TriangularReciprocalsOQ01

open Finset BigOperators

/-- The nth k-gonal number: P_k(n) = n((k-2)n - (k-4))/2 for n ≥ 1. -/
def polygonalNumber (k n : ℕ) : ℕ :=
  n * ((k - 2) * n - (k - 4)) / 2

/-- Triangular numbers as a special case. -/
theorem triangular_is_polygonal (n : ℕ) (hn : n ≥ 1) :
    polygonalNumber 3 n = n * (n + 1) / 2 := by
  unfold polygonalNumber
  omega

/-- Partial fraction decomposition for reciprocals of k-gonal numbers.
    For k ≥ 3 and n ≥ 1:
    2 / P_k(n) = 2 / (n((k-2)n-(k-4))/2) = 4 / (n · ((k-2)n-(k-4)))
    By partial fractions: = (2/(k-2)) · (1/n - 1/(n + (k-4)/(k-2))) -/
-- The partial fraction allows telescoping for certain k values

/-- For k=3 (triangular): ∑_{n=1}^N 2/(n(n+1)) = 2 - 2/(N+1).
    This telescopes: 2/(n(n+1)) = 2/n - 2/(n+1). -/
theorem triangular_partial_sum (N : ℕ) (hN : N ≥ 1) :
    ∑ n in Finset.Icc 1 N, (2 : ℚ) / (n * (n + 1)) = 2 - 2 / (↑N + 1) := by
  sorry

/-- For k=5 (pentagonal): Pent(n) = n(3n-1)/2.
    ∑_{n=1}^∞ 1/Pent(n) = ∑ 2/(n(3n-1)).
    By partial fractions: 2/(n(3n-1)) = 2/n - 6/(3n-1) ... this needs
    the digamma function for a closed form. -/
-- The pentagonal case has a closed form involving ln(3) and π/√3

/-- The general sum ∑ 1/P_k(n) converges for all k ≥ 3 (comparison with 1/n²). -/
theorem polygonal_reciprocal_converges (k : ℕ) (hk : k ≥ 3) :
    ∃ L : ℝ, Filter.Tendsto
      (fun N => ∑ n in Finset.Icc 1 N, (1 : ℝ) / polygonalNumber k n)
      Filter.atTop (nhds L) := by
  sorry

end TriangularReciprocalsOQ01
