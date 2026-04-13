/-
  Aristotle targets for Erdős Problem #977 (Greatest Prime Factor of 2^n - 1)
  Routine supporting lemmas for automated proof search.
  See Erdos977Problem.lean for the main formalization.

  Criteria for inclusion:
  - NOT the main theorems (stewart_2013, schinzel_bound, zsygmondy, lai_limsup_bound)
  - Routine lemmas about greatestPrimeFactor and mersenne that follow from definitions
  - Arithmetic properties of Mersenne numbers
  - Properties of greatest prime factor from Finset.max' API

  Excluded (too deep for Aristotle):
  - stewart_2013: Stewart's 2013 theorem (deep number theory)
  - schinzel_bound: Schinzel (1962) bound (deep number theory)
  - stewart_quantitative / stewart_bound_implies_main: deep analytic NT
  - zsygmondy: Zsygmondy's theorem (deep, though may be in Mathlib)
  - lai_limsup_bound: Lai (2021) result
  - ord_divides / large_gpf_small_order: ord2 definition is simplified placeholder
-/
import Mathlib
import Proofs.Erdos977Problem

open Finset Nat Real Filter

namespace Erdos977Aristotle

open Erdos977

/-- P(n) divides n for n > 1.
    Strategy: P(n) = max' of primeFactors(n), which is a member, hence divides n. -/
theorem gpf_dvd (n : ℕ) (hn : n > 1) : P n ∣ n := by
  sorry

/-- P(n) is prime for n > 1.
    Strategy: max' of primeFactors(n) is prime since all elements of primeFactors are prime. -/
theorem gpf_prime (n : ℕ) (hn : n > 1) : (P n).Prime := by
  sorry

/-- P(n) is the maximum prime dividing n.
    Strategy: p ∈ primeFactors(n), so p ≤ max'(primeFactors(n)) = P(n). -/
theorem gpf_is_max (n : ℕ) (hn : n > 1) (p : ℕ) (hp : p.Prime) (hdvd : p ∣ n) :
    p ≤ P n := by
  sorry

/-- Mersenne number is positive for n ≥ 1.
    Strategy: 2^n ≥ 2 for n ≥ 1, so 2^n - 1 ≥ 1 > 0. -/
theorem mersenne_pos (n : ℕ) (hn : n ≥ 1) : mersenne n > 0 := by
  sorry

/-- Mersenne number is > 1 for n ≥ 2.
    Strategy: 2^n ≥ 4 for n ≥ 2, so 2^n - 1 ≥ 3 > 1. -/
theorem mersenne_gt_one (n : ℕ) (hn : n ≥ 2) : mersenne n > 1 := by
  sorry

/-- P(2^n - 1) is prime for n ≥ 2.
    Follows from mersenne_gt_one and gpf_prime. -/
theorem gpf_mersenne_well_defined (n : ℕ) (hn : n ≥ 2) :
    (P (mersenne n)).Prime := by
  sorry

/-- If M_n = 2^n - 1 is prime (Mersenne prime), then P(M_n) = M_n.
    Strategy: M_n is prime → M_n is its own only prime factor → P(M_n) = M_n. -/
theorem gpf_mersenne_prime (n : ℕ) (hn : n ≥ 2) (hmp : IsMersennePrime n) :
    P (mersenne n) = mersenne n := by
  sorry

/-- For Mersenne primes: P(M_n)/n = (2^n - 1)/n as real numbers.
    Follows from gpf_mersenne_prime by rewriting. -/
theorem mersenne_prime_ratio_large (n : ℕ) (hn : n ≥ 2) (hmp : IsMersennePrime n) :
    (P (mersenne n) : ℝ) / n = (2 ^ n - 1 : ℝ) / n := by
  sorry

/-- P(2^2 - 1) = P(3) = 3. -/
theorem gpf_mersenne_2 : P (mersenne 2) = 3 := by
  sorry

/-- P(2^3 - 1) = P(7) = 7. -/
theorem gpf_mersenne_3 : P (mersenne 3) = 7 := by
  sorry

/-- P(2^5 - 1) = P(31) = 31 (Mersenne prime). -/
theorem gpf_mersenne_5 : P (mersenne 5) = 31 := by
  sorry

/-- P(2^7 - 1) = P(127) = 127 (Mersenne prime). -/
theorem gpf_mersenne_7 : P (mersenne 7) = 127 := by
  sorry

/-- P(2^11 - 1) = P(2047) = 89, since 2047 = 23 × 89. -/
theorem gpf_mersenne_11 : P (mersenne 11) = 89 := by
  sorry

end Erdos977Aristotle
