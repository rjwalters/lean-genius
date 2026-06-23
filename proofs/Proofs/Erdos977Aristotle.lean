/-
  Aristotle targets for Erdos977Problem
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
  - schinzel_ratio / stewart_quantitative / stewart_bound_implies_main: deep analytic NT
  - zsygmondy: Zsygmondy's theorem (deep, though may be in Mathlib)
  - lai_limsup_bound: Lai (2021) result
  - ord_divides / large_gpf_small_order: ord2 definition is simplified placeholder
  - gpf_mersenne_2/3/5/7/11: noncomputable def, decide won't work

  NOTE: Definitions are re-declared here (not imported from main file) to avoid
  redeclaration errors when this companion file is compiled standalone.
-/
import Mathlib

namespace Erdos977

open Finset Nat Real Filter

/-- The greatest prime factor of n, or 0 if n ≤ 1. -/
noncomputable def greatestPrimeFactor (n : ℕ) : ℕ :=
  if h : n ≤ 1 then 0
  else (n.primeFactors).max' (Nat.primeFactors_nonempty (Nat.one_lt_iff_ne_one.mpr
    (fun hn => h (le_of_eq hn))))

/-- Notation: P(n) for greatest prime factor. -/
notation "P" => greatestPrimeFactor

/-- Mersenne number M_n = 2^n - 1. -/
def mersenne (n : ℕ) : ℕ := 2 ^ n - 1

/-- A Mersenne prime is a prime of the form 2^n - 1. -/
def IsMersennePrime (n : ℕ) : Prop := (mersenne n).Prime

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

end Erdos977
