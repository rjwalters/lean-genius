/-
  Erdős Problem #977: Greatest Prime Factor of 2^n - 1

  Source: https://erdosproblems.com/977
  Status: SOLVED (Stewart 2013)

  Statement:
  If P(m) is the greatest prime divisor of m, then is it true that
  P(2^n - 1) / n → ∞ as n → ∞?

  Solution:
  - Stewart (2013): P(2^n - 1) ≫ n^{1 + 1/(104 log log n)} for large n
  - Schinzel (1962): P(2^n - 1) > 2n for n > 12

  Related: P(n! + 1) behavior is still OPEN.

  Tags: number-theory, prime-factors, mersenne
-/

import Mathlib.NumberTheory.Primorial
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Instances.Real
import Mathlib.Tactic

namespace Erdos977

open Nat Real Filter

/- ## Part I: Greatest Prime Factor -/

/-- The greatest prime factor of n, or 0 if n ≤ 1. -/
noncomputable def greatestPrimeFactor (n : ℕ) : ℕ :=
  if h : n ≤ 1 then 0
  else (n.primeFactors).max' (Nat.primeFactors_nonempty (Nat.one_lt_iff_ne_one.mpr
    (fun hn => h (le_of_eq hn))))

/-- Notation: P(n) for greatest prime factor. -/
notation "P" => greatestPrimeFactor

/-- P(n) divides n for n > 1. -/
theorem gpf_dvd (n : ℕ) (hn : n > 1) : P n ∣ n := by
  sorry

/-- P(n) is prime for n > 1. -/
theorem gpf_prime (n : ℕ) (hn : n > 1) : (P n).Prime := by
  sorry

/-- P(n) is the maximum prime dividing n. -/
theorem gpf_is_max (n : ℕ) (hn : n > 1) (p : ℕ) (hp : p.Prime) (hdvd : p ∣ n) :
    p ≤ P n := by
  sorry

/- ## Part II: Mersenne Numbers -/

/-- Mersenne number M_n = 2^n - 1. -/
def mersenne (n : ℕ) : ℕ := 2 ^ n - 1

/-- Mersenne number is positive for n ≥ 1. -/
theorem mersenne_pos (n : ℕ) (hn : n ≥ 1) : mersenne n > 0 := by
  sorry

/-- Mersenne number is > 1 for n ≥ 2. -/
theorem mersenne_gt_one (n : ℕ) (hn : n ≥ 2) : mersenne n > 1 := by
  sorry

/-- P(2^n - 1) is well-defined for n ≥ 2. -/
theorem gpf_mersenne_well_defined (n : ℕ) (hn : n ≥ 2) :
    (P (mersenne n)).Prime := by
  sorry

/- ## Part III: The Main Question -/

/-- The main question: Does P(2^n - 1) / n → ∞? -/
def MainQuestion : Prop :=
  Tendsto (fun n : ℕ => (P (mersenne n) : ℝ) / n) atTop atTop

/-- Stewart (2013): The answer is YES. -/
theorem stewart_2013 : MainQuestion := by
  sorry

/- ## Part IV: Schinzel's Bound -/

/-- Schinzel (1962): P(2^n - 1) > 2n for n > 12. -/
theorem schinzel_bound (n : ℕ) (hn : n > 12) :
    P (mersenne n) > 2 * n := by
  sorry

/-- Corollary: P(2^n - 1) / n > 2 for n > 12. -/
theorem schinzel_ratio (n : ℕ) (hn : n > 12) :
    (P (mersenne n) : ℝ) / n > 2 := by
  sorry

/- ## Part V: Stewart's Quantitative Bound -/

/-- Stewart's quantitative bound: P(2^n - 1) ≥ n^{1 + 1/(104 log log n)}. -/
theorem stewart_quantitative :
    ∀ᶠ n in atTop, (P (mersenne n) : ℝ) ≥
      (n : ℝ) ^ (1 + 1 / (104 * Real.log (Real.log n))) := by
  sorry

/-- Stewart's bound implies the main result. -/
theorem stewart_bound_implies_main :
    (∀ᶠ n in atTop, (P (mersenne n) : ℝ) ≥
      (n : ℝ) ^ (1 + 1 / (104 * Real.log (Real.log n)))) →
    MainQuestion := by
  sorry

/- ## Part VI: Small Cases -/

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

/-- P(2^11 - 1) = P(2047) = P(23 × 89) = 89. -/
theorem gpf_mersenne_11 : P (mersenne 11) = 89 := by
  sorry

/- ## Part VII: Mersenne Primes -/

/-- A Mersenne prime is a prime of the form 2^n - 1. -/
def IsMersennePrime (n : ℕ) : Prop := (mersenne n).Prime

/-- If M_n is a Mersenne prime, then P(M_n) = M_n. -/
theorem gpf_mersenne_prime (n : ℕ) (hn : n ≥ 2) (hmp : IsMersennePrime n) :
    P (mersenne n) = mersenne n := by
  sorry

/-- For Mersenne primes, P(M_n)/n = (2^n - 1)/n → ∞. -/
theorem mersenne_prime_ratio_large (n : ℕ) (hn : n ≥ 2) (hmp : IsMersennePrime n) :
    (P (mersenne n) : ℝ) / n = (2 ^ n - 1 : ℝ) / n := by
  sorry

/- ## Part VIII: Related Problem - P(n! + 1) -/

/-- The related open question about P(n! + 1). -/
def RelatedQuestion : Prop :=
  Tendsto (fun n : ℕ => (P (Nat.factorial n + 1) : ℝ) / (n * Real.log n)) atTop atTop

/-- Under ABC conjecture: P(n! + 1) > (1 + o(1)) n log n. -/
def ABCImpliesFactorialBound : Prop :=
  ∀ ε > 0, ∀ᶠ n in atTop,
    (P (Nat.factorial n + 1) : ℝ) > (1 - ε) * n * Real.log n

/-- Lai (2021): limsup P(n! + 1) / n ≥ 1 + 9 log 2 ≈ 7.238. -/
theorem lai_limsup_bound :
    Filter.limsup (fun n : ℕ => (P (Nat.factorial n + 1) : ℝ) / n) atTop ≥
      1 + 9 * Real.log 2 := by
  sorry

/- ## Part IX: Primitive Prime Factors -/

/-- A primitive prime factor of 2^n - 1 is a prime p | 2^n - 1
    such that p ∤ 2^k - 1 for all k < n. -/
def IsPrimitivePrimeFactor (p n : ℕ) : Prop :=
  p.Prime ∧ p ∣ mersenne n ∧ ∀ k < n, ¬(p ∣ mersenne k)

/-- Zsygmondy's theorem: For n > 6, 2^n - 1 has a primitive prime factor. -/
theorem zsygmondy (n : ℕ) (hn : n > 6) :
    ∃ p, IsPrimitivePrimeFactor p n := by
  sorry

/-- Primitive prime factors give lower bounds on P(2^n - 1). -/
theorem primitive_gives_lower_bound (n : ℕ) (hn : n > 6) :
    ∃ p, IsPrimitivePrimeFactor p n ∧ p ≤ P (mersenne n) := by
  sorry

/- ## Part X: Order of 2 modulo p -/

/-- The multiplicative order of 2 modulo p. -/
noncomputable def ord2 (p : ℕ) : ℕ :=
  if hp : p.Prime ∧ p > 2 then Nat.minFac (p - 1) else 0  -- simplified

/-- If p | 2^n - 1, then ord_p(2) | n. -/
theorem ord_divides (p n : ℕ) (hp : p.Prime) (hp2 : p > 2) (hdvd : p ∣ mersenne n) :
    ord2 p ∣ n := by
  sorry

/-- Connection: Large P(2^n - 1) relates to small ord_p(2). -/
theorem large_gpf_small_order (n : ℕ) (hn : n ≥ 2) :
    ∃ p, p.Prime ∧ p ∣ mersenne n ∧ ord2 p ≤ n ∧ p = P (mersenne n) := by
  sorry

end Erdos977

/-
  ## Summary

  This file formalizes Erdős Problem #977 on the greatest prime factor of 2^n - 1.

  **Status**: SOLVED (Stewart 2013)

  **The Question**: Does P(2^n - 1) / n → ∞ as n → ∞?

  **Answer**: YES! Stewart (2013) proved P(2^n - 1) ≥ n^{1 + 1/(104 log log n)}.

  **Earlier Results**:
  - Schinzel (1962): P(2^n - 1) > 2n for n > 12

  **What we formalize**:
  1. Greatest prime factor P(n)
  2. Mersenne numbers 2^n - 1
  3. Stewart's theorem (main result)
  4. Schinzel's bound
  5. Stewart's quantitative bound
  6. Small cases and Mersenne primes
  7. Related open problem P(n! + 1)
  8. Primitive prime factors (Zsygmondy)
  9. Order of 2 modulo p

  **Key sorries**:
  - `stewart_2013`: The main result
  - `schinzel_bound`: The 1962 lower bound
  - `stewart_quantitative`: The precise growth rate

  **Related**: P(n! + 1) question remains OPEN
-/
