/-
Erdős Problem #962: Consecutive Integers with Large Prime Divisors

Source: https://erdosproblems.com/962
Status: SOLVED (bounds established)

Statement:
Let k(n) be the maximal k such that there exists m ≤ n where each of
m+1, ..., m+k is divisible by at least one prime > k.
Estimate k(n).

Known Results:
- Erdős (1965): k(n) ≫_ε exp((log n)^{1/2-ε})
- Erdős conjecture: k(n) = o(n^ε) for all ε > 0
- Tao: k(n) ≤ (1+o(1))√n (upper bound)
- Tang: k(n) ≥ exp((1/√2 - o(1))√(log n · log log n)) (lower bound)

References:
- [Er65] Erdős: Extremal problems in number theory (1965)
- Tao: Comment on erdosproblems.com
- Tang: Lower bound improvement

Tags: number-theory, prime-numbers, consecutive-integers, divisibility
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.Filter.Basic

open Nat Finset Real Filter

namespace Erdos962

/- ## Part I: Basic Definitions -/

/--
**Largest Prime Factor:**
The largest prime dividing n, or 0 if n ≤ 1.
-/
noncomputable def lpf (n : ℕ) : ℕ :=
  if h : n > 1 then n.factors.maximum?.getD 0 else 0

/--
**Property: Divisible by Prime > k:**
n has at least one prime factor greater than k.
-/
def HasLargePrimeFactor (n k : ℕ) : Prop :=
  ∃ p : ℕ, p.Prime ∧ p ∣ n ∧ p > k

/- ## Part II: The k(n) Function -/

/--
**Valid Interval:**
The interval {m+1, ..., m+k} where each element has a prime factor > k.
-/
def IsValidInterval (m k : ℕ) : Prop :=
  ∀ i : ℕ, 1 ≤ i → i ≤ k → HasLargePrimeFactor (m + i) k

/--
**The Function k(n):**
k(n) = max{k : ∃ m ≤ n, IsValidInterval m k}

The largest k such that we can find m ≤ n with m+1,...,m+k all
having a prime factor exceeding k.
-/
noncomputable def k_func (n : ℕ) : ℕ :=
  sSup { k : ℕ | ∃ m : ℕ, m ≤ n ∧ IsValidInterval m k }

/--
**k is well-defined and finite:**
For any n, we have k(n) ≤ n.
-/
/--
**Monotonicity:**
k(n) ≤ k(n+1) for all n.
-/
/--
**k(n) ≥ 1 for n ≥ 2:**
We can always find a single integer with a large prime factor.
-/
/--
**Small values:**
For small n, k(n) is small.
-/
/- ## Part III: Erdős's Lower Bound -/

/--
**Erdős (1965) Lower Bound:**
For any ε > 0, k(n) ≫_ε exp((log n)^{1/2-ε}).

This means k(n) grows at least as fast as exp(√(log n)^{1-2ε}).
-/
/- ## Part IV: Tang's Improved Lower Bound -/

/--
**Tang's Lower Bound:**
k(n) ≥ exp((1/√2 - o(1))√(log n · log log n)).

This significantly improves Erdős's original bound.
-/
axiom tang_lower_bound :
  ∀ ε > 0, ∀ᶠ n in atTop,
    (k_func n : ℝ) ≥ Real.exp ((1 / Real.sqrt 2 - ε) *
      Real.sqrt (Real.log n * Real.log (Real.log n)))

/--
**Tang's exponent:**
The constant 1/√2 ≈ 0.707 appears in the lower bound.
-/
noncomputable def tangConstant : ℝ := 1 / Real.sqrt 2

/- ## Part V: Tao's Upper Bound -/

/--
**Tao's Upper Bound:**
k(n) ≤ (1 + o(1))√n.

This provides the first non-trivial upper bound.
-/
axiom tao_upper_bound :
  ∀ ε > 0, ∀ᶠ n in atTop, (k_func n : ℝ) ≤ (1 + ε) * Real.sqrt n

/- ## Part VI: Erdős's Conjecture -/

/--
**Erdős's Conjecture:**
k(n) = o(n^ε) for all ε > 0.

This asks whether k(n) grows slower than any power of n.
Tao's bound k(n) ≤ (1+o(1))√n does NOT prove the conjecture
since √n = n^{1/2} and we need o(n^ε) for all ε > 0.
-/
def ErdosConjecture : Prop :=
  ∀ ε > 0, ∀ᶠ n in atTop, (k_func n : ℝ) < n ^ ε

/- ## Part VII: Smooth Numbers Connection -/

/--
**Smooth number:**
n is y-smooth if all prime factors of n are ≤ y.
-/
def IsSmooth (n y : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ∣ n → p ≤ y

/--
**Complementary property:**
n is NOT k-smooth iff n has a prime factor > k.
-/
/- ## Part VIII: Summary -/

/--
**Erdős Problem #962: SOLVED (bounds established)**

**DEFINITION:**
k(n) = max{k : ∃ m ≤ n, each of m+1,...,m+k has prime factor > k}

**KNOWN BOUNDS:**
- Lower: exp((1/√2 - o(1))√(log n · log log n)) (Tang)
- Upper: (1 + o(1))√n (Tao)

**CONJECTURE (OPEN):**
k(n) = o(n^ε) for all ε > 0

**KEY INSIGHT:**
The problem asks how long an interval can be where all integers
"avoid" being divisible only by small primes.
-/
theorem erdos_962_summary :
    -- Tang's lower bound holds
    (∀ ε > 0, ∀ᶠ n in atTop,
      (k_func n : ℝ) ≥ Real.exp ((1 / Real.sqrt 2 - ε) *
        Real.sqrt (Real.log n * Real.log (Real.log n)))) ∧
    -- Tao's upper bound holds
    (∀ ε > 0, ∀ᶠ n in atTop, (k_func n : ℝ) ≤ (1 + ε) * Real.sqrt n) :=
  ⟨tang_lower_bound, tao_upper_bound⟩

/--
**Erdős Problem #962: Bounds on k(n)**
Tang's lower bound and Tao's upper bound.
-/
theorem erdos_962 :
    (∀ ε > 0, ∀ᶠ n in atTop,
      (k_func n : ℝ) ≥ Real.exp ((1 / Real.sqrt 2 - ε) *
        Real.sqrt (Real.log n * Real.log (Real.log n)))) ∧
    (∀ ε > 0, ∀ᶠ n in atTop, (k_func n : ℝ) ≤ (1 + ε) * Real.sqrt n) :=
  erdos_962_summary

end Erdos962
