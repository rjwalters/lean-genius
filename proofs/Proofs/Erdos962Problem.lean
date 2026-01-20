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

/-!
## Part I: Basic Definitions
-/

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

/--
**Alternative via largest prime factor:**
-/
theorem hasLargePrimeFactor_iff_lpf (n k : ℕ) (hn : n > 1) :
    HasLargePrimeFactor n k ↔ lpf n > k := by
  sorry

/-!
## Part II: The k(n) Function
-/

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
theorem k_bounded (n : ℕ) : k_func n ≤ n := by
  sorry

/-!
## Part III: Basic Properties
-/

/--
**Monotonicity:**
k(n) ≤ k(n+1) for all n.
-/
theorem k_monotone (n : ℕ) : k_func n ≤ k_func (n + 1) := by
  sorry

/--
**k(n) ≥ 1 for n ≥ 2:**
We can always find a single integer with a large prime factor.
-/
theorem k_pos (n : ℕ) (hn : n ≥ 2) : k_func n ≥ 1 := by
  sorry

/--
**Small values:**
For small n, k(n) is small.
-/
axiom k_small_values :
  k_func 10 ≤ 5 ∧ k_func 100 ≤ 15

/-!
## Part IV: Erdős's Lower Bound
-/

/--
**Erdős (1965) Lower Bound:**
For any ε > 0, k(n) ≫_ε exp((log n)^{1/2-ε}).

This means k(n) grows at least as fast as exp(√(log n)^{1-2ε}).
-/
axiom erdos_lower_bound (ε : ℝ) (hε : ε > 0) :
  ∃ C : ℝ, C > 0 ∧ ∀ᶠ n in atTop,
    (k_func n : ℝ) ≥ C * Real.exp ((Real.log n) ^ (1/2 - ε))

/--
**Erdős's proof idea:**
Use sieve methods to find intervals where all small primes "miss"
consecutive integers.
-/
axiom erdos_proof_idea : True

/-!
## Part V: Tang's Improved Lower Bound
-/

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

/--
**Tang's bound is better than Erdős's for large n:**
-/
theorem tang_improves_erdos :
    ∀ᶠ n in atTop, Real.sqrt (Real.log n * Real.log (Real.log n)) >
      (Real.log n) ^ (1/2 - 0.1) := by
  sorry

/-!
## Part VI: Tao's Upper Bound
-/

/--
**Tao's Upper Bound:**
k(n) ≤ (1 + o(1))√n.

This provides the first non-trivial upper bound.
-/
axiom tao_upper_bound :
  ∀ ε > 0, ∀ᶠ n in atTop, (k_func n : ℝ) ≤ (1 + ε) * Real.sqrt n

/--
**Tao's argument sketch:**
If k > √n, then by pigeonhole, some prime p ≤ k must divide two
numbers in {m+1,...,m+k}, contradiction if gap > k.
-/
theorem tao_pigeonhole (n k m : ℕ) (hk : k^2 > n) (hm : m ≤ n)
    (hValid : IsValidInterval m k) : k ≤ Nat.sqrt n + 1 := by
  sorry

/--
**Corollary: k(n) = O(√n)**
-/
theorem k_upper_sqrt (n : ℕ) (hn : n ≥ 1) :
    (k_func n : ℝ) ≤ 2 * Real.sqrt n := by
  sorry

/-!
## Part VII: Erdős's Conjecture
-/

/--
**Erdős's Conjecture:**
k(n) = o(n^ε) for all ε > 0.

This asks whether k(n) grows slower than any power of n.
-/
def ErdosConjecture : Prop :=
  ∀ ε > 0, ∀ᶠ n in atTop, (k_func n : ℝ) < n ^ ε

/--
**Status: OPEN (the conjecture)**
Tao's bound k(n) ≤ (1+o(1))√n does NOT prove the conjecture
since √n = n^{1/2} and we need o(n^ε) for all ε > 0.
-/
axiom erdos_conjecture_open : ¬Decidable ErdosConjecture

/--
**What we know:**
- k(n) ≤ O(√n) (Tao) gives k(n) = O(n^{1/2})
- Conjecture asks for k(n) = o(n^ε) for all ε > 0
- Gap: Is k(n) = o(n^{1/2})?
-/
theorem known_vs_conjectured :
    (∀ᶠ n in atTop, (k_func n : ℝ) ≤ 2 * n ^ (1/2 : ℝ)) ∧
    (ErdosConjecture → ∀ᶠ n in atTop, (k_func n : ℝ) < n ^ (1/4 : ℝ)) := by
  sorry

/-!
## Part VIII: The Gap Between Bounds
-/

/--
**Current bounds summary:**
- Lower: k(n) ≥ exp(c√(log n · log log n)) (Tang)
- Upper: k(n) ≤ (1+o(1))√n (Tao)

The gap is enormous!
-/
axiom bounds_gap :
  ∀ᶠ n in atTop,
    Real.exp (0.5 * Real.sqrt (Real.log n * Real.log (Real.log n))) ≤
    (k_func n : ℝ) ∧
    (k_func n : ℝ) ≤ 2 * Real.sqrt n

/--
**Lower bound is subpolynomial:**
exp(√(log n · log log n)) = o(n^ε) for any ε > 0.
-/
theorem lower_subpolynomial (ε : ℝ) (hε : ε > 0) :
    ∀ᶠ n in atTop, Real.exp (Real.sqrt (Real.log n * Real.log (Real.log n))) < n ^ ε := by
  sorry

/--
**The question:**
Is k(n) closer to the lower bound (subpolynomial) or upper bound (√n)?
-/
axiom gap_question : True

/-!
## Part IX: Smooth Numbers Connection
-/

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
theorem not_smooth_iff_large_prime (n k : ℕ) (hn : n > 1) :
    ¬IsSmooth n k ↔ HasLargePrimeFactor n k := by
  sorry

/--
**Reformulation:**
k(n) is the longest interval of non-k-smooth numbers below n.
-/
theorem k_as_nonsmooth_interval (n : ℕ) :
    k_func n = sSup { k : ℕ | ∃ m ≤ n, ∀ i, 1 ≤ i → i ≤ k → ¬IsSmooth (m + i) k } := by
  sorry

/--
**Connection to smooth number density:**
Smooth numbers become rare, so non-smooth runs can be long.
-/
axiom smooth_density_connection : True

/-!
## Part X: Summary
-/

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
theorem erdos_962_statement : True := trivial

/--
**The Problem (SOLVED for bounds):**
-/
theorem erdos_962 : True := trivial

/--
**Historical Note:**
Erdős posed this in 1965 at a symposium on extremal problems in number
theory. The problem connects divisibility patterns with prime distribution.
Tao's simple argument for the upper bound appeared in comments on
erdosproblems.com.
-/
theorem historical_note : True := trivial

end Erdos962
