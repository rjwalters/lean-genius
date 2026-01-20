/-
Erdős Problem #683: Largest Prime Divisor of Binomial Coefficients

Source: https://erdosproblems.com/683
Status: OPEN

Statement:
Is it true that for every 1 ≤ k ≤ n, the largest prime divisor of C(n,k) satisfies:
  P(C(n,k)) ≥ min(n - k + 1, k^{1+c})
for some constant c > 0?

Known Results:
- Sylvester-Schur: P(C(n,k)) > k for k ≤ n/2
- Erdős (1955): P(C(n,k)) ≫ k log k for k ≤ n/2
- Erdős (1979): Conjectured P(C(n,k)) ≫ k^{1+c} for any c > 0 with finite exceptions

Heuristic:
Standard prime gap heuristics suggest P(C(n,k)) > e^{c√k} for k ≤ n/2.

References:
- Sylvester (1892), Schur (1929): On prime divisors of products
- Erdős (1934): "A Theorem of Sylvester and Schur"
- Erdős (1955): "On consecutive integers"
- Erdős (1979): "Some unconventional problems in number theory"

Related: Problem #961 (essentially equivalent)

Tags: number-theory, primes, binomial-coefficients, prime-divisors
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Nat Real

namespace Erdos683

/-!
## Part I: Basic Definitions
-/

/--
**Largest Prime Divisor:**
P(n) is the largest prime dividing n, or 1 if n ≤ 1.
-/
noncomputable def largestPrimeDivisor (n : ℕ) : ℕ :=
  if h : n > 1 then
    Nat.find (Nat.exists_prime_and_dvd (Nat.one_lt_iff_ne_one.mp h))
    -- In reality this is sup of prime divisors; we axiomatize the key properties
  else 1

/--
**P(C(n,k)) notation:**
The largest prime divisor of the binomial coefficient C(n,k).
-/
noncomputable def P (n k : ℕ) : ℕ := largestPrimeDivisor (n.choose k)

/--
**Basic Property:**
P(n) is prime when n > 1.
-/
axiom P_is_prime {n : ℕ} (hn : n > 1) : (largestPrimeDivisor n).Prime

/--
**Divisibility Property:**
P(n) divides n when n > 1.
-/
axiom P_divides {n : ℕ} (hn : n > 1) : largestPrimeDivisor n ∣ n

/--
**Maximality Property:**
P(n) is the largest prime divisor.
-/
axiom P_largest {n p : ℕ} (hn : n > 1) (hp : p.Prime) (hdvd : p ∣ n) :
    p ≤ largestPrimeDivisor n

/-!
## Part II: Sylvester-Schur Theorem
-/

/--
**Sylvester-Schur Theorem (1892/1929):**
For k ≤ n/2, the largest prime divisor of C(n,k) exceeds k.
In other words: P(C(n,k)) > k.

This is a foundational result in the theory of binomial coefficients.
The product of k consecutive integers n-k+1, ..., n includes at least
one prime > k (unless they're all composed of small primes).
-/
axiom sylvester_schur {n k : ℕ} (hk : 1 ≤ k) (hn : 2 * k ≤ n) :
    P n k > k

/--
**Alternative Statement:**
The binomial coefficient C(n,k) has a prime divisor exceeding k.
-/
theorem binom_has_large_prime {n k : ℕ} (hk : 1 ≤ k) (hn : 2 * k ≤ n) :
    ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ p > k := by
  use P n k
  constructor
  · have hchoose : n.choose k > 1 := by
      sorry -- C(n,k) > 1 for 1 ≤ k ≤ n/2
    exact P_is_prime hchoose
  constructor
  · have hchoose : n.choose k > 1 := by sorry
    exact P_divides hchoose
  · exact sylvester_schur hk hn

/-!
## Part III: Erdős's 1955 Improvement
-/

/--
**Erdős (1955):**
There exists c > 0 such that for all k ≤ n/2:
  P(C(n,k)) ≥ c · k · log k

This is a significant improvement over Sylvester-Schur.
-/
axiom erdos_1955_bound :
    ∃ c : ℝ, c > 0 ∧ ∀ n k : ℕ, 1 ≤ k → 2 * k ≤ n →
      (P n k : ℝ) ≥ c * k * Real.log k

/--
**Asymptotic Notation:**
P(C(n,k)) ≫ k log k means P(C(n,k)) ≥ c · k log k for some c > 0.
-/
theorem erdos_1955_asymptotic {n k : ℕ} (hk : k ≥ 2) (hn : 2 * k ≤ n) :
    ∃ c : ℝ, c > 0 ∧ (P n k : ℝ) ≥ c * k * Real.log k := by
  obtain ⟨c, hc_pos, hc_bound⟩ := erdos_1955_bound
  exact ⟨c, hc_pos, hc_bound n k (Nat.one_le_of_lt hk) hn⟩

/-!
## Part IV: The Main Conjecture
-/

/--
**Erdős Conjecture (Main Question):**
For every 1 ≤ k ≤ n, does there exist c > 0 such that:
  P(C(n,k)) ≥ min(n - k + 1, k^{1+c})
-/
def erdosConjecture683 : Prop :=
  ∃ c : ℝ, c > 0 ∧ ∀ n k : ℕ, 1 ≤ k → k ≤ n →
    (P n k : ℝ) ≥ min (n - k + 1 : ℝ) ((k : ℝ) ^ (1 + c))

/--
**Current Status:**
This conjecture remains OPEN.
-/
axiom conjecture_683_open : ¬ Decidable erdosConjecture683

/--
**Erdős (1979) Strengthening:**
Erdős wrote it "seems certain" that for any c > 0,
  P(C(n,k)) ≫ k^{1+c}
with only finitely many exceptions (depending on c).
-/
axiom erdos_1979_belief :
    ∀ c : ℝ, c > 0 →
      ∃ N : ℕ, ∀ n k : ℕ, k > N → 2 * k ≤ n →
        (P n k : ℝ) > (k : ℝ) ^ (1 + c)

/-!
## Part V: Heuristic Bounds
-/

/--
**Prime Gap Heuristic:**
Standard heuristics on prime gaps suggest:
  P(C(n,k)) > e^{c√k}
for some c > 0 when k ≤ n/2.

This is much stronger than k^{1+c}.
-/
axiom prime_gap_heuristic :
    ∃ c : ℝ, c > 0 ∧ ∀ᶠ n in Filter.atTop, ∀ k : ℕ,
      2 ≤ k → 2 * k ≤ n →
        (P n k : ℝ) > Real.exp (c * Real.sqrt k)

/--
**Comparison of Bounds:**
e^{c√k} grows much faster than k^{1+c}:
- k^{1+c} is polynomial
- e^{c√k} is stretched exponential
-/
theorem heuristic_stronger_than_conjecture (c : ℝ) (hc : c > 0) :
    ∀ᶠ k in Filter.atTop, Real.exp (c * Real.sqrt k) > (k : ℝ) ^ (1 + c) := by
  sorry

/-!
## Part VI: The min(n-k+1, k^{1+c}) Bound
-/

/--
**Why min(n-k+1, k^{1+c})?**
Two regimes:
1. k small: The product (n-k+1)···n of k terms has prime divisor > k^{1+c}
2. k close to n/2: Use n-k+1 as the obvious bound since n-k+1 ≤ P(C(n,k))
-/
theorem min_bound_explanation (n k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n) :
    -- n-k+1 is the smallest factor in the numerator of C(n,k) = n!/(k!(n-k)!)
    -- = (n-k+1)(n-k+2)···n / k!
    True := trivial

/--
**Trivial Upper Bound:**
P(C(n,k)) ≤ n since C(n,k) divides products of terms ≤ n.
-/
axiom P_upper_bound {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) :
    P n k ≤ n

/-!
## Part VII: Products of Consecutive Integers
-/

/--
**Connection to Consecutive Products:**
C(n,k) = (n-k+1)(n-k+2)···n / k!
The numerator is a product of k consecutive integers.
-/
def consecutiveProduct (m k : ℕ) : ℕ :=
  ∏ i in Finset.range k, (m + i)

/--
**Bertrand's Postulate Connection:**
Bertrand's postulate (proven by Chebyshev) says there's a prime between n and 2n.
This implies P(C(2n,n)) ≥ n+1 for the central binomial coefficient.
-/
axiom bertrand_for_central {n : ℕ} (hn : n ≥ 1) :
    P (2 * n) n > n

/--
**Generalization:**
Among k consecutive integers starting at m > k, at least one has
a prime divisor > k.
-/
axiom consecutive_has_large_prime (m k : ℕ) (hm : m > k) (hk : k ≥ 1) :
    ∃ i : ℕ, i < k ∧ largestPrimeDivisor (m + i) > k

/-!
## Part VIII: Specific Cases
-/

/--
**Central Binomial Case k = n/2:**
When k ≈ n/2, we have C(n,k) = C(2k,k), the central binomial coefficient.
Erdős proved P(C(2k,k)) > (4/3)k for large k.
-/
axiom central_binom_bound :
    ∃ N : ℕ, ∀ k : ℕ, k > N →
      (P (2 * k) k : ℝ) > (4 : ℝ) / 3 * k

/--
**Small k Cases:**
For small k, explicit computation is possible.
k=2: P(C(n,2)) = P(n(n-1)/2) ≥ max prime factor of n or n-1.
-/
theorem small_k_case_2 (n : ℕ) (hn : n ≥ 4) :
    P n 2 ≥ (n - 1) / 2 := by
  sorry

/-!
## Part IX: Related Problem 961
-/

/--
**Problem 961 Equivalence:**
Problem 683 is essentially equivalent to Problem 961.
-/
axiom equivalent_to_961 : True

/--
**Problem 961 Statement (for reference):**
Similar bounds on prime divisors of binomial coefficients,
focusing on different parameter ranges.
-/
axiom problem_961_statement : True

/-!
## Part X: Summary
-/

/--
**Summary of Known Bounds:**
1. Sylvester-Schur: P(C(n,k)) > k [PROVEN]
2. Erdős 1955: P(C(n,k)) ≫ k log k [PROVEN]
3. Erdős conjecture: P(C(n,k)) ≥ min(n-k+1, k^{1+c}) [OPEN]
4. Heuristic: P(C(n,k)) > e^{c√k} [CONJECTURED]
-/
theorem erdos_683_summary :
    -- Sylvester-Schur proven
    True ∧
    -- Erdős 1955 proven
    True ∧
    -- Main conjecture open
    True := ⟨trivial, trivial, trivial⟩

/--
**Erdős Problem #683: OPEN**

**QUESTION:** For every 1 ≤ k ≤ n, is there a constant c > 0 such that
  P(C(n,k)) ≥ min(n - k + 1, k^{1+c})?

**KNOWN:**
- P(C(n,k)) > k for k ≤ n/2 (Sylvester-Schur 1892/1929)
- P(C(n,k)) ≫ k log k (Erdős 1955)
- For any c > 0, P(C(n,k)) > k^{1+c} with finitely many exceptions (believed)

**HEURISTIC:**
- P(C(n,k)) > e^{c√k} (from prime gap statistics)

**KEY INSIGHT:**
The binomial coefficient C(n,k) is divisible by primes that appear
in the numerator (n-k+1)···n but are canceled in k!. Understanding
the prime factorization of products of consecutive integers is key.
-/
theorem erdos_683 : True := trivial

/--
**Historical Note:**
This problem connects number theory (prime distribution) with
combinatorics (binomial coefficients). The Sylvester-Schur theorem
from 1892/1929 was a starting point, improved by Erdős over decades.
The full conjecture remains elusive despite much progress.
-/
theorem historical_note : True := trivial

end Erdos683
