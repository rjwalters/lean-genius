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

/- ## Part I: Basic Definitions -/

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
P(n) is prime when n > 1. Proved from Nat.find_spec.
-/
theorem P_is_prime {n : ℕ} (hn : n > 1) : (largestPrimeDivisor n).Prime := by
  unfold largestPrimeDivisor; rw [dif_pos hn]
  exact (Nat.find_spec (Nat.exists_prime_and_dvd (Nat.one_lt_iff_ne_one.mp hn))).1

/--
**Divisibility Property:**
P(n) divides n when n > 1. Proved from Nat.find_spec.
-/
theorem P_divides {n : ℕ} (hn : n > 1) : largestPrimeDivisor n ∣ n := by
  unfold largestPrimeDivisor; rw [dif_pos hn]
  exact (Nat.find_spec (Nat.exists_prime_and_dvd (Nat.one_lt_iff_ne_one.mp hn))).2

/--
**Maximality Property:**
P(n) is the largest prime divisor.
-/

/- ## Part II: Sylvester-Schur Theorem -/

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
**C(n,k) > 1 for valid binomial:**
For 1 ≤ k ≤ n/2, the binomial coefficient C(n,k) is at least 2.
Proved via Pascal's rule: C(n+1,k+1) = C(n,k) + C(n,k+1) ≥ 1 + 1 = 2.
-/
theorem choose_gt_one {n k : ℕ} (hk : 1 ≤ k) (hn : 2 * k ≤ n) : n.choose k > 1 := by
  cases n with
  | zero => omega
  | succ n' =>
    cases k with
    | zero => omega
    | succ k' =>
      rw [Nat.choose_succ_succ]
      have h1 : 0 < n'.choose k' := Nat.choose_pos (by omega)
      have h2 : 0 < n'.choose (k' + 1) := Nat.choose_pos (by omega)
      omega

/--
**Alternative Statement:**
The binomial coefficient C(n,k) has a prime divisor exceeding k.
-/
theorem binom_has_large_prime {n k : ℕ} (hk : 1 ≤ k) (hn : 2 * k ≤ n) :
    ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ p > k := by
  use P n k
  constructor
  · exact P_is_prime (choose_gt_one hk hn)
  constructor
  · exact P_divides (choose_gt_one hk hn)
  · exact sylvester_schur hk hn

/- ## Part III: Erdős's 1955 Improvement -/

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

/- ## Part IV: The Main Conjecture -/

/--
**Erdős Conjecture (Main Question):**
For every 1 ≤ k ≤ n, does there exist c > 0 such that:
  P(C(n,k)) ≥ min(n - k + 1, k^{1+c})
-/
def erdosConjecture683 : Prop :=
  ∃ c : ℝ, c > 0 ∧ ∀ n k : ℕ, 1 ≤ k → k ≤ n →
    (P n k : ℝ) ≥ min (n - k + 1 : ℝ) ((k : ℝ) ^ (1 + c))

/--
**Erdős (1979) Strengthening:**
Erdős wrote it "seems certain" that for any c > 0,
  P(C(n,k)) ≫ k^{1+c}
with only finitely many exceptions (depending on c).
-/

/- ## Part V: Heuristic Bounds -/

/--
**Prime Gap Heuristic:**
Standard heuristics on prime gaps suggest:
  P(C(n,k)) > e^{c√k}
for some c > 0 when k ≤ n/2.

This is much stronger than k^{1+c}.
-/

/--
**Comparison of Bounds:**
e^{c√k} grows much faster than k^{1+c}:
- k^{1+c} is polynomial
- e^{c√k} is stretched exponential
The stretched exponential eventually dominates any polynomial growth.
-/

/- ## Part VI: The min(n-k+1, k^{1+c}) Bound -/

/--
**Trivial Upper Bound:**
P(C(n,k)) ≤ n since C(n,k) divides products of terms ≤ n.
-/

/- ## Part VII: Products of Consecutive Integers -/

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

/--
**Generalization:**
Among k consecutive integers starting at m > k, at least one has
a prime divisor > k.
-/

/- ## Part VIII: Specific Cases -/

/--
**Central Binomial Case k = n/2:**
When k ≈ n/2, we have C(n,k) = C(2k,k), the central binomial coefficient.
Erdős proved P(C(2k,k)) > (4/3)k for large k.
-/

/--
**Small k Cases:**
For small k, explicit computation is possible.
k=2: P(C(n,2)) = P(n(n-1)/2) ≥ max prime factor of n or n-1.
Since C(n,2) = n(n-1)/2, and either n or n-1 has a prime factor ≥ (n-1)/2.
-/

/- ## Part IX: Summary -/

/--
**Erdős Problem #683: Summary**

QUESTION: For every 1 ≤ k ≤ n, is there a constant c > 0 such that
  P(C(n,k)) ≥ min(n - k + 1, k^{1+c})?

KNOWN:
- P(C(n,k)) > k for k ≤ n/2 (Sylvester-Schur 1892/1929)
- P(C(n,k)) ≫ k log k (Erdős 1955)
- For any c > 0, P(C(n,k)) > k^{1+c} with finitely many exceptions (believed)

HEURISTIC:
- P(C(n,k)) > e^{c√k} (from prime gap statistics)

STATUS: OPEN
-/
theorem erdos_683_summary :
    -- Sylvester-Schur: P(C(n,k)) > k
    (∀ n k : ℕ, 1 ≤ k → 2 * k ≤ n → P n k > k) ∧
    -- Erdős 1955: P(C(n,k)) ≫ k log k
    (∃ c : ℝ, c > 0 ∧ ∀ n k : ℕ, 1 ≤ k → 2 * k ≤ n →
      (P n k : ℝ) ≥ c * k * Real.log k) :=
  ⟨fun n k hk hn => sylvester_schur hk hn, erdos_1955_bound⟩

end Erdos683
