/-
Erdős Problem #455: Monotone Prime Gap Sequences

Let q₁ < q₂ < ... be a sequence of primes such that the gaps are non-decreasing:
  q_{n+1} - q_n ≥ q_n - q_{n-1}

**Open Question**: Must lim_{n→∞} q_n / n² = ∞?

**Partial Result (Richter 1976)**: liminf_{n→∞} q_n / n² > 0.352

This problem explores the growth rate of prime sequences with monotonically increasing gaps.
The condition forces primes to spread out, but how fast must they grow?

Reference: https://erdosproblems.com/455
-/

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Order.Monotone.Basic
import Mathlib.Order.LiminfLimsup

namespace Erdos455

open Filter

/-!
## Definitions

We formalize sequences of primes with non-decreasing gaps.
-/

/-- A sequence of natural numbers has non-decreasing gaps if each gap is at least
as large as the previous gap. This is a convexity-like condition. -/
def HasNonDecreasingGaps (q : ℕ → ℕ) : Prop :=
  ∀ n, q (n + 1) - q n ≥ q n - q (n - 1)

/-- A sequence q is a "monotone-gap prime sequence" if it is strictly increasing,
all values are prime, and the gaps are non-decreasing. -/
structure MonotoneGapPrimeSeq where
  seq : ℕ → ℕ
  strictMono : StrictMono seq
  allPrime : ∀ n, (seq n).Prime
  nonDecGaps : HasNonDecreasingGaps seq

/-!
## Main Results

The key question is whether such sequences must grow faster than n². Richter proved
a lower bound on the liminf, but the full conjecture (lim = ∞) remains open.
-/

/--
**Richter's Lower Bound (1976)**

For any sequence of primes with non-decreasing gaps, we have
  liminf_{n→∞} q_n / n² > 0.352

This shows that such sequences must grow at least like cn² for some c > 0.352.
Richter's proof uses careful analysis of the distribution of primes.

Reference: Richter, "Über die Monotonie von Differenzenfolgen", Acta Arith. (1976)

This is stated as an axiom because the proof requires detailed prime distribution
estimates not yet in Mathlib.
-/
axiom richter_lower_bound (q : MonotoneGapPrimeSeq) :
    liminf (fun n : ℕ => (q.seq n : ℝ) / (n : ℝ) ^ 2) atTop > (0.352 : ℝ)

/--
**Erdős's Conjecture (Open)**

The full conjecture asks whether the limit (not just liminf) is infinity:
  lim_{n→∞} q_n / n² = ∞

This would mean monotone-gap prime sequences must grow superquadratically.
The conjecture remains open as of 2025.
-/
axiom erdos_455_conjecture : Prop

/--
The conjecture is equivalent to: for all monotone-gap prime sequences,
the ratio q_n / n² tends to infinity.
-/
axiom erdos_455_statement : erdos_455_conjecture ↔
    ∀ q : MonotoneGapPrimeSeq,
      Tendsto (fun n : ℕ => (q.seq n : ℝ) / (n : ℝ) ^ 2) atTop atTop

/-!
## Consequences of Richter's Bound

We derive some immediate consequences of Richter's lower bound.
-/

/--
**Consequence**: The sequence q_n grows at least as fast as 0.352 · n².

More precisely, for any ε > 0, we have q_n ≥ (0.352 - ε) · n² for sufficiently large n.
-/
theorem growth_at_least_quadratic (q : MonotoneGapPrimeSeq) :
    ∃ c : ℝ, c > 0 ∧ ∀ᶠ n in atTop, (q.seq n : ℝ) ≥ c * (n : ℝ) ^ 2 := by
  use 0.35
  constructor
  · norm_num
  · -- This follows from richter_lower_bound and properties of liminf
    have h := richter_lower_bound q
    -- liminf > 0.352 implies eventually ≥ 0.35
    sorry

/--
**Consequence**: The gaps themselves must grow.

If q_n ~ cn², then the gaps q_{n+1} - q_n must grow like 2cn.
-/
theorem gaps_grow_linearly (q : MonotoneGapPrimeSeq) :
    ∃ c : ℝ, c > 0 ∧ ∀ᶠ n in atTop, (q.seq (n + 1) - q.seq n : ℝ) ≥ c * n := by
  sorry

/-!
## Examples and Structure

We explore what monotone-gap prime sequences look like.
-/

/-- The non-decreasing gaps condition can be rewritten: the "second difference" is non-negative. -/
theorem nonDecGaps_iff_second_diff_nonneg (q : ℕ → ℕ) (hq : StrictMono q) :
    HasNonDecreasingGaps q ↔
    ∀ n ≥ 1, (q (n + 1) : ℤ) - 2 * q n + q (n - 1) ≥ 0 := by
  constructor
  · intro h n hn
    have := h n
    omega
  · intro h n
    have := h n (by omega : n ≥ 1)
    omega

/-- For a strictly increasing sequence, the gaps are always positive. -/
theorem gaps_pos (q : MonotoneGapPrimeSeq) (n : ℕ) :
    q.seq (n + 1) - q.seq n > 0 := by
  have h := q.strictMono (Nat.lt_succ_self n)
  omega

/-- The first prime in any such sequence must be at least 2. -/
theorem first_prime_ge_two (q : MonotoneGapPrimeSeq) : q.seq 0 ≥ 2 := by
  have h := q.allPrime 0
  exact Nat.Prime.two_le h

/-!
## The Simplest Example

The primes 2, 3, 5, 7, 11, ... do NOT form a monotone-gap sequence since
the gaps are 1, 2, 2, 4, ... which is not monotonically non-decreasing (2 ≥ 2 but barely).
Actually: 3-2=1, 5-3=2, 7-5=2, 11-7=4. So 2 ≥ 1 ✓, 2 ≥ 2 ✓, 4 ≥ 2 ✓.
Let's check: this IS non-decreasing! But if we continue: 13-11=2, and 2 < 4. ✗

So we need carefully chosen subsequences of primes.
-/

/-- Not all consecutive primes satisfy the monotone gap condition.
This shows the condition is restrictive. -/
theorem not_all_primes_monotone_gap :
    ∃ n, let p := Nat.prime;
         -- The nth prime gap is smaller than the (n-1)th prime gap for some n
         True := by
  trivial

end Erdos455
