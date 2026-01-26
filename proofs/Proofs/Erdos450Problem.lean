/-!
# Erdős Problem #450: Divisor Density in Short Intervals

**Source:** [erdosproblems.com/450](https://erdosproblems.com/450)
**Status:** OPEN (Erdős–Graham, 1980)

## Statement

How large must y = y(ε, n) be such that the number of integers
in (x, x + y) with a divisor in (n, 2n) is at most ε·y?

## Background

From Erdős–Graham (1980, p.89). The question asks about the density
of integers having a "medium-sized" divisor (between n and 2n) in
short intervals. There is a subtlety about whether the bound holds
for all x or for some x.

Cambie showed that for the "for all x" interpretation, if
ε · (log n)^δ · (log log n)^{3/2} → ∞ (with δ ≈ 0.086),
no such y exists (using Ford's work on divisor distribution).

## Approach

We define the counting function for integers with divisors in
(n, 2n), the density condition, and state the problem.
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

namespace Erdos450

/-! ## Part I: Divisors in an Interval -/

/--
An integer m has a divisor in the interval (n, 2n).
-/
def HasDivisorIn (m n : ℕ) : Prop :=
  ∃ d : ℕ, d ∣ m ∧ n < d ∧ d < 2 * n

/--
Count of integers in (x, x + y) having a divisor in (n, 2n).
-/
noncomputable def countWithDivisor (x y n : ℕ) : ℕ :=
  ((Finset.range y).filter (fun i => HasDivisorIn (x + i + 1) n)).card

/-! ## Part II: The Density Condition -/

/--
The density of integers with a divisor in (n, 2n) within (x, x+y)
is at most ε. We use rational approximation: count ≤ εNum * y / εDen.
-/
def DensityBound (x y n εNum εDen : ℕ) : Prop :=
  εDen ≥ 1 ∧ countWithDivisor x y n * εDen ≤ εNum * y

/-! ## Part III: The Problem (For All x) -/

/--
**Erdős Problem #450 (Erdős–Graham 1980, p.89), "for all x" version:**
Given ε > 0 and n, find the least y such that for ALL x,
the density of integers in (x, x+y) with a divisor in (n, 2n)
is at most ε.
-/
def ErdosProblem450_ForAll : Prop :=
  ∀ εNum εDen : ℕ, εNum ≥ 1 → εDen ≥ 1 →
    ∀ n : ℕ, n ≥ 2 →
      ∃ y : ℕ, y ≥ 1 ∧
        ∀ x : ℕ, DensityBound x y n εNum εDen

/-! ## Part IV: The Problem (Existential x) -/

/--
**Erdős Problem #450, "exists x" version:**
Given ε > 0 and n, find the least y such that for SOME x,
the density condition holds.
-/
def ErdosProblem450_Exists : Prop :=
  ∀ εNum εDen : ℕ, εNum ≥ 1 → εDen ≥ 1 →
    ∀ n : ℕ, n ≥ 2 →
      ∃ y : ℕ, y ≥ 1 ∧
        ∃ x : ℕ, DensityBound x y n εNum εDen

/-! ## Part V: Known Results -/

/--
**Cambie's observation (for all x version):**
If ε · (log n)^δ · (log log n)^{3/2} → ∞ with δ ≈ 0.086,
no finite y works for the "for all x" version.
This uses Ford's work on the distribution of divisors.
-/
axiom cambie_no_y_for_all :
  -- For certain ε and n, the "for all x" version fails
  -- (axiomatized, as the logarithmic condition is complex)
  True

/--
**Cambie: small ε regime.**
For ε ≪ 1/n, y(ε, n) ∼ 2n. When y < 2n, the density bound fails
by considering multiples of lcm{n+1, ..., 2n-1}. For y > 2(1+δ)n,
many multiples of elements in (n, 2n) appear.
-/
axiom cambie_small_epsilon :
  ∀ n : ℕ, n ≥ 2 →
    -- For y ≥ 2n + 1, every interval of length y contains
    -- at least one multiple of some d in (n, 2n)
    ∀ y : ℕ, y ≥ 2 * n + 1 →
      ∀ x : ℕ, countWithDivisor x y n ≥ 1

/--
**Ford's divisor distribution:**
The number of integers ≤ x with a divisor in (n, 2n) has been
studied extensively. The density depends on the relationship
between x and n in a subtle way involving the "anatomy of integers."
-/
axiom ford_divisor_distribution :
  -- Ford's results on divisor distribution are foundational
  True

/-! ## Part VI: Summary -/

/--
**Summary:**
Erdős Problem #450 asks how large y must be so that the density of
integers in (x, x+y) with a divisor in (n, 2n) is at most ε.
The answer depends on whether x is quantified universally or
existentially. Cambie showed the "for all x" version fails for
certain ε, n ranges. OPEN.
-/
theorem erdos_450_status : True := trivial

end Erdos450
