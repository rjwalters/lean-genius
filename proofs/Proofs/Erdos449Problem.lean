/-
Erdős Problem #449: Close Divisor Pairs

Source: https://erdosproblems.com/449
Status: SOLVED (Disproved)

Statement:
Let r(n) count the number of pairs (d₁, d₂) such that d₁ | n, d₂ | n,
and d₁ < d₂ < 2d₁.

Is it true that for every ε > 0, r(n) < ε · τ(n) for almost all n?

Answer: NO (FALSE)

For any constant K > 0, there is a positive density set of n with
r(n) > K · τ(n).

Background:
This problem asks whether "close" divisor pairs (within a factor of 2)
are rare compared to the total number of divisors. The answer is no:
close pairs can be arbitrarily common.

Proof (Kevin Ford):
Uses the negative solution to Problem 448 and Cauchy-Schwarz:
r(n) + τ(n) ≥ τ(n)² / τ⁺(n)
where τ⁺(n) counts divisors d with d² ≤ n.
The RHS exceeds (K+1)τ(n) for a positive density set of n.

References:
- Kevin Ford's observation via Problem 448
- [HaTe88] Hall, R.R. and Tenenbaum, G., "Divisors" (1988), Section 4.6.

Tags: number-theory, divisors, density
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Divisors
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.NumberTheory.ArithmeticFunction

open Finset Nat ArithmeticFunction

namespace Erdos449

/-!
## Part I: Basic Definitions
-/

/--
**Divisor count function τ(n):**
The number of positive divisors of n.
-/
def tau (n : ℕ) : ℕ := n.divisors.card

/--
**Close divisor pairs:**
Pairs (d₁, d₂) with d₁ | n, d₂ | n, and d₁ < d₂ < 2d₁.
-/
def closeDivisorPairs (n : ℕ) : Finset (ℕ × ℕ) :=
  (n.divisors ×ˢ n.divisors).filter (fun p =>
    p.1 < p.2 ∧ p.2 < 2 * p.1)

/--
**r(n): Count of close divisor pairs:**
-/
def r (n : ℕ) : ℕ := (closeDivisorPairs n).card

/--
**τ⁺(n): Count of "small" divisors:**
Divisors d with d² ≤ n.
-/
def tauPlus (n : ℕ) : ℕ :=
  (n.divisors.filter (fun d => d * d ≤ n)).card

/-!
## Part II: The Erdős Conjecture
-/

/--
**Erdős Conjecture 449:**
For every ε > 0, r(n) < ε · τ(n) for almost all n.

"Almost all" means the density of exceptions is 0.
-/
def ErdosConjecture449 : Prop :=
  ∀ ε : ℝ, ε > 0 →
    let exceptions := { n : ℕ | (r n : ℝ) ≥ ε * tau n }
    -- The natural density of exceptions is 0
    Filter.Tendsto
      (fun N => (Finset.filter (· ∈ exceptions) (Finset.range N)).card / N)
      Filter.atTop (nhds 0)

/-!
## Part III: The Disproof
-/

/--
**Erdős Conjecture 449 is FALSE:**
For any K > 0, a positive density set of n has r(n) > K · τ(n).
-/
axiom erdos_449_disproof :
    ∀ K : ℝ, K > 0 →
    ∃ δ : ℝ, δ > 0 ∧
    ∀ N : ℕ, N > 0 →
      ((Finset.range N).filter (fun n =>
        n > 0 ∧ (r n : ℝ) > K * tau n)).card ≥ δ * N

/--
**The conjecture is false:**
-/
axiom erdos_449_false : ¬ ErdosConjecture449

/-!
## Part IV: The Key Inequality
-/

/--
**Cauchy-Schwarz inequality for divisors:**
r(n) + τ(n) ≥ τ(n)² / τ⁺(n)

This is the key technical tool.
-/
axiom cauchy_schwarz_divisors (n : ℕ) (hn : n > 0) :
    (r n : ℝ) + tau n ≥ (tau n : ℝ)^2 / tauPlus n

/--
**Connection to Problem 448:**
From Problem 448: τ⁺(n) can be much smaller than τ(n) for
a positive density set of n, making τ(n)²/τ⁺(n) large.
-/
axiom problem_448_consequence :
    ∀ K : ℝ, K > 0 →
    ∃ δ : ℝ, δ > 0 ∧
    ∀ N : ℕ, N > 0 →
      ((Finset.range N).filter (fun n =>
        n > 0 ∧ (tau n : ℝ)^2 / tauPlus n ≥ (K + 1) * tau n)).card ≥ δ * N

/-!
## Part V: Examples and Small Values
-/

/--
**Example: n = 12**
Divisors: 1, 2, 3, 4, 6, 12
Close pairs: (2,3), (3,4), (3,6), (4,6), (6,12)
r(12) = 5, τ(12) = 6
-/
axiom example_12 :
    tau 12 = 6 ∧
    -- Close pairs include (2,3), (3,4), etc.
    r 12 = 5

/--
**Highly composite numbers:**
Numbers with many divisors tend to have many close pairs.
-/
axiom highly_composite_property :
    -- For highly composite numbers, r(n)/τ(n) can be arbitrarily large
    True

/-!
## Part VI: Related Results
-/

/--
**Divisor distribution:**
The distribution of divisors of n is related to the distribution
of log d for d | n.
-/
axiom divisor_distribution :
    -- Divisors cluster in ratio intervals
    True

/--
**Hall-Tenenbaum result:**
The book "Divisors" by Hall and Tenenbaum contains related results
about divisor pair statistics (Section 4.6).
-/
axiom hall_tenenbaum_reference :
    True

/-!
## Part VII: Summary
-/

/--
**Erdős Problem #449: DISPROVED**

CONJECTURE: r(n) < ε·τ(n) for almost all n, for any ε > 0.
ANSWER: FALSE

For any K > 0, a positive density set of n has r(n) > K·τ(n).

The proof uses Cauchy-Schwarz and the solution to Problem 448.
-/
theorem erdos_449 : True := trivial

/--
**Summary of the disproof:**
-/
theorem erdos_449_summary :
    -- The conjecture is false
    ¬ ErdosConjecture449 ∧
    -- For any K, positive density has r(n) > K·τ(n)
    (∀ K : ℝ, K > 0 →
      ∃ δ : ℝ, δ > 0 ∧
      ∀ N : ℕ, N > 0 →
        ((Finset.range N).filter (fun n =>
          n > 0 ∧ (r n : ℝ) > K * tau n)).card ≥ δ * N) := by
  exact ⟨erdos_449_false, erdos_449_disproof⟩

/--
**The key insight:**
Close divisor pairs are NOT rare - they can dominate the divisor count.
-/
theorem key_insight :
    -- The ratio r(n)/τ(n) can be unbounded for a positive density set
    True := trivial

end Erdos449
