/-
Erdős Problem #252: Irrationality of Divisor Power Sums

Source: https://erdosproblems.com/252
Status: PARTIALLY SOLVED (k ≤ 4 proved, k ≥ 5 open)

Statement:
For k ≥ 1 and σ_k(n) = Σ_{d|n} d^k (the sum of k-th powers of divisors),
is the sum Σ_{n=1}^∞ σ_k(n)/n! irrational?

History:
- k = 0: Erdős-Straus (1971) proved irrational
- k = 1, 2: Erdős (1952) observed these are straightforward
- k = 3: Independently proved by Schlage-Puchta (2006) and Friedlander-Luca-Stoiciu (2007)
- k = 4: Pratt (2022)
- k ≥ 5: OPEN

Conditional results:
- All k ≥ 1 would follow from Schinzel's hypothesis H (Schlage-Puchta 2006)
- All k ≥ 4 would follow from the prime k-tuples conjecture (Friedlander-Luca-Stoiciu 2007)

Reference: Guy's "Unsolved Problems in Number Theory" Problem B14
-/

import Mathlib.NumberTheory.ArithmeticFunction.Defs
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Tactic

open scoped Nat ArithmeticFunction
open ArithmeticFunction

namespace Erdos252

/-! ## The Divisor Power Sum

The main object of study is the infinite series Σ_{n=1}^∞ σ_k(n)/n!
where σ_k(n) = Σ_{d|n} d^k is the sum of k-th powers of divisors of n.

Special cases:
- σ_0(n) = d(n) = number of divisors
- σ_1(n) = σ(n) = sum of divisors
-/

/-- The divisor power sum: Σ_{n=1}^∞ σ_k(n)/n! -/
noncomputable def divisorPowerSum (k : ℕ) : ℝ :=
  ∑' n, (sigma k n : ℝ) / (n ! : ℝ)

/-! ## Proved Cases: k = 0, 1, 2, 3, 4

These cases have been proved unconditionally by various authors.
We axiomatize these results as they require transcendence-theory techniques
beyond current Mathlib.
-/

/-- **Erdős-Straus (1971)**: Σ σ_0(n)/n! = Σ d(n)/n! is irrational.
    σ_0(n) counts the number of divisors of n. -/
axiom erdos_252_k0 : Irrational (divisorPowerSum 0)

/-- **Erdős (1952)**: Σ σ_1(n)/n! is irrational.
    σ_1(n) is the classical sum of divisors function. -/
axiom erdos_252_k1 : Irrational (divisorPowerSum 1)

/-- **Erdős (1952)**: Σ σ_2(n)/n! is irrational.
    σ_2(n) is the sum of squares of divisors. -/
axiom erdos_252_k2 : Irrational (divisorPowerSum 2)

/-- **Schlage-Puchta (2006) / Friedlander-Luca-Stoiciu (2007)**:
    Σ σ_3(n)/n! is irrational. Two independent proofs. -/
axiom erdos_252_k3 : Irrational (divisorPowerSum 3)

/-- **Pratt (2022)**: Σ σ_4(n)/n! is irrational.
    This was the most recent breakthrough. -/
axiom erdos_252_k4 : Irrational (divisorPowerSum 4)

/-- Consolidation: irrationality is proved for all k ≤ 4. -/
theorem erdos_252_le_4 (k : ℕ) (hk : k ≤ 4) : Irrational (divisorPowerSum k) := by
  interval_cases k
  · exact erdos_252_k0
  · exact erdos_252_k1
  · exact erdos_252_k2
  · exact erdos_252_k3
  · exact erdos_252_k4

/-! ## The Open Conjecture: k ≥ 5

For k ≥ 5, the irrationality of Σ σ_k(n)/n! remains open.
The full conjecture is that these sums are irrational for ALL k ≥ 1.
-/

/-- **Erdős Problem #252** (Full Conjecture):
    For all k ≥ 1, the sum Σ σ_k(n)/n! is irrational.

    This is OPEN for k ≥ 5. -/
def Erdos252Conjecture : Prop :=
  ∀ k ≥ 1, Irrational (divisorPowerSum k)

/-- The open part: is Σ σ_k(n)/n! irrational for k ≥ 5? -/
def Erdos252Open : Prop :=
  ∀ k ≥ 5, Irrational (divisorPowerSum k)

/-! ## Conditional Results

The conjecture follows from either of two famous conjectures in number theory:
1. Schinzel's Hypothesis H (about simultaneous prime values of polynomials)
2. The Prime k-tuples Conjecture (Hardy-Littlewood)
-/

/-- **Schinzel's Hypothesis H** (simplified statement):
    If a finite set of integer polynomials satisfies certain necessary conditions
    (irreducible, no fixed prime divisor for the product), then there are
    infinitely many integers where all polynomials simultaneously take prime values.

    Full formalization would require significant polynomial machinery. -/
def SchinzelHypothesisH : Prop :=
  ∀ (polys : Finset (Polynomial ℤ)),
    (∀ p ∈ polys, Polynomial.degree p ≥ 1) →  -- non-constant
    (∀ p ∈ polys, Irreducible p) →            -- irreducible
    (∀ prime : ℕ, prime.Prime →               -- no fixed prime divisor
      ∃ n : ℤ, ¬ (prime : ℤ) ∣ ∏ p ∈ polys, p.eval n) →
    Set.Infinite {n : ℕ | ∀ p ∈ polys, (p.eval (n : ℤ)).natAbs.Prime}

/-- **Schlage-Puchta (2006)**: Schinzel's Hypothesis H implies irrationality for all k. -/
axiom schinzel_implies_all_k :
    SchinzelHypothesisH → Erdos252Conjecture

/-- **Prime k-tuples Conjecture** (simplified):
    Admissible k-tuples of linear forms take prime values infinitely often. -/
def PrimeKTuplesConjecture : Prop :=
  ∀ (k : ℕ) (a : Fin k → ℕ+) (b : Fin k → ℕ),
    (∀ p : ℕ, p.Prime → ∃ n : ℕ, ¬ p ∣ ∏ i, (a i * n + b i)) →
    Set.Infinite {n : ℕ | ∀ i : Fin k, ((a i : ℕ) * n + b i).Prime}

/-- **Friedlander-Luca-Stoiciu (2007)**: Prime k-tuples implies irrationality for k ≥ 4. -/
axiom prime_tuples_implies_ge_4 :
    PrimeKTuplesConjecture → ∀ k ≥ 4, Irrational (divisorPowerSum k)

/-! ## Basic Properties of Divisor Sums

We verify some basic properties and examples.
-/

/-- σ_0(1) = 1 (1 has exactly one divisor). -/
theorem sigma_0_one : sigma 0 1 = 1 := by decide

/-- σ_1(6) = 1 + 2 + 3 + 6 = 12 (6 is a perfect number). -/
theorem sigma_1_six : sigma 1 6 = 12 := by native_decide

/-- σ_0(6) = 4 (6 has divisors 1, 2, 3, 6). -/
theorem sigma_0_six : sigma 0 6 = 4 := by native_decide

/-- σ_2(2) = 1² + 2² = 5. -/
theorem sigma_2_two : sigma 2 2 = 5 := by native_decide

/-- For prime p, σ_k(p) = 1 + p^k.

The divisors of p are {1, p}, so σ_k(p) = 1^k + p^k = 1 + p^k.
-/
axiom sigma_prime (p : ℕ) (hp : p.Prime) (k : ℕ) :
    sigma k p = 1 + p ^ k

/-! ## Convergence

The series Σ σ_k(n)/n! converges absolutely because σ_k(n) ≤ n^(k+1)
and Σ n^(k+1)/n! converges.
-/

/-- Upper bound: σ_k(n) ≤ n · n^k = n^(k+1) (every divisor is ≤ n).

The sum has at most n terms (actually d(n) ≤ n), each at most n^k.
-/
axiom sigma_le_pow (n k : ℕ) : sigma k n ≤ n ^ (k + 1)

/-- The series converges (proof sketch via comparison test).

By sigma_le_pow, σ_k(n)/n! ≤ n^(k+1)/n!, and Σ n^(k+1)/n! converges
since n^(k+1)/n! → 0 faster than any geometric sequence.
-/
axiom divisorPowerSum_summable (k : ℕ) :
    Summable (fun n => (sigma k n : ℝ) / (n ! : ℝ))

/-! ## Summary

**Erdős Problem #252** asks whether Σ_{n=1}^∞ σ_k(n)/n! is irrational for all k ≥ 1.

**Known:**
- k = 0: Yes (Erdős-Straus 1971)
- k = 1, 2: Yes (Erdős 1952)
- k = 3: Yes (Schlage-Puchta 2006, Friedlander-Luca-Stoiciu 2007)
- k = 4: Yes (Pratt 2022)

**Open:**
- k ≥ 5: Unknown unconditionally

**Conditional:**
- All k follow from Schinzel's Hypothesis H
- All k ≥ 4 follow from Prime k-tuples Conjecture
-/

#check Erdos252Conjecture
#check erdos_252_le_4

end Erdos252
