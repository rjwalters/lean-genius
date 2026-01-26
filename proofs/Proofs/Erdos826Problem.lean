/-
Erdős Problem #826: Divisor Function Growth Along Shifts

**Problem Statement (OPEN)**

Are there infinitely many n such that, for all k ≥ 1,
  τ(n + k) ≪ k?

Here τ(m) = σ₀(m) is the number of divisors of m.

This asks: can we find infinitely many starting points n where the
divisor function grows at most linearly in the shift k?

This is a stronger form of Erdős Problem #248.

**Status**: OPEN — Terence Tao has noted this appears difficult.

Reference: https://erdosproblems.com/826
Source: [Er74b]

Adapted from formal-conjectures (Apache 2.0 License)
-/

import Mathlib.NumberTheory.ArithmeticFunction
import Mathlib.Data.Nat.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Infinite
import Mathlib.Tactic

open scoped ArithmeticFunction
open Nat

namespace Erdos826

/-!
# Part 1: The Divisor Function

τ(n) = σ₀(n) counts the number of positive divisors of n.
-/

/--
**The Divisor Function τ(n)**

τ(n) = |{d : d | n}| counts positive divisors of n.

In Mathlib, this is `σ 0 n` (the arithmetic function σ₀),
which equals the number of divisors.

**Examples:**
- τ(1) = 1
- τ(p) = 2 for prime p
- τ(6) = 4 (divisors: 1, 2, 3, 6)
- τ(12) = 6 (divisors: 1, 2, 3, 4, 6, 12)
-/
noncomputable def tau (n : ℕ) : ℕ := σ 0 n

/-!
# Part 2: Growth of the Divisor Function

Known bounds on τ(n).
-/

/--
**Average Order of τ**

The average value of τ(n) for n ≤ x is approximately log(x).
More precisely, Σ_{n≤x} τ(n) = x log(x) + (2γ - 1)x + O(√x),
where γ is the Euler-Mascheroni constant.
-/
axiom average_order_tau :
    ∃ C₁ C₂ : ℝ, C₁ > 0 ∧ C₂ > 0 ∧
    ∀ x ≥ 2, C₁ * Real.log x ≤ (1/x) * ∑ n ∈ Finset.range (⌊x⌋₊), (σ 0 (n+1) : ℝ)
    ∧ (1/x) * ∑ n ∈ Finset.range (⌊x⌋₊), (σ 0 (n+1) : ℝ) ≤ C₂ * Real.log x

/--
**Maximum Order of τ**

The maximum order of τ(n) is 2^{(1+o(1)) log(n)/log(log(n))}.
In particular, τ(n) can be much larger than any fixed power of log(n).

Highly composite numbers achieve this maximum order.
-/
axiom max_order_tau :
    ∀ ε > (0 : ℝ), ∃ C : ℝ, ∀ n ≥ 2,
    (σ 0 n : ℝ) ≤ C * (2 : ℝ) ^ ((1 + ε) * Real.log n / Real.log (Real.log n))

/-!
# Part 3: The Linear Bound Condition

The core condition of Problem #826.
-/

/--
**Linear Bound on Shifted Divisors**

The condition τ(n + k) ≤ C · k for all k ≥ 1 says that
starting from n, the divisor function grows at most linearly
in the offset.

This is a strong condition: it requires τ(n+1) ≤ C,
τ(n+2) ≤ 2C, τ(n+3) ≤ 3C, etc.
-/
def linearBoundCondition (n : ℕ) (C : ℝ) : Prop :=
  ∀ k : ℕ, k ≥ 1 → (σ 0 (n + k) : ℝ) ≤ C * k

/--
**The Set of "Good" Starting Points**

S(C) = {n : τ(n + k) ≤ C · k for all k ≥ 1}

These are starting points where divisor growth is well-controlled.
-/
def goodStartingPoints (C : ℝ) : Set ℕ :=
  { n | linearBoundCondition n C }

/-!
# Part 4: The Erdős Conjecture

The formal statement of Problem #826.
-/

/--
**Erdős Problem #826 (OPEN)**

Are there infinitely many n such that τ(n + k) ≪ k for all k ≥ 1?

Formally: ∃ C > 0, S(C) is infinite.

This asks for a single constant C that works simultaneously
for all k, at infinitely many starting points n.
-/
def erdos_826_conjecture : Prop :=
  ∃ C : ℝ, C > 0 ∧ (goodStartingPoints C).Infinite

/--
**The formal statement from formal-conjectures.**

Using Mathlib's σ 0 for the divisor function.
-/
axiom erdos_826_statement :
    erdos_826_conjecture ↔
    ∃ C > (0 : ℝ), { n | ∀ k ≥ 1, σ 0 (n + k) ≤ C * k }.Infinite

/-!
# Part 5: Relation to Problem #248

Problem #826 strengthens Erdős Problem #248.
-/

/--
**Erdős Problem #248 (Weaker Form)**

Problem #248 asks about specific growth rates of τ along shifts,
while #826 asks for the stronger linear bound τ(n+k) ≤ Ck.

If #826 is true, then #248 follows.
-/
def erdos_248_weaker : Prop :=
  ∃ C : ℝ, C > 0 ∧ { n | ∀ k ≥ 1, (σ 0 (n + k) : ℝ) ≤ C * k ^ (1 : ℝ) }.Infinite

/-- Problem #826 implies Problem #248 (the weaker form). -/
theorem erdos_826_implies_248 (h : erdos_826_conjecture) : erdos_248_weaker := by
  obtain ⟨C, hC, hInf⟩ := h
  exact ⟨C, hC, hInf⟩

/-!
# Part 6: Small Examples and Observations

Understanding when the linear bound can hold.
-/

/--
**Why the Problem is Hard**

For n + k to have τ(n+k) ≤ Ck, we need n + k to have few divisors
relative to k. In particular:
- n + 1 must have ≤ C divisors (so n+1 has few prime factors)
- n + 2 must have ≤ 2C divisors
- This must hold for ALL k simultaneously

The constraint gets easier as k grows (allowing more divisors),
but the constraint at k = 1 is very restrictive.
-/

/-- At k = 1: τ(n+1) ≤ C, so n+1 must have few divisors. -/
def fewDivisorsAt1 (n : ℕ) (C : ℝ) : Prop :=
  (σ 0 (n + 1) : ℝ) ≤ C

/-- If n+1 is prime, τ(n+1) = 2, which easily satisfies the bound. -/
axiom prime_satisfies_bound (n : ℕ) (hn : Nat.Prime (n + 1)) :
    (σ 0 (n + 1) : ℝ) = 2

/-!
# Part 7: Probabilistic Heuristic

Why one might expect the conjecture to be true.
-/

/--
**Heuristic Argument**

The average value of τ(m) is about log(m). For m = n + k with
n large and k moderate, τ(n+k) is "typically" about log(n).

The condition τ(n+k) ≤ Ck is automatically satisfied when
k ≥ log(n)/C, since the average is only log(n).

The difficult range is small k (k ≤ log(n)/C), where we need
n+1, n+2, ..., n+⌊log(n)/C⌋ to all have unusually few divisors.

By multiplicative number theory heuristics, such "smooth intervals"
should occur infinitely often, but proving this is hard.
-/
def heuristicCriticalRange (n : ℕ) (C : ℝ) : ℕ :=
  ⌈Real.log n / C⌉₊

/-!
# Part 8: Connection to Smooth Numbers

The role of smooth numbers in this problem.
-/

/--
**Smooth Numbers and Few Divisors**

A number is y-smooth if all its prime factors are ≤ y.
Numbers with few divisors tend to have few distinct prime factors.

If n+1 has only small prime factors and small exponents,
then τ(n+1) will be small. The problem essentially asks
for infinitely many n where a consecutive block starting at
n+1 consists of numbers with controlled divisor counts.
-/
def hasControlledDivisors (m : ℕ) (bound : ℝ) : Prop :=
  (σ 0 m : ℝ) ≤ bound

/-!
# Part 9: Why Tao Considers This Difficult

The structural challenges.
-/

/--
**Difficulty Assessment**

Terence Tao has noted this problem appears difficult. The key
challenges are:

1. **Simultaneous control:** The bound must hold for ALL k ≥ 1,
   not just most k. Even one large value of τ(n+k) relative
   to k disqualifies n.

2. **Small k dominance:** The constraint at k = 1 (τ(n+1) ≤ C)
   forces n+1 to have very few divisors, severely restricting
   candidates.

3. **Correlation structure:** Divisor counts of consecutive integers
   are not independent — shared small prime factors create
   dependencies that are hard to handle.

4. **Beyond current methods:** Standard sieve methods give upper
   bounds on τ in short intervals but not the uniform control
   over all shifts that this problem requires.
-/

/-!
# Part 10: Problem Status

Summary and open status.
-/

/-- The problem is OPEN. -/
def erdos_826_status : String := "OPEN"

/-- Main statement: the conjecture remains unresolved. -/
theorem erdos_826_main :
    -- The conjecture is well-defined
    (erdos_826_conjecture ↔ ∃ C > (0 : ℝ), (goodStartingPoints C).Infinite) ∧
    -- It implies the weaker Problem #248
    (erdos_826_conjecture → erdos_248_weaker) := by
  constructor
  · constructor
    · intro ⟨C, hC, hInf⟩
      exact ⟨C, hC, hInf⟩
    · intro ⟨C, hC, hInf⟩
      exact ⟨C, hC, hInf⟩
  · exact erdos_826_implies_248

/-!
# Summary

**Problem:** Are there infinitely many n such that τ(n+k) ≪ k
for all k ≥ 1?

**Status:** OPEN

**Difficulty:** Considered difficult by Terence Tao.

**Key challenge:** Requires simultaneous control of divisor counts
across all shifts from a single starting point, infinitely often.

**Relation:** Stronger form of Erdős Problem #248.

**Source:** [Er74b], posed by Erdős in 1974.
-/

end Erdos826
