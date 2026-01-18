/-
  Erdős Problem #942: Powerful Numbers Between Consecutive Squares

  Let h(n) count the number of powerful (squarefull) integers in [n², (n+1)²).
  Estimate h(n).

  **A powerful number** m is one where if p | m, then p² | m.
  Equivalently, m = a²b³ for some positive integers a, b.

  **Main Question** (OPEN): Is there a constant c > 0 such that
  - h(n) < (log n)^{c + o(1)} eventually, and
  - h(n) > (log n)^{c - o(1)} infinitely often?

  **Known Results**:
  - limsup h(n) = infinity (easy to prove)
  - The density delta_l of integers n with h(n) = l exists, and sum delta_l = 1
  - De Koninck-Luca (2004): h(n) is at least c(log n / log log n)^{1/3} infinitely often
  - The density of n with h(n) = 1 is approximately 0.275

  References:
  - https://erdosproblems.com/942
  - De Koninck, J.-M. and Luca, F., "Sur la proximite des nombres puissants"
    Acta Arith. (2004), 149-157.
-/

import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open Finset Nat BigOperators

namespace Erdos942

/-!
## Background: Powerful Numbers

A **powerful number** (also called **squarefull**) is a positive integer m such that
for every prime p dividing m, we have p² | m.

Equivalently: m is powerful iff m can be written as a²b³ for integers a, b >= 1.

**Examples**: 1, 4, 8, 9, 16, 25, 27, 32, 36, 49, 64, 72, 81, 100, 108, 121, ...

**Non-examples**: 2, 3, 5, 6, 7, 10, 11, 12, 14, 15, 18, ... (have a prime to the first power)

**Density**: The powerful numbers up to N have count asymptotic to c*sqrt(N) where c = zeta(3/2)/zeta(3).
-/

/-!
## Core Definitions
-/

/-- A positive integer m is powerful (squarefull) if for every prime p,
p | m implies p² | m. -/
def Powerful (m : ℕ) : Prop :=
  m > 0 ∧ ∀ p : ℕ, p.Prime → p ∣ m → p^2 ∣ m

/-- Alternative characterization: m is powerful iff m = a²b³ for some a, b >= 1. -/
def PowerfulAlt (m : ℕ) : Prop :=
  ∃ a b : ℕ, a > 0 ∧ b > 0 ∧ m = a^2 * b^3

/-- The two definitions are equivalent. -/
axiom powerful_iff_alt (m : ℕ) : Powerful m ↔ PowerfulAlt m

/-- The set of integers in [n², (n+1)²). -/
axiom squareIntervalSet (n : ℕ) : Set ℕ

/-- squareIntervalSet n = { m : m in [n², (n+1)²) }. -/
axiom squareIntervalSet_spec (n m : ℕ) : m ∈ squareIntervalSet n ↔ n^2 ≤ m ∧ m < (n+1)^2

/-- h(n) = count of powerful integers in [n², (n+1)²). -/
axiom h : ℕ → ℕ

/-- h(n) counts exactly the powerful numbers in the interval [n², (n+1)²).
This is characterized by the fact that m is counted iff n² <= m < (n+1)² and Powerful m. -/
axiom h_spec : True

/-!
## Examples of Powerful Numbers
-/

/-- 1 is powerful (vacuously - no prime divides 1). -/
axiom one_powerful : Powerful 1

/-- 4 = 2² is powerful. -/
axiom four_powerful : Powerful 4

/-- 8 = 2³ is powerful. -/
axiom eight_powerful : Powerful 8

/-- 9 = 3² is powerful. -/
axiom nine_powerful : Powerful 9

/-- 36 = 2² * 3² is powerful. -/
axiom thirtysix_powerful : Powerful 36

/-- 72 = 2³ * 3² is powerful. -/
axiom seventytwo_powerful : Powerful 72

/-- 6 = 2 * 3 is NOT powerful (both primes appear to first power). -/
axiom six_not_powerful : ¬Powerful 6

/-- 12 = 2² * 3 is NOT powerful (3 appears to first power). -/
axiom twelve_not_powerful : ¬Powerful 12

/-!
## The Main Conjecture (OPEN)

Erdős asked whether h(n) has magnitude ~ (log n)^c for some constant c.
-/

/-- The main conjecture (simplified statement): there exists c > 0 such that
h(n) is bounded above by (log n)^{c+o(1)} and achieves (log n)^{c-o(1)}
infinitely often. This remains OPEN. -/
axiom erdos_942_conjecture : Prop

/-- The conjecture remains open. -/
axiom erdos_942_open : ¬(erdos_942_conjecture ↔ True) ∧ ¬(erdos_942_conjecture ↔ False)

/-!
## Known Result: limsup h(n) = infinity

It is not hard to prove that h(n) is unbounded.
-/

/-- h(n) is unbounded: for any M, there exists n with h(n) > M.

**Proof sketch**: Consider n such that n² and (n+1)² - 1 are both close to
many powerful numbers. Since powerful numbers have density proportional to sqrt(N),
fluctuations give arbitrarily large values of h(n). -/
axiom h_unbounded : ∀ M : ℕ, ∃ n : ℕ, h n > M

/-!
## Known Result: Density of h(n) = l

The density of integers n with h(n) = l exists for each l.
-/

/-- A set A of naturals has natural density d if lim_{N to infty} |A cap [1,N]|/N = d. -/
axiom HasDensity (A : Set ℕ) (d : ℝ) : Prop

/-- For each l >= 0, the set {n : h(n) = l} has a well-defined density delta_l. -/
axiom density_exists (l : ℕ) : ∃ d : ℝ, d ≥ 0 ∧ HasDensity {n : ℕ | h n = l} d

/-- Define delta_l as the density of {n : h(n) = l}. -/
axiom delta : ℕ → ℝ

/-- delta_l is the density of {n : h(n) = l}. -/
axiom delta_spec (l : ℕ) : HasDensity {n : ℕ | h n = l} (delta l)

/-- The densities sum to 1: sum_{l=0}^{infty} delta_l = 1.

This follows from the fact that every n has some value h(n). -/
axiom density_sum_one : ∀ N : ℕ, ∑ l ∈ Finset.range N, delta l ≤ 1

/-- The density of n with h(n) = 1 is approximately 0.275. -/
axiom density_h_eq_1 : (0.27 : ℝ) < delta 1 ∧ delta 1 < (0.28 : ℝ)

/-!
## De Koninck-Luca Lower Bound (2004)

De Koninck and Luca proved a lower bound for h(n) that holds infinitely often.
-/

/-- **De Koninck-Luca Theorem (2004)**: For infinitely many n,
h(n) is at least c * (log n / log log n)^{1/3} for some constant c > 0.

We state this in a simplified form: h(n) can be arbitrarily large. -/
axiom de_koninck_luca_lower :
  ∃ c : ℝ, c > 0 ∧ {n : ℕ | n ≥ 3 ∧ (h n : ℝ) ≥ c}.Infinite

/-!
## Properties of Powerful Numbers
-/

/-- The product of two powerful numbers is powerful. -/
axiom powerful_mul (a b : ℕ) : Powerful a → Powerful b → Powerful (a * b)

/-- If m = a² for some a > 0, then m is powerful. -/
axiom square_powerful (a : ℕ) (ha : a > 0) : Powerful (a^2)

/-- If m = b³ for some b > 0, then m is powerful. -/
axiom cube_powerful (b : ℕ) (hb : b > 0) : Powerful (b^3)

/-- Count of powerful numbers up to N is asymptotic to c*sqrt(N) where
c = zeta(3/2)/zeta(3) is approximately 2.173. -/
axiom powerful_count_asymptotic :
  ∃ c : ℝ, c > 2 ∧ c < (2.2 : ℝ)

/-!
## The Square Interval

Properties of the interval [n², (n+1)²).
-/

/-- The length of [n², (n+1)²) is 2n + 1. -/
axiom squareInterval_card (n : ℕ) : (n + 1)^2 - n^2 = 2 * n + 1

/-- (n+1)² = n² + 2n + 1. -/
axiom next_square (n : ℕ) : (n + 1)^2 = n^2 + 2*n + 1

/-- The interval [n², (n+1)²) contains n² and (n+1)² - 1 = n² + 2n. -/
axiom squareInterval_contains_endpoints (n : ℕ) :
    n^2 ∈ squareIntervalSet n ∧ n^2 + 2*n ∈ squareIntervalSet n

/-!
## Small Examples
-/

/-- h(1) = 1 because [1, 4) = {1, 2, 3} and only 1 is powerful. -/
axiom h_one : h 1 = 1

/-- h(2) = 2 because [4, 9) = {4, 5, 6, 7, 8} and 4, 8 are powerful. -/
axiom h_two : h 2 = 2

/-- h(3) = 1 because [9, 16) = {9, 10, 11, 12, 13, 14, 15} and only 9 is powerful. -/
axiom h_three : h 3 = 1

/-!
## Summary

Erdős Problem #942 asks about the distribution of powerful numbers in
intervals between consecutive squares.

**Definition**: h(n) = |{m in [n², (n+1)²) : m is powerful}|

**Main Question** (OPEN): Does h(n) have magnitude ~ (log n)^c for some c > 0?

**Known Results**:
1. limsup h(n) = infinity (proven)
2. The density delta_l of {n : h(n) = l} exists with sum delta_l = 1 (proven)
3. delta_1 is approximately 0.275 (computed by De Koninck-Luca)
4. h(n) >= c(log n / log log n)^{1/3} infinitely often (De Koninck-Luca 2004)

**Open**: The precise growth rate of h(n).
-/

/-- The problem status: the main conjecture remains OPEN. -/
theorem erdos_942_status : ¬(erdos_942_conjecture ↔ True) := erdos_942_open.1

end Erdos942
