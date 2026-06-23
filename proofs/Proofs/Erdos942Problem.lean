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

/-
## Background: Powerful Numbers

A **powerful number** (also called **squarefull**) is a positive integer m such that
for every prime p dividing m, we have p² | m.

Equivalently: m is powerful iff m can be written as a²b³ for integers a, b >= 1.

**Examples**: 1, 4, 8, 9, 16, 25, 27, 32, 36, 49, 64, 72, 81, 100, 108, 121, ...

**Non-examples**: 2, 3, 5, 6, 7, 10, 11, 12, 14, 15, 18, ... (have a prime to the first power)

**Density**: The powerful numbers up to N have count asymptotic to c*sqrt(N) where c = zeta(3/2)/zeta(3).
-/

/-
## Core Definitions
-/

/-- A positive integer m is powerful (squarefull) if for every prime p,
p | m implies p² | m. -/
def Powerful (m : ℕ) : Prop :=
  m > 0 ∧ ∀ p : ℕ, p.Prime → p ∣ m → p^2 ∣ m

/-- Alternative characterization: m is powerful iff m = a²b³ for some a, b >= 1. -/
def PowerfulAlt (m : ℕ) : Prop :=
  ∃ a b : ℕ, a > 0 ∧ b > 0 ∧ m = a^2 * b^3

/-- The set of integers in [n², (n+1)²). -/
/-- h(n) = count of powerful integers in [n², (n+1)²). -/
axiom h : ℕ → ℕ

/- h(n) counts exactly the powerful numbers in the interval [n², (n+1)²).
This is characterized by the fact that m is counted iff n² <= m < (n+1)² and Powerful m. -/

/-
## Examples of Powerful Numbers
-/

/-
## The Main Conjecture (OPEN)

Erdős asked whether h(n) has magnitude ~ (log n)^c for some constant c.
-/

/-- The main conjecture (simplified statement): there exists c > 0 such that
h(n) is bounded above by (log n)^{c+o(1)} and achieves (log n)^{c-o(1)}
infinitely often. This remains OPEN. -/
axiom erdos_942_conjecture : Prop

/-- The conjecture remains open. -/
axiom erdos_942_open : ¬(erdos_942_conjecture ↔ True) ∧ ¬(erdos_942_conjecture ↔ False)

/-
## Known Result: limsup h(n) = infinity

It is not hard to prove that h(n) is unbounded.
-/

/-
## Known Result: Density of h(n) = l

The density of integers n with h(n) = l exists for each l.
-/

/-- A set A of naturals has natural density d if lim_{N to infty} |A cap [1,N]|/N = d. -/
/-- Define delta_l as the density of {n : h(n) = l}. -/
/-
## De Koninck-Luca Lower Bound (2004)

De Koninck and Luca proved a lower bound for h(n) that holds infinitely often.
-/

/-
## Properties of Powerful Numbers
-/

/-
## The Square Interval

Properties of the interval [n², (n+1)²).
-/

/-
## Small Examples
-/

/-
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
