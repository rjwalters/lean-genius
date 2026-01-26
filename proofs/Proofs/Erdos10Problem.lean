/-!
# Erdős Problem #10 — Sums of a Prime and Powers of 2

Is there some k such that every sufficiently large integer is the sum of
a prime and at most k powers of 2?

Erdős described this as "probably unattackable." He and Graham conjectured
that no such k exists.

## Key Results

- **Gallagher (1975)**: For any ε > 0 there exists k(ε) such that the set
  of integers representable as a prime plus at most k(ε) powers of 2 has
  lower density at least 1 − ε.
- **Granville–Soundararajan (1998)**: Conjectured that at most 3 powers of
  2 suffice for all odd integers > 1, and hence at most 4 powers of 2
  suffice for all even integers.
- **Grechuk**: Observed that 1117175146 is not the sum of a prime and at
  most 3 powers of 2.
- **Romanoff (1934)**: A positive proportion of integers are the sum of a
  prime and a power of 2.
- There are infinitely many even integers not the sum of a prime and 2
  powers of 2 (covering congruence argument).

*Reference:* [erdosproblems.com/10](https://www.erdosproblems.com/10)
-/

import Mathlib.Tactic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Order.Filter.AtTopBot.Group

open Set Filter

/-! ## Core Definitions -/

/-- The set of natural numbers that can be written as a sum of a prime
and at most `k` powers of 2. We represent the powers-of-2 component
as a multiset of exponents whose cardinality is at most `k`. -/
def sumPrimeAndTwoPows (k : ℕ) : Set ℕ :=
  { n | ∃ (p : ℕ) (pows : Multiset ℕ),
    p.Prime ∧ pows.card ≤ k ∧ n = p + (pows.map (2 ^ ·)).sum }

/-- Asymptotic lower density of a set of natural numbers. We define it as
the liminf of |S ∩ [0,n]| / (n+1). -/
noncomputable def Set.lowerDensity (S : Set ℕ) : ℝ :=
  Filter.liminf (fun n => (↑(Finset.card (Finset.filter (· ∈ S) (Finset.range (n + 1)))) : ℝ)
    / (↑(n + 1) : ℝ)) atTop

/-! ## Main Conjecture -/

/-- **Erdős Problem #10 (Open).**
Is there some k such that every integer > 1 is the sum of a prime and
at most k powers of 2?

Erdős and Graham conjectured the answer is *no*: for every k there exist
arbitrarily large integers not so representable. -/
axiom erdos_10_conjecture :
  ¬ ∃ k : ℕ, {n : ℕ | 1 < n} ⊆ sumPrimeAndTwoPows k

/-! ## Gallagher's Density Theorem -/

/-- **Gallagher (1975).** For any ε > 0 there exists k(ε) such that the
set of integers representable as a prime plus at most k(ε) powers of 2
has lower density at least 1 − ε. -/
axiom gallagher_density (ε : ℝ) (hε : 0 < ε) :
  ∃ k : ℕ, 1 - ε ≤ (sumPrimeAndTwoPows k).lowerDensity

/-! ## Granville–Soundararajan Conjecture -/

/-- **Granville–Soundararajan (1998) — Odd Part.**
Every odd integer > 1 is the sum of a prime and at most 3 powers of 2. -/
axiom granville_soundararajan_odd :
  {n : ℕ | Odd n ∧ 1 < n} ⊆ sumPrimeAndTwoPows 3

/-- **Granville–Soundararajan (1998) — Even Part.**
Every even integer ≥ 2 is the sum of a prime and at most 4 powers of 2. -/
axiom granville_soundararajan_even :
  {n : ℕ | Even n ∧ n ≠ 0} ⊆ sumPrimeAndTwoPows 4

/-! ## Counterexample to k = 3 for Even Integers -/

/-- **Grechuk's observation.** The number 1117175146 is not the sum of
a prime and at most 3 powers of 2. This shows that the Granville–
Soundararajan conjecture cannot be extended to all integers with k = 3. -/
axiom grechuk_counterexample : 1117175146 ∉ sumPrimeAndTwoPows 3

/-! ## Infinitely Many Exceptions for k = 2 -/

/-- There are infinitely many even integers that are not the sum of a
prime and 2 powers of 2. This follows from covering congruence arguments. -/
axiom infinitely_many_exceptions_k2 :
  Set.Infinite ({n : ℕ | Even n} \ sumPrimeAndTwoPows 2)

/-! ## Conjectured Infinitely Many Exceptions for k = 3 -/

/-- It is conjectured (following Grechuk's observation and parity arguments)
that there are infinitely many even integers not the sum of a prime and
at most 3 powers of 2. -/
axiom infinitely_many_exceptions_k3 :
  Set.Infinite ({n : ℕ | Even n} \ sumPrimeAndTwoPows 3)

/-! ## Romanoff's Theorem -/

/-- **Romanoff (1934).** A positive proportion of integers are the sum of
a prime and a power of 2 (i.e., the k = 1 case already has positive
lower density). -/
axiom romanoff_positive_density :
  0 < (sumPrimeAndTwoPows 1).lowerDensity
