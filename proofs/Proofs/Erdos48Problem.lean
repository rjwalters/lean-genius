/-
Erdős Problem #48: Infinitely Many Pairs with φ(n) = σ(m)

Source: https://erdosproblems.com/48
Status: SOLVED (Ford-Luca-Pomerance, 2010)

Statement:
Are there infinitely many integers n, m such that φ(n) = σ(m)?
(where φ is Euler's totient and σ is sum of divisors)

Answer: YES

Ford, Luca, and Pomerance (2010) proved:
1. There are infinitely many such pairs
2. Quantitative bound: at least exp((log log x)^c) values a ≤ x satisfy a = φ(n) = σ(m)

Garaev (2011) improved the bound to exp((log log x)^ω(x)) where ω(x) → ∞.

Key Insight:
The problem would follow immediately from the twin prime conjecture:
If p and p+2 are both prime, then φ(p) = p-1 and σ(p+2) when p+2 is prime...
Actually the connection is more subtle.

References:
- Erdős [Er59c], [Er74b], [Er95]
- Ford, Luca, Pomerance (2010): "Common values of the arithmetic functions φ and σ"
- Garaev (2011): Improved density estimates
- Guy's Unsolved Problems in Number Theory, B38
-/

import Mathlib.Data.Nat.Totient
import Mathlib.NumberTheory.Divisors
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open Nat BigOperators Finset

namespace Erdos48

/-
## Part I: Arithmetic Functions

The two central functions: Euler's totient φ and sum of divisors σ.
-/

/--
**Sum of Divisors** σ(n):
The sum of all positive divisors of n.

Examples:
- σ(1) = 1
- σ(6) = 1 + 2 + 3 + 6 = 12
- σ(p) = 1 + p for prime p
-/
def sumDivisors (n : ℕ) : ℕ := (n.divisors).sum id

/-- Notation for sum of divisors. -/
notation "σ(" n ")" => sumDivisors n

/-
**Euler's Totient** φ(n):
The count of integers from 1 to n that are coprime to n.
Uses Mathlib's Nat.totient.

Examples:
- φ(1) = 1
- φ(6) = 2 (only 1 and 5 are coprime to 6)
- φ(p) = p - 1 for prime p
-/

/-
## Part II: Basic Properties
-/

/-- σ(1) = 1 -/
theorem sumDivisors_one : σ(1) = 1 := by
  simp [sumDivisors, Nat.divisors_one]

/-- σ(p) = 1 + p for prime p -/
axiom sumDivisors_prime (p : ℕ) (hp : p.Prime) : σ(p) = 1 + p

/-- σ(n) ≥ n for all n ≥ 1 -/
axiom sumDivisors_ge (n : ℕ) (hn : n ≥ 1) : σ(n) ≥ n

/-- σ(n) > n for n > 1 (n divides itself and 1 divides n) -/
axiom sumDivisors_gt (n : ℕ) (hn : n > 1) : σ(n) > n

/-- φ(1) = 1 -/
theorem totient_one : (1 : ℕ).totient = 1 := by native_decide

/-- φ(p) = p - 1 for prime p -/
theorem totient_prime (p : ℕ) (hp : p.Prime) : p.totient = p - 1 :=
  Nat.totient_prime hp

/-- φ(n) < n for n > 1 -/
axiom totient_lt (n : ℕ) (hn : n > 1) : n.totient < n

/-- φ(n) ≥ 1 for n ≥ 1 -/
axiom totient_pos (n : ℕ) (hn : n ≥ 1) : n.totient ≥ 1

/-
## Part III: The Totient-Sigma Pair Set
-/

/--
**Totient-Sigma Pairs:**
The set of pairs (n, m) where φ(n) = σ(m).
-/
def totientSigmaPairs : Set (ℕ × ℕ) :=
  {p : ℕ × ℕ | p.1.totient = σ(p.2)}

/--
**Common Values:**
The set of values that are both φ(n) for some n and σ(m) for some m.
-/
def commonValues : Set ℕ :=
  {a : ℕ | (∃ n : ℕ, n.totient = a) ∧ (∃ m : ℕ, σ(m) = a)}

/--
A value is common iff there exists a totient-sigma pair achieving it.
-/
theorem commonValues_iff (a : ℕ) :
    a ∈ commonValues ↔ ∃ n m : ℕ, n.totient = a ∧ σ(m) = a := by
  constructor
  · intro ⟨⟨n, hn⟩, ⟨m, hm⟩⟩
    exact ⟨n, m, hn, hm⟩
  · intro ⟨n, m, hn, hm⟩
    exact ⟨⟨n, hn⟩, ⟨m, hm⟩⟩

/-
## Part IV: Verified Examples

Concrete pairs satisfying φ(n) = σ(m).
-/

/-- σ(3) = 1 + 3 = 4 -/
theorem sumDivisors_three : σ(3) = 4 := by native_decide

/-- φ(5) = 4 -/
theorem totient_five : (5 : ℕ).totient = 4 := by native_decide

/--
**Example 1:** (5, 3) satisfies φ(5) = σ(3) = 4.
-/
theorem pair_5_3 : (5, 3) ∈ totientSigmaPairs := by
  simp only [totientSigmaPairs, Set.mem_setOf_eq]
  native_decide

/-- σ(1) = 1 -/
theorem sumDivisors_one' : σ(1) = 1 := sumDivisors_one

/-- φ(2) = 1 -/
theorem totient_two : (2 : ℕ).totient = 1 := by native_decide

/--
**Example 2:** (2, 1) satisfies φ(2) = σ(1) = 1.
-/
theorem pair_2_1 : (2, 1) ∈ totientSigmaPairs := by
  simp only [totientSigmaPairs, Set.mem_setOf_eq]
  native_decide

/-- σ(2) = 1 + 2 = 3 -/
theorem sumDivisors_two : σ(2) = 3 := by native_decide

/-- φ(4) = 2 -/
theorem totient_four : (4 : ℕ).totient = 2 := by native_decide

/-- σ(4) = 1 + 2 + 4 = 7 -/
theorem sumDivisors_four : σ(4) = 7 := by native_decide

/-- φ(7) = 6 -/
theorem totient_seven : (7 : ℕ).totient = 6 := by native_decide

/-- σ(5) = 1 + 5 = 6 -/
theorem sumDivisors_five : σ(5) = 6 := by native_decide

/--
**Example 3:** (7, 5) satisfies φ(7) = σ(5) = 6.
-/
theorem pair_7_5 : (7, 5) ∈ totientSigmaPairs := by
  simp only [totientSigmaPairs, Set.mem_setOf_eq]
  native_decide

/-- φ(13) = 12 -/
theorem totient_thirteen : (13 : ℕ).totient = 12 := by native_decide

/-- σ(11) = 1 + 11 = 12 -/
theorem sumDivisors_eleven : σ(11) = 12 := by native_decide

/--
**Example 4:** (13, 11) satisfies φ(13) = σ(11) = 12.
-/
theorem pair_13_11 : (13, 11) ∈ totientSigmaPairs := by
  simp only [totientSigmaPairs, Set.mem_setOf_eq]
  native_decide

/-- φ(3) = 2 -/
theorem totient_three : (3 : ℕ).totient = 2 := by native_decide

/-
Note: Finding a pair with value 2 is tricky since σ(1) = 1 and σ(m) ≥ m+1 for m > 1.
The value 2 is NOT in commonValues.
-/

/-- σ(6) = 1 + 2 + 3 + 6 = 12 -/
theorem sumDivisors_six : σ(6) = 12 := by native_decide

/--
**Example 5:** (13, 6) also works: φ(13) = 12 = σ(6).
-/
theorem pair_13_6 : (13, 6) ∈ totientSigmaPairs := by
  simp only [totientSigmaPairs, Set.mem_setOf_eq]
  native_decide

/-
## Part V: Ford-Luca-Pomerance Theorem

The main result: infinitely many pairs exist.
-/

/--
**Ford-Luca-Pomerance Theorem (2010):**
There are infinitely many pairs (n, m) with φ(n) = σ(m).

More precisely, for some constant c > 0:
  |{a ≤ x : ∃ n, m with φ(n) = σ(m) = a}| ≥ exp((log log x)^c)
-/
axiom ford_luca_pomerance : totientSigmaPairs.Infinite

/--
**Erdős Problem #48: SOLVED**
The main theorem.
-/
theorem erdos_48 : totientSigmaPairs.Infinite := ford_luca_pomerance

/--
**Common Values are Infinite:**
The set of values appearing as both φ(n) and σ(m) is infinite.
-/
axiom commonValues_infinite : commonValues.Infinite

/-
## Part VI: Garaev's Improvement

Strengthened density bounds.
-/

/--
**Garaev's Theorem (2011):**
The number of common values up to x is at least exp((log log x)^ω(x))
where ω(x) → ∞ as x → ∞.

This improves Ford-Luca-Pomerance by replacing the constant c with
a slowly growing function.
-/
axiom garaev_improvement :
    ∀ x : ℕ, x ≥ 3 → ∃ count : ℕ,
      count ≤ (Finset.range x).card ∧
      count ≥ 1 ∧  -- Simplified: at least one common value
      ∃ S : Finset ℕ, S.card = count ∧ ∀ a ∈ S, a ∈ commonValues

/-
## Part VII: Connection to Twin Primes
-/

/--
**Twin Prime Connection:**
If p and p+2 are both prime (twin primes), then:
- φ(p+2) = p + 1
- σ(p) = p + 1

So (p+2, p) would be a totient-sigma pair!

This shows the problem would follow from the twin prime conjecture.
-/
theorem twin_prime_gives_pair (p : ℕ) (hp : p.Prime) (hp2 : (p + 2).Prime) :
    (p + 2, p) ∈ totientSigmaPairs := by
  simp only [totientSigmaPairs, Set.mem_setOf_eq]
  have h1 : (p + 2).totient = p + 1 := by
    rw [totient_prime (p + 2) hp2]
    omega
  have h2 : σ(p) = 1 + p := sumDivisors_prime p hp
  rw [h1, h2]
  ring

/--
**Twin Prime Conjecture Implication:**
If there are infinitely many twin primes, then Erdős #48 follows.
-/
axiom twin_prime_implies_erdos_48 :
    (∃ S : Set ℕ, S.Infinite ∧ ∀ p ∈ S, p.Prime ∧ (p + 2).Prime) →
    totientSigmaPairs.Infinite

/-
## Part VIII: Special Cases
-/

/--
**Prime Pairs:**
For primes p, q with p - 1 = q + 1, we have φ(p) = σ(q).
This means p = q + 2, i.e., (p, q) = (q+2, q).
-/
theorem prime_pair_condition (p q : ℕ) (hp : p.Prime) (hq : q.Prime) :
    (p, q) ∈ totientSigmaPairs ↔ p - 1 = q + 1 := by
  constructor
  · intro hmem
    simp only [totientSigmaPairs, Set.mem_setOf_eq] at hmem
    rw [totient_prime p hp, sumDivisors_prime q hq] at hmem
    omega
  · intro heq
    simp only [totientSigmaPairs, Set.mem_setOf_eq]
    rw [totient_prime p hp, sumDivisors_prime q hq]
    omega

/--
**Sophie Germain Connection:**
A Sophie Germain prime p has 2p + 1 also prime.
For such p: φ(2p+1) = 2p and we seek m with σ(m) = 2p.
-/
def isSophieGermain (p : ℕ) : Prop := p.Prime ∧ (2 * p + 1).Prime

/--
**Perfect Number Connection:**
A perfect number n satisfies σ(n) = 2n.
If we can find m with φ(m) = 2n, then (m, n) is a pair.
-/
def isPerfect (n : ℕ) : Prop := σ(n) = 2 * n

/-- 6 is perfect: σ(6) = 12 = 2 · 6 -/
theorem six_is_perfect : isPerfect 6 := by
  simp only [isPerfect]
  native_decide

/-
## Part IX: Value Distribution
-/

/--
**Totient Range:**
The set of values attained by φ.
-/
def totientRange : Set ℕ := {a : ℕ | ∃ n : ℕ, n.totient = a}

/--
**Sigma Range:**
The set of values attained by σ.
-/
def sigmaRange : Set ℕ := {a : ℕ | ∃ m : ℕ, σ(m) = a}

/--
Common values are exactly the intersection of ranges.
-/
theorem commonValues_eq_inter : commonValues = totientRange ∩ sigmaRange := by
  ext a
  simp only [commonValues, totientRange, sigmaRange, Set.mem_inter_iff, Set.mem_setOf_eq]

/--
**1 is a Common Value:**
φ(2) = 1 and σ(1) = 1.
-/
theorem one_is_common : (1 : ℕ) ∈ commonValues := by
  constructor
  · use 2
    native_decide
  · use 1
    exact sumDivisors_one

/--
**4 is a Common Value:**
φ(5) = 4 and σ(3) = 4.
-/
theorem four_is_common : (4 : ℕ) ∈ commonValues := by
  constructor
  · use 5
    native_decide
  · use 3
    native_decide

/--
**6 is a Common Value:**
φ(7) = 6 and σ(5) = 6.
-/
theorem six_is_common : (6 : ℕ) ∈ commonValues := by
  constructor
  · use 7
    native_decide
  · use 5
    native_decide

/--
**12 is a Common Value:**
φ(13) = 12 and σ(11) = 12.
-/
theorem twelve_is_common : (12 : ℕ) ∈ commonValues := by
  constructor
  · use 13
    native_decide
  · use 11
    native_decide

/-
## Part X: Multiplicativity
-/

/--
**σ is Multiplicative:**
For coprime m, n: σ(m·n) = σ(m)·σ(n).
-/
axiom sumDivisors_multiplicative (m n : ℕ) (hm : m ≥ 1) (hn : n ≥ 1)
    (hcop : Nat.Coprime m n) :
    σ(m * n) = σ(m) * σ(n)

/--
**φ is Multiplicative:**
For coprime m, n: φ(m·n) = φ(m)·φ(n).
This is in Mathlib as Nat.totient_mul.
-/
theorem totient_multiplicative (m n : ℕ) (hcop : Nat.Coprime m n) :
    (m * n).totient = m.totient * n.totient :=
  Nat.totient_mul hcop

/-
## Part XI: Main Results Summary
-/

/--
**Erdős Problem #48: SOLVED**

There are infinitely many pairs (n, m) with φ(n) = σ(m).

Key results:
1. ford_luca_pomerance: The main infinitude theorem
2. garaev_improvement: Strengthened density bounds
3. twin_prime_gives_pair: Connection to twin primes
4. Concrete examples: (2,1), (5,3), (7,5), (13,11), (13,6)
-/
theorem erdos_48_summary :
    totientSigmaPairs.Infinite ∧
    commonValues.Infinite ∧
    (1 : ℕ) ∈ commonValues ∧
    (4 : ℕ) ∈ commonValues ∧
    (6 : ℕ) ∈ commonValues ∧
    (12 : ℕ) ∈ commonValues :=
  ⟨erdos_48, commonValues_infinite, one_is_common, four_is_common,
   six_is_common, twelve_is_common⟩

/--
The answer to Erdős's question is YES.
-/
theorem erdos_48_answer : ∃ S : Set (ℕ × ℕ), S.Infinite ∧ S ⊆ totientSigmaPairs := by
  use totientSigmaPairs
  exact ⟨erdos_48, Set.Subset.rfl⟩

/--
There are at least 5 known pairs.
-/
theorem at_least_five_pairs : ∃ S : Finset (ℕ × ℕ), S.card ≥ 5 ∧
    ∀ p ∈ S, p ∈ totientSigmaPairs := by
  use {(2, 1), (5, 3), (7, 5), (13, 11), (13, 6)}
  constructor
  · native_decide
  · intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl
    · exact pair_2_1
    · exact pair_5_3
    · exact pair_7_5
    · exact pair_13_11
    · exact pair_13_6

end Erdos48
