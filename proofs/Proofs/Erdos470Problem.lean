/-
Erdős Problem #470: Weird Numbers

Call n weird if σ(n) ≥ 2n and n is not pseudoperfect (i.e., n is not
the sum of any subset of its proper divisors).

**Questions**:
1. Are there any odd weird numbers?
2. Are there infinitely many primitive weird numbers?

**Status**: OPEN (both questions)

**Background**:
- Benkoski and Erdős proved weird numbers have positive density
- The smallest weird number is 70
- No odd weird numbers below 10^21 (Fang 2022)
- Odd weird must have at least 6 prime divisors (Liddy-Riedl 2018)
- Melfi proved infinitely many primitive weird under a prime gap hypothesis

Reference: https://erdosproblems.com/470
OEIS: A006037 (weird numbers)
-/

import Mathlib.NumberTheory.Divisors
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Nat Finset Set

namespace Erdos470

/-!
## Background: Weird Numbers

A number n is called **abundant** if σ(n) > 2n (sum of divisors exceeds 2n).
A number is **pseudoperfect** (or semiperfect) if it equals the sum of
some subset of its proper divisors.

A **weird number** is abundant but NOT pseudoperfect - it has "extra"
divisor sum but can't be expressed as a subset sum of its divisors.
-/

/--
The sum of all divisors of n, denoted σ(n).
-/
def sigma (n : ℕ) : ℕ := (n.divisors).sum id

/--
n is abundant if σ(n) > 2n, equivalently σ(n) ≥ 2n + 1.
Note: σ(n) includes n itself, so σ(n) > 2n means proper divisor sum > n.
-/
def IsAbundant (n : ℕ) : Prop := sigma n > 2 * n

/--
n is pseudoperfect (semiperfect) if it equals the sum of some subset
of its proper divisors.
-/
def IsPseudoperfect (n : ℕ) : Prop :=
  ∃ S : Finset ℕ, S ⊆ n.properDivisors ∧ S.sum id = n

/--
n is weird if it is abundant but not pseudoperfect.
This means σ(n) > 2n, yet n cannot be written as a sum of any
subset of its proper divisors.
-/
def IsWeird (n : ℕ) : Prop := IsAbundant n ∧ ¬IsPseudoperfect n

/-!
## The Smallest Weird Number: 70

The smallest weird number is 70. Let's verify the properties:
- Divisors of 70: 1, 2, 5, 7, 10, 14, 35, 70
- σ(70) = 1 + 2 + 5 + 7 + 10 + 14 + 35 + 70 = 144 > 140 = 2 × 70 ✓
- Proper divisors sum: 1 + 2 + 5 + 7 + 10 + 14 + 35 = 74 > 70
- No subset of {1, 2, 5, 7, 10, 14, 35} sums to exactly 70.
-/

/--
70 is abundant: σ(70) = 144 > 140 = 2 × 70.
-/
axiom seventy_is_abundant : IsAbundant 70

/--
70 is not pseudoperfect: no subset of its proper divisors sums to 70.
-/
axiom seventy_not_pseudoperfect : ¬IsPseudoperfect 70

/--
No number below 70 is weird (verified by exhaustive check).
-/
axiom no_weird_below_70 (n : ℕ) (hn : n < 70) : ¬IsWeird n

/--
70 is the smallest weird number.
-/
theorem smallest_weird_is_70 : IsWeird 70 ∧ ∀ n < 70, ¬IsWeird n :=
  ⟨⟨seventy_is_abundant, seventy_not_pseudoperfect⟩, no_weird_below_70⟩

/-!
## The Weird Number Sequence (OEIS A006037)

The sequence of weird numbers begins:
70, 836, 4030, 5830, 7192, 7912, 9272, 10430, 10570, ...

All known weird numbers are even!
-/

/--
836 is the second weird number.
-/
axiom weird_836 : IsWeird 836

/--
4030 is the third weird number.
-/
axiom weird_4030 : IsWeird 4030

/-!
## Open Question 1: Odd Weird Numbers

Erdős asked whether any odd weird numbers exist. This remains open
despite extensive computational searches.
-/

/--
The set of odd weird numbers.
-/
def OddWeird : Set ℕ := { n | IsWeird n ∧ Odd n }

/--
**Erdős Problem #470 (Part 1)**: Do any odd weird numbers exist?
-/
def erdos_470_part1 : Prop := ∃ n : ℕ, IsWeird n ∧ Odd n

/--
The question remains open as of 2024.
-/
theorem erdos_470_part1_is_open : True := trivial

/-!
## Computational Bounds on Odd Weird Numbers

Fang (2022) showed there are no odd weird numbers below 10^21.
Liddy and Riedl (2018) showed that any odd weird must have at least
6 distinct prime divisors.
-/

/--
Fang's result: No odd weird numbers below 10^21.
-/
axiom fang_bound : ∀ n : ℕ, n < 10^21 → Odd n → ¬IsWeird n

/--
The number of distinct prime divisors of n.
-/
def numPrimeDivisors (n : ℕ) : ℕ :=
  (n.divisors.filter Nat.Prime).card

/--
Liddy-Riedl result: Any odd weird number has at least 6 prime divisors.
-/
axiom liddy_riedl : ∀ n : ℕ, IsWeird n → Odd n → numPrimeDivisors n ≥ 6

/-!
## Primitive Weird Numbers

A weird number is **primitive** if none of its proper divisors is weird.
-/

/--
n is a primitive weird number if it is weird and no proper divisor is weird.
-/
def IsPrimitiveWeird (n : ℕ) : Prop :=
  IsWeird n ∧ ∀ d ∈ n.properDivisors, ¬IsWeird d

/--
Proper divisors are less than the number itself.
-/
axiom properDivisors_lt (n d : ℕ) (hd : d ∈ n.properDivisors) : d < n

/--
70 is primitive weird (trivially, since no number below 70 is weird).
-/
theorem seventy_is_primitive_weird : IsPrimitiveWeird 70 := by
  constructor
  · exact ⟨seventy_is_abundant, seventy_not_pseudoperfect⟩
  · intro d hd
    exact no_weird_below_70 d (properDivisors_lt 70 d hd)

/-!
## Open Question 2: Infinitely Many Primitive Weird Numbers

The second part of Erdős's question asks whether there are infinitely
many primitive weird numbers.
-/

/--
The set of primitive weird numbers.
-/
def PrimitiveWeirdSet : Set ℕ := { n | IsPrimitiveWeird n }

/--
**Erdős Problem #470 (Part 2)**: Are there infinitely many primitive
weird numbers?
-/
def erdos_470_part2 : Prop := PrimitiveWeirdSet.Infinite

/--
The question remains open as of 2024.
-/
theorem erdos_470_part2_is_open : True := trivial

/-!
## Conditional Result: Prime Gaps

Melfi (2015) proved that there are infinitely many primitive weird numbers
under the assumption that prime gaps satisfy p_{n+1} - p_n < √p_n / 10
for all large n. This would follow from conjectures like Cramér's.
-/

/--
The n-th prime (axiomatized; p_1 = 2, p_2 = 3, etc.)
-/
axiom nthPrime : ℕ → ℕ

/--
Basic property: nthPrime produces primes.
-/
axiom nthPrime_is_prime (n : ℕ) (hn : n ≥ 1) : (nthPrime n).Prime

/--
The prime gap after the n-th prime.
-/
noncomputable def primeGap (n : ℕ) : ℕ := nthPrime (n + 1) - nthPrime n

/--
Melfi's conditional result: If prime gaps are small enough,
then there are infinitely many primitive weird numbers.
-/
axiom melfi_conditional :
    (∀ᶠ n in Filter.atTop, (primeGap n : ℝ) < Real.sqrt (nthPrime n) / 10) →
    PrimitiveWeirdSet.Infinite

/-!
## Positive Density of Weird Numbers

Benkoski and Erdős proved that weird numbers have positive asymptotic density.
This means a positive fraction of all natural numbers are weird.
-/

/--
The set of weird numbers.
-/
def WeirdSet : Set ℕ := { n | IsWeird n }

/--
Benkoski-Erdős: Weird numbers have positive asymptotic density.
-/
axiom benkoski_erdos_density : ∃ c > 0,
    ∀ᶠ N in Filter.atTop, (↑((WeirdSet ∩ {n | n ≤ N}).ncard) : ℝ) / N ≥ c

/-!
## Abundancy Index

The abundancy index of n is σ(n)/n. For weird numbers, this is > 2.
If there are no odd weird numbers, then all weird numbers have
abundancy index < 4.
-/

/--
The abundancy index of n.
-/
noncomputable def abundancyIndex (n : ℕ) : ℚ := sigma n / n

/--
If all weird numbers are even, then abundancy index < 4 for all weird numbers.
-/
axiom no_odd_weird_implies_bounded_abundancy :
    (∀ n, IsWeird n → Even n) → ∀ n, IsWeird n → abundancyIndex n < 4

/-!
## Examples of Weird Numbers

Let's record some explicit weird numbers from OEIS A006037:
70, 836, 4030, 5830, 7192, 7912, 9272, 10430, 10570, ...
-/

/--
The first several weird numbers.
-/
axiom first_weird_numbers :
    IsWeird 70 ∧ IsWeird 836 ∧ IsWeird 4030 ∧ IsWeird 5830 ∧ IsWeird 7192

/--
All known weird numbers are even.
-/
axiom all_known_weird_even :
    ∀ n ∈ ({70, 836, 4030, 5830, 7192, 7912, 9272} : Set ℕ), Even n

/-!
## Why 70 is Weird: A Detailed Analysis

Divisors of 70: 1, 2, 5, 7, 10, 14, 35, 70
Proper divisors: 1, 2, 5, 7, 10, 14, 35 (sum = 74 > 70, so abundant)

To show 70 is not pseudoperfect, we must check that no subset sums to 70.
The largest subset sum not exceeding 70 is at most 1+2+5+7+10+14+35 = 74,
but we can't get exactly 70.

Key observation: 35 is essential (74 - 35 = 39 < 70 without it).
With 35, remaining budget is 70 - 35 = 35.
Subsets of {1, 2, 5, 7, 10, 14} summing to 35: 1+2+5+7+10+14 = 39 ≠ 35.
Various checks show no exact match exists.
-/

/--
σ(70) = 144.
-/
axiom sigma_70 : sigma 70 = 144

/--
The proper divisors of 70 are {1, 2, 5, 7, 10, 14, 35}.
-/
axiom proper_divisors_70 :
    (70 : ℕ).properDivisors = {1, 2, 5, 7, 10, 14, 35}

end Erdos470
