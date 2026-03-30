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
import Mathlib.Data.Nat.Prime.Nth

open Nat Finset Set

namespace Erdos470

/-
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

/-- Decidability of IsPseudoperfect: check all subsets of properDivisors. -/
instance decidableIsPseudoperfect (n : ℕ) : Decidable (IsPseudoperfect n) :=
  decidable_of_iff (∃ S ∈ n.properDivisors.powerset, S.sum id = n) ⟨
    fun ⟨S, hmem, hsum⟩ => ⟨S, Finset.mem_powerset.mp hmem, hsum⟩,
    fun ⟨S, hsub, hsum⟩ => ⟨S, Finset.mem_powerset.mpr hsub, hsum⟩⟩

/-- Decidability of IsWeird. -/
instance decidableIsWeird (n : ℕ) : Decidable (IsWeird n) :=
  inferInstanceAs (Decidable (IsAbundant n ∧ ¬IsPseudoperfect n))

/-
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
theorem seventy_is_abundant : IsAbundant 70 := by
  unfold IsAbundant sigma
  native_decide

/--
70 is not pseudoperfect: no subset of its proper divisors sums to 70.
-/
theorem seventy_not_pseudoperfect : ¬IsPseudoperfect 70 := by
  intro ⟨S, hS_sub, hS_sum⟩
  have : ∀ T ∈ (70 : ℕ).properDivisors.powerset, T.sum id ≠ 70 := by native_decide
  exact this S (Finset.mem_powerset.mpr hS_sub) hS_sum

/--
No number below 70 is weird (verified by exhaustive check over all n < 70).
-/
theorem no_weird_below_70 (n : ℕ) (hn : n < 70) : ¬IsWeird n := by
  have h : ∀ m ∈ Finset.range 70, ¬IsWeird m := by native_decide
  exact h n (Finset.mem_range.mpr hn)

/--
70 is the smallest weird number.
-/
theorem smallest_weird_is_70 : IsWeird 70 ∧ ∀ n < 70, ¬IsWeird n :=
  ⟨⟨seventy_is_abundant, seventy_not_pseudoperfect⟩, no_weird_below_70⟩

/-
## The Second Weird Number: 836

836 = 2² × 11 × 19. Its proper divisors are {1, 2, 4, 11, 19, 22, 38, 44, 76, 209, 418}.
σ(836) > 2 × 836. No subset of proper divisors sums to 836.
-/

/--
836 is the second weird number.
-/
theorem weird_836 : IsWeird 836 := by
  constructor
  · unfold IsAbundant sigma; native_decide
  · intro ⟨S, hS_sub, hS_sum⟩
    have : ∀ T ∈ (836 : ℕ).properDivisors.powerset, T.sum id ≠ 836 := by native_decide
    exact this S (Finset.mem_powerset.mpr hS_sub) hS_sum

/-
## Open Question 1: Odd Weird Numbers

Erdős asked whether any odd weird numbers exist. This remains open
despite extensive computational searches.

Key facts:
- 945 = 3³ × 5 × 7 is the smallest odd abundant number
- 945 is semiperfect (hence not weird)
- Any odd weird must exceed 945

Fang (2022): no odd weird numbers below 10^21.
Liddy-Riedl (2018): any odd weird has ≥ 6 distinct prime divisors.
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
945 = 3³ × 5 × 7 is odd and abundant: σ(945) = 1920 > 1890 = 2 × 945.
-/
theorem nine45_odd_abundant : Odd 945 ∧ IsAbundant 945 := by
  constructor
  · exact ⟨472, by omega⟩
  · unfold IsAbundant sigma; native_decide

/--
945 is semiperfect: its proper divisors contain a subset summing to 945.
-/
theorem nine45_semiperfect : IsPseudoperfect 945 := by
  have : ∃ S ∈ (945 : ℕ).properDivisors.powerset, S.sum id = 945 := by native_decide
  exact let ⟨S, hmem, hsum⟩ := this; ⟨S, Finset.mem_powerset.mp hmem, hsum⟩

/--
945 is not weird (it is semiperfect).
-/
theorem nine45_not_weird : ¬IsWeird 945 := fun ⟨_, hnp⟩ => hnp nine45_semiperfect

/--
No odd number below 945 is abundant.
-/
theorem no_odd_abundant_below_945 (n : ℕ) (hn : n < 945) (hodd : Odd n) :
    ¬IsAbundant n := by
  have h : ∀ m ∈ Finset.range 945, Odd m → ¬IsAbundant m := by native_decide
  exact h n (Finset.mem_range.mpr hn) hodd

/--
Any odd weird number must exceed 945.
-/
theorem odd_weird_gt_945 (n : ℕ) (hw : IsWeird n) (hodd : Odd n) : 945 < n := by
  by_contra h
  push_neg at h
  rcases Nat.lt_or_eq_of_le h with hlt | heq
  · exact absurd hw.1 (no_odd_abundant_below_945 n hlt hodd)
  · exact absurd (heq ▸ nine45_semiperfect) hw.2

/-
## Extending the Odd Weird Bound

The odd abundant numbers (OEIS A005231) begin:
945, 1575, 2205, 2835, 3465, 4095, 4725, ...
Each is semiperfect, with no odd abundant numbers in between.
We push the lower bound for odd weird numbers step by step.
-/

/--
1575 = 3² × 5² × 7 is semiperfect.
-/
theorem fifteen75_semiperfect : IsPseudoperfect 1575 := by
  have : ∃ S ∈ (1575 : ℕ).properDivisors.powerset, S.sum id = 1575 := by native_decide
  exact let ⟨S, hmem, hsum⟩ := this; ⟨S, Finset.mem_powerset.mp hmem, hsum⟩

/--
No odd number in (945, 1575) is abundant.
-/
theorem no_odd_abundant_946_to_1575 (n : ℕ) (hn1 : 945 < n) (hn2 : n < 1575)
    (hodd : Odd n) : ¬IsAbundant n := by
  have h : ∀ m ∈ Finset.Icc 946 1574, Odd m → ¬IsAbundant m := by native_decide
  exact h n (Finset.mem_Icc.mpr ⟨hn1, by omega⟩) hodd

/--
Any odd weird number must exceed 1575.
-/
theorem odd_weird_gt_1575 (n : ℕ) (hw : IsWeird n) (hodd : Odd n) : 1575 < n := by
  have h945 := odd_weird_gt_945 n hw hodd
  by_contra hle
  push_neg at hle
  rcases Nat.lt_or_eq_of_le hle with hlt | heq
  · exact absurd hw.1 (no_odd_abundant_946_to_1575 n h945 hlt hodd)
  · exact absurd (heq ▸ fifteen75_semiperfect) hw.2

/--
2205 = 3² × 5 × 7² is semiperfect.
-/
theorem twenty205_semiperfect : IsPseudoperfect 2205 := by
  have : ∃ S ∈ (2205 : ℕ).properDivisors.powerset, S.sum id = 2205 := by native_decide
  exact let ⟨S, hmem, hsum⟩ := this; ⟨S, Finset.mem_powerset.mp hmem, hsum⟩

/--
No odd number in (1575, 2205) is abundant.
-/
theorem no_odd_abundant_1576_to_2205 (n : ℕ) (hn1 : 1575 < n) (hn2 : n < 2205)
    (hodd : Odd n) : ¬IsAbundant n := by
  have h : ∀ m ∈ Finset.Icc 1576 2204, Odd m → ¬IsAbundant m := by native_decide
  exact h n (Finset.mem_Icc.mpr ⟨hn1, by omega⟩) hodd

/--
Any odd weird number must exceed 2205.
-/
theorem odd_weird_gt_2205 (n : ℕ) (hw : IsWeird n) (hodd : Odd n) : 2205 < n := by
  have h1575 := odd_weird_gt_1575 n hw hodd
  by_contra hle
  push_neg at hle
  rcases Nat.lt_or_eq_of_le hle with hlt | heq
  · exact absurd hw.1 (no_odd_abundant_1576_to_2205 n h1575 hlt hodd)
  · exact absurd (heq ▸ twenty205_semiperfect) hw.2

/--
2835 = 3⁴ × 5 × 7 is semiperfect.
-/
theorem twenty835_semiperfect : IsPseudoperfect 2835 := by
  have : ∃ S ∈ (2835 : ℕ).properDivisors.powerset, S.sum id = 2835 := by native_decide
  exact let ⟨S, hmem, hsum⟩ := this; ⟨S, Finset.mem_powerset.mp hmem, hsum⟩

/--
No odd number in (2205, 2835) is abundant.
-/
theorem no_odd_abundant_2206_to_2835 (n : ℕ) (hn1 : 2205 < n) (hn2 : n < 2835)
    (hodd : Odd n) : ¬IsAbundant n := by
  have h : ∀ m ∈ Finset.Icc 2206 2834, Odd m → ¬IsAbundant m := by native_decide
  exact h n (Finset.mem_Icc.mpr ⟨hn1, by omega⟩) hodd

/--
Any odd weird number must exceed 2835.
-/
theorem odd_weird_gt_2835 (n : ℕ) (hw : IsWeird n) (hodd : Odd n) : 2835 < n := by
  have h2205 := odd_weird_gt_2205 n hw hodd
  by_contra hle
  push_neg at hle
  rcases Nat.lt_or_eq_of_le hle with hlt | heq
  · exact absurd hw.1 (no_odd_abundant_2206_to_2835 n h2205 hlt hodd)
  · exact absurd (heq ▸ twenty835_semiperfect) hw.2

/--
3465 = 3² × 5 × 7 × 11 is semiperfect.
-/
theorem thirty465_semiperfect : IsPseudoperfect 3465 := by
  have : ∃ S ∈ (3465 : ℕ).properDivisors.powerset, S.sum id = 3465 := by native_decide
  exact let ⟨S, hmem, hsum⟩ := this; ⟨S, Finset.mem_powerset.mp hmem, hsum⟩

/--
No odd number in (2835, 3465) is abundant.
-/
theorem no_odd_abundant_2836_to_3465 (n : ℕ) (hn1 : 2835 < n) (hn2 : n < 3465)
    (hodd : Odd n) : ¬IsAbundant n := by
  have h : ∀ m ∈ Finset.Icc 2836 3464, Odd m → ¬IsAbundant m := by native_decide
  exact h n (Finset.mem_Icc.mpr ⟨hn1, by omega⟩) hodd

/--
Any odd weird number must exceed 3465.
-/
theorem odd_weird_gt_3465 (n : ℕ) (hw : IsWeird n) (hodd : Odd n) : 3465 < n := by
  have h2835 := odd_weird_gt_2835 n hw hodd
  by_contra hle
  push_neg at hle
  rcases Nat.lt_or_eq_of_le hle with hlt | heq
  · exact absurd hw.1 (no_odd_abundant_2836_to_3465 n h2835 hlt hodd)
  · exact absurd (heq ▸ thirty465_semiperfect) hw.2

/--
4095 = 3² × 5 × 7 × 13 is semiperfect.
-/
theorem forty95_semiperfect : IsPseudoperfect 4095 := by
  have : ∃ S ∈ (4095 : ℕ).properDivisors.powerset, S.sum id = 4095 := by native_decide
  exact let ⟨S, hmem, hsum⟩ := this; ⟨S, Finset.mem_powerset.mp hmem, hsum⟩

/--
No odd number in (3465, 4095) is abundant.
-/
theorem no_odd_abundant_3466_to_4095 (n : ℕ) (hn1 : 3465 < n) (hn2 : n < 4095)
    (hodd : Odd n) : ¬IsAbundant n := by
  have h : ∀ m ∈ Finset.Icc 3466 4094, Odd m → ¬IsAbundant m := by native_decide
  exact h n (Finset.mem_Icc.mpr ⟨hn1, by omega⟩) hodd

/--
Any odd weird number must exceed 4095.
-/
theorem odd_weird_gt_4095 (n : ℕ) (hw : IsWeird n) (hodd : Odd n) : 4095 < n := by
  have h3465 := odd_weird_gt_3465 n hw hodd
  by_contra hle
  push_neg at hle
  rcases Nat.lt_or_eq_of_le hle with hlt | heq
  · exact absurd hw.1 (no_odd_abundant_3466_to_4095 n h3465 hlt hodd)
  · exact absurd (heq ▸ forty95_semiperfect) hw.2

/--
4725 = 3³ × 5² × 7 is semiperfect.
-/
theorem forty725_semiperfect : IsPseudoperfect 4725 := by
  have : ∃ S ∈ (4725 : ℕ).properDivisors.powerset, S.sum id = 4725 := by native_decide
  exact let ⟨S, hmem, hsum⟩ := this; ⟨S, Finset.mem_powerset.mp hmem, hsum⟩

/--
No odd number in (4095, 4725) is abundant.
-/
theorem no_odd_abundant_4096_to_4725 (n : ℕ) (hn1 : 4095 < n) (hn2 : n < 4725)
    (hodd : Odd n) : ¬IsAbundant n := by
  have h : ∀ m ∈ Finset.Icc 4096 4724, Odd m → ¬IsAbundant m := by native_decide
  exact h n (Finset.mem_Icc.mpr ⟨hn1, by omega⟩) hodd

/--
Any odd weird number must exceed 4725, covering the first seven odd abundant
numbers (945, 1575, 2205, 2835, 3465, 4095, 4725) — all verified semiperfect.
-/
theorem odd_weird_gt_4725 (n : ℕ) (hw : IsWeird n) (hodd : Odd n) : 4725 < n := by
  have h4095 := odd_weird_gt_4095 n hw hodd
  by_contra hle
  push_neg at hle
  rcases Nat.lt_or_eq_of_le hle with hlt | heq
  · exact absurd hw.1 (no_odd_abundant_4096_to_4725 n h4095 hlt hodd)
  · exact absurd (heq ▸ forty725_semiperfect) hw.2

/-
## Computational Bounds on Odd Weird Numbers

Fang (2022) showed there are no odd weird numbers below 10^21.
Liddy and Riedl (2018) showed that any odd weird must have at least
6 distinct prime divisors.
-/

/--
The number of distinct prime divisors of n.
-/
def numPrimeDivisors (n : ℕ) : ℕ :=
  (n.divisors.filter Nat.Prime).card

/--
Liddy-Riedl (2018): any odd weird number has at least 6 distinct prime divisors.
This is axiomatized — the proof requires deep sieve-theoretic arguments.
-/
axiom liddy_riedl_6_primes (n : ℕ) (hw : IsWeird n) (hodd : Odd n) :
    6 ≤ numPrimeDivisors n

/-
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
theorem properDivisors_lt (n d : ℕ) (hd : d ∈ n.properDivisors) : d < n :=
  (Nat.mem_properDivisors.1 hd).2

/--
70 is primitive weird (trivially, since no number below 70 is weird).
-/
theorem seventy_is_primitive_weird : IsPrimitiveWeird 70 := by
  constructor
  · exact ⟨seventy_is_abundant, seventy_not_pseudoperfect⟩
  · intro d hd
    exact no_weird_below_70 d (properDivisors_lt 70 d hd)

/-
## Open Question 2: Infinitely Many Primitive Weird Numbers
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

/-
## Conditional Result: Prime Gaps

Melfi (2015) proved that there are infinitely many primitive weird numbers
under the assumption that prime gaps satisfy p_{n+1} - p_n < √p_n / 10
for all large n. This would follow from conjectures like Cramér's.
-/

/--
The n-th prime: nthPrime 0 = 2, nthPrime 1 = 3, nthPrime 2 = 5, etc.
-/
noncomputable def nthPrime (n : ℕ) : ℕ := Nat.nth Nat.Prime n

/--
The first prime is 2 (from Mathlib).
-/
theorem nthPrime_zero : nthPrime 0 = 2 := Nat.nth_prime_zero_eq_two

/--
Every nthPrime output is prime (from Mathlib).
-/
theorem nthPrime_prime (n : ℕ) : Nat.Prime (nthPrime n) :=
  Nat.nth_mem_of_infinite Nat.infinite_setOf_prime n

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

/-
## Positive Density of Weird Numbers

Benkoski and Erdős proved that weird numbers have positive asymptotic density.
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

/--
The abundancy index of n.
-/
noncomputable def abundancyIndex (n : ℕ) : ℚ := sigma n / n

/-
## Summary

**Erdős Problem #470**: Both questions remain OPEN.
Key established results:
1. 70 is the smallest weird number, 836 is the second
2. 70 is primitive weird
3. Any odd weird exceeds 4725 (first 7 odd abundants verified semiperfect)
4. Weird numbers have positive density (Benkoski-Erdős)
5. Melfi's conditional infinitude of primitive weirds
-/

/--
**Complete summary of Erdős Problem #470.**
-/
theorem erdos_470 :
    (IsWeird 70 ∧ ∀ n < 70, ¬IsWeird n) ∧
    IsWeird 836 ∧
    IsPrimitiveWeird 70 ∧
    (∀ n, IsWeird n → Odd n → 4725 < n) ∧
    (∃ c > 0, ∀ᶠ N in Filter.atTop, (↑((WeirdSet ∩ {n | n ≤ N}).ncard) : ℝ) / N ≥ c) ∧
    ((∀ᶠ n in Filter.atTop, (primeGap n : ℝ) < Real.sqrt (nthPrime n) / 10) →
      PrimitiveWeirdSet.Infinite) :=
  ⟨smallest_weird_is_70, weird_836, seventy_is_primitive_weird,
   odd_weird_gt_4725, benkoski_erdos_density, melfi_conditional⟩

end Erdos470
