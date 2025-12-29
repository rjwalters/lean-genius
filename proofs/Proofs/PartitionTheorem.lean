import Archive.Wiedijk100Theorems.Partition
import Mathlib.Combinatorics.Enumerative.Partition
import Mathlib.Tactic

/-!
# The Partition Theorem (Euler's Partition Identity)

## What This Proves
The Partition Theorem (Wiedijk's 100 Theorems #45) states that the number of partitions
of a natural number n into distinct parts equals the number of partitions of n into
odd parts.

**Mathematical Statement:**
For any natural number n:
  |{partitions of n with distinct parts}| = |{partitions of n with only odd parts}|

## Example

For n = 5:
- **Distinct parts**: {5}, {4+1}, {3+2} → 3 partitions
- **Odd parts**: {5}, {3+1+1}, {1+1+1+1+1} → 3 partitions

For n = 8:
- **Distinct parts**: {8}, {7+1}, {6+2}, {5+3}, {5+2+1}, {4+3+1} → 6 partitions
- **Odd parts**: {7+1}, {5+3}, {5+1+1+1}, {3+3+1+1}, {3+1+1+1+1+1}, {1+1+1+1+1+1+1+1} → 6 partitions

## Approach
- **Foundation (from Mathlib):** We use `Archive.Wiedijk100Theorems.Partition` which
  provides the complete proof using generating functions. The proof shows that the
  generating functions for odd and distinct partitions are equal.
- **Original Contributions:** This file provides a pedagogical wrapper with:
  1. Clear explanation of the bijection principle
  2. Concrete examples of partition counting
  3. Connection to generating functions
  4. Historical context (Euler, 1748)
- **Proof Techniques Demonstrated:** Generating functions, finite products,
  coefficient comparison.

## Status
- [x] Complete proof
- [x] Uses Mathlib for main results
- [x] Proves partition equality
- [x] Pedagogical commentary
- [x] Complete (no sorries)

## Mathlib Dependencies
- `Nat.Partition` : Definition of integer partitions
- `Nat.Partition.odds` : Partitions with only odd parts
- `Nat.Partition.distincts` : Partitions with distinct parts
- `Theorems100.partition_theorem` : The main theorem

## Historical Note
This theorem was first proved by Leonhard Euler in 1748 using his pioneering work
on generating functions. It's one of the foundational results in partition theory
and combinatorics.

Euler's original proof compared the infinite products:
- Distinct parts: ∏_{k≥1} (1 + x^k)
- Odd parts: ∏_{k≥0} 1/(1 - x^(2k+1))

He showed these are equal by factoring (1-x^(2k))/(1-x^k) = 1 + x^k.

## The Bijection (Intuitive Explanation)

There is a beautiful bijective proof of this theorem:

**From distinct to odd:**
1. Take a partition into distinct parts
2. Write each part in binary: e.g., 6 = 4 + 2 = 2² + 2¹
3. Replace each 2^i with (2^i copies of 1) grouped appropriately
4. The result is a partition into odd parts

**More explicitly:**
For each part d, write d = 2^a × b where b is odd.
Then d contributes 2^a copies of the odd number b.

**Example:** Distinct partition {6, 5, 3} of 14
- 6 = 2¹ × 3 → two 3s
- 5 = 2⁰ × 5 → one 5
- 3 = 2⁰ × 3 → one 3
Result: {5, 3, 3, 3} (all odd) ✓

This bijection is called the "Glaisher correspondence" after James Whitbread Lee Glaisher.

## Wiedijk's 100 Theorems: #45
-/

namespace PartitionTheorem

open Finset Nat

/-! ## Part I: Integer Partitions

An integer partition of n is a way of writing n as a sum of positive integers,
where the order of summands doesn't matter. -/

/-- A partition of n is represented as a multiset of positive integers
summing to n. -/
example (n : ℕ) : Type := Nat.Partition n

/-- The parts of a partition are the summands. -/
example (n : ℕ) (p : Nat.Partition n) : Multiset ℕ := p.parts

/-- The sum of parts equals n (by definition). -/
example (n : ℕ) (p : Nat.Partition n) : (p.parts.sum : ℕ) = n := p.parts_sum

/-! ## Part II: Distinct Partitions

A partition is "distinct" if no part appears more than once. -/

/-- The set of distinct partitions of n.
A partition is distinct if its parts form a set (no repetitions). -/
example (n : ℕ) : Finset (Nat.Partition n) := Nat.Partition.distincts n

/-- A partition is distinct iff its parts have no duplicates. -/
theorem distinct_iff_nodup {n : ℕ} (p : Nat.Partition n) :
    p ∈ Nat.Partition.distincts n ↔ p.parts.Nodup := by
  simp [Nat.Partition.distincts]

/-! ## Part III: Odd Partitions

A partition is "odd" if every part is an odd number. -/

/-- The set of odd partitions of n.
A partition is odd if every part is odd (not divisible by 2). -/
example (n : ℕ) : Finset (Nat.Partition n) := Nat.Partition.odds n

/-- A partition is odd iff all its parts are odd numbers. -/
theorem odd_iff_all_odd {n : ℕ} (p : Nat.Partition n) :
    p ∈ Nat.Partition.odds n ↔ ∀ i ∈ p.parts, ¬Even i := by
  simp [Nat.Partition.odds]

/-! ## Part IV: The Partition Theorem -/

/-- **The Partition Theorem (Wiedijk #45)**

The number of partitions of n into distinct parts equals
the number of partitions of n into odd parts.

This is proved via generating functions:
- Distinct GF: ∏_{k=1}^∞ (1 + x^k)
- Odd GF: ∏_{k=0}^∞ 1/(1 - x^{2k+1})

These are equal because:
∏(1 + x^k) = ∏(1 - x^{2k})/(1 - x^k)
           = [∏_{k even}(1-x^k)] / [∏_{all k}(1-x^k)]
           = 1 / [∏_{k odd}(1-x^k)]
           = ∏ 1/(1 - x^{2k+1})
-/
theorem partition_theorem (n : ℕ) :
    (Nat.Partition.distincts n).card = (Nat.Partition.odds n).card :=
  (Theorems100.partition_theorem n).symm

/-! ## Part V: Concrete Examples

Let's verify the theorem for small values of n. -/

/-- For n = 0: one empty partition, which is both distinct and odd. -/
example : (Nat.Partition.distincts 0).card = 1 := by native_decide
example : (Nat.Partition.odds 0).card = 1 := by native_decide

/-- For n = 1: {1} is the only partition, which is both distinct and odd. -/
example : (Nat.Partition.distincts 1).card = 1 := by native_decide
example : (Nat.Partition.odds 1).card = 1 := by native_decide

/-- For n = 2: Distinct: {2}. Odd: {1+1}. Both have 1 partition. -/
example : (Nat.Partition.distincts 2).card = 1 := by native_decide
example : (Nat.Partition.odds 2).card = 1 := by native_decide

/-- For n = 3: Distinct: {3}, {2+1}. Odd: {3}, {1+1+1}. Both have 2. -/
example : (Nat.Partition.distincts 3).card = 2 := by native_decide
example : (Nat.Partition.odds 3).card = 2 := by native_decide

/-- For n = 4: Distinct: {4}, {3+1}. Odd: {3+1}, {1+1+1+1}. Both have 2. -/
example : (Nat.Partition.distincts 4).card = 2 := by native_decide
example : (Nat.Partition.odds 4).card = 2 := by native_decide

/-- For n = 5: 3 partitions of each type.
Distinct: {5}, {4+1}, {3+2}
Odd: {5}, {3+1+1}, {1+1+1+1+1} -/
example : (Nat.Partition.distincts 5).card = 3 := by native_decide
example : (Nat.Partition.odds 5).card = 3 := by native_decide

/-- For n = 6: 4 partitions of each type. -/
example : (Nat.Partition.distincts 6).card = 4 := by native_decide
example : (Nat.Partition.odds 6).card = 4 := by native_decide

/-- For n = 7: 5 partitions of each type. -/
example : (Nat.Partition.distincts 7).card = 5 := by native_decide
example : (Nat.Partition.odds 7).card = 5 := by native_decide

/-- For n = 8: 6 partitions of each type.
Distinct: {8}, {7+1}, {6+2}, {5+3}, {5+2+1}, {4+3+1}
Odd: {7+1}, {5+3}, {5+1+1+1}, {3+3+1+1}, {3+1+1+1+1+1}, {1×8} -/
example : (Nat.Partition.distincts 8).card = 6 := by native_decide
example : (Nat.Partition.odds 8).card = 6 := by native_decide

/-! ## Part VI: The Generating Function Approach

The classical proof uses generating functions (formal power series).

**Generating function for distinct partitions:**
Each part k can appear 0 or 1 time, so the GF is:
  ∏_{k≥1} (1 + x^k) = (1+x)(1+x²)(1+x³)...

**Generating function for odd partitions:**
Each odd part (2k+1) can appear any number of times, so the GF is:
  ∏_{k≥0} 1/(1-x^{2k+1}) = 1/((1-x)(1-x³)(1-x⁵)...)

**The Key Identity:**
  (1 + x^k) = (1 - x^{2k})/(1 - x^k)

Therefore:
  ∏_{k≥1}(1+x^k) = ∏_{k≥1}(1-x^{2k})/∏_{k≥1}(1-x^k)
                 = ∏_{k≥1}(1-x^{2k}) / ∏_{k≥1}(1-x^k)

The numerator has factors for all even exponents.
The denominator has factors for all exponents.
Cancellation leaves only factors for odd exponents in the denominator:
                 = 1 / ∏_{k odd}(1-x^k)

This equals the generating function for odd partitions! -/

/-! ## Part VII: The Bijective Proof (Glaisher's Correspondence)

Beyond generating functions, there's a direct bijection:

**Distinct → Odd:**
1. For each distinct part d, write d = 2^a × b where b is odd
2. Replace d with 2^a copies of the odd part b

**Odd → Distinct:**
1. Group identical odd parts
2. If an odd part b appears m times, write m in binary: m = Σ 2^{aᵢ}
3. Replace (m copies of b) with distinct parts {2^{aᵢ} × b}

**Example (Distinct → Odd):**
Start: {6, 5, 3}
- 6 = 2¹ × 3 → {3, 3} (two 3s)
- 5 = 2⁰ × 5 → {5} (one 5)
- 3 = 2⁰ × 3 → {3} (one 3)
Result: {5, 3, 3, 3}

**Example (Odd → Distinct):**
Start: {5, 3, 3, 3}
- One 5: 1 = 2⁰ → {1×5} = {5}
- Three 3s: 3 = 2⁰ + 2¹ → {1×3, 2×3} = {3, 6}
Result: {6, 5, 3}

This bijection is invertible, proving the theorem combinatorially. -/

/-! ## Part VIII: Connection to Pentagonal Number Theorem

Euler's partition identity is closely related to his Pentagonal Number Theorem:

  ∏_{k≥1}(1-x^k) = Σ_{n=-∞}^{∞} (-1)^n x^{n(3n-1)/2}

The exponents n(3n-1)/2 are the generalized pentagonal numbers:
  0, 1, 2, 5, 7, 12, 15, 22, 26, ...

This gives a recurrence for the partition function p(n):
  p(n) = p(n-1) + p(n-2) - p(n-5) - p(n-7) + p(n-12) + p(n-15) - ...

with signs alternating in pairs (+, +, -, -, +, +, ...) -/

/-! ## Part IX: Values of the Partition Counts

The sequence of distinct/odd partition counts for n = 0, 1, 2, ... is:
  1, 1, 1, 2, 2, 3, 4, 5, 6, 8, 10, 12, 15, 18, 22, 27, ...

This is OEIS sequence A000009 (number of partitions into distinct parts).

Asymptotically, the number of partitions into distinct parts grows like:
  exp(π√(n/3)) / (4 × 3^(1/4) × n^(3/4))
-/

#check partition_theorem
#check distinct_iff_nodup
#check odd_iff_all_odd

end PartitionTheorem
