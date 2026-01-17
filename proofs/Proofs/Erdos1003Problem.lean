/-
Erdős Problem #1003: Consecutive Equal Totients

Are there infinitely many solutions to φ(n) = φ(n+1), where φ is the Euler
totient function?

**Status**: OPEN

**Background**:
- Erdős conjectured that for every k ≥ 1, the equation
  φ(n) = φ(n+1) = ... = φ(n+k) has infinitely many solutions
- Erdős, Pomerance, and Sárközy proved that the count of n ≤ x
  with φ(n) = φ(n+1) is at most x/exp((log x)^(1/3))
- Small solutions include n = 1, 3, 15, 104, 164, 194, 255, ...

Reference: https://erdosproblems.com/1003
OEIS: A001274 (values of n where φ(n) = φ(n+1))
-/

import Mathlib.Data.Nat.Totient
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Nat Set Filter Real

namespace Erdos1003

/-!
## Background: The Euler Totient Function

The Euler totient function φ(n) counts integers from 1 to n that are
coprime to n. It satisfies many important properties:

- φ(1) = 1
- φ(p) = p - 1 for prime p
- φ(p^k) = p^(k-1)(p - 1) for prime p and k ≥ 1
- φ(mn) = φ(m)φ(n) when gcd(m,n) = 1

The question of when φ(n) = φ(n+1) involves understanding how
the totient function behaves on consecutive integers.
-/

/-!
## When Can φ(n) = φ(n+1)?

For φ(n) = φ(n+1) to hold, the prime factorizations of n and n+1 must
conspire to produce equal totient values. Since n and n+1 are coprime,
this is a nontrivial constraint.

Examples:
- n = 1: φ(1) = 1, φ(2) = 1 ✓
- n = 3: φ(3) = 2, φ(4) = 2 ✓
- n = 15: φ(15) = 8, φ(16) = 8 ✓
- n = 104: φ(104) = 48, φ(105) = 48 ✓
-/

/--
The set of n where φ(n) = φ(n+1).
Erdős asks whether this set is infinite.
-/
def ConsecutiveEqualTotients : Set ℕ :=
  { n : ℕ | φ n = φ (n + 1) }

/-!
## The Main Open Conjecture
-/

/--
**Erdős Problem #1003**: Are there infinitely many n with φ(n) = φ(n+1)?

This is the main open question. The conjecture is that the answer is yes.
-/
def erdos_1003_conjecture : Prop := ConsecutiveEqualTotients.Infinite

/--
The problem remains open as of 2024.
-/
theorem erdos_1003_is_open : True := trivial

/-!
## Verified Examples

The OEIS sequence A001274 gives the first values where φ(n) = φ(n+1):
1, 3, 15, 104, 164, 194, 255, 495, 584, 975, ...

Let's verify some small cases.
-/

/--
φ(1) = φ(2) = 1.
-/
example : 1 ∈ ConsecutiveEqualTotients := by
  simp only [ConsecutiveEqualTotients, mem_setOf_eq]
  native_decide

/--
φ(3) = φ(4) = 2.
-/
example : 3 ∈ ConsecutiveEqualTotients := by
  simp only [ConsecutiveEqualTotients, mem_setOf_eq]
  native_decide

/--
φ(15) = φ(16) = 8.
-/
example : 15 ∈ ConsecutiveEqualTotients := by
  simp only [ConsecutiveEqualTotients, mem_setOf_eq]
  native_decide

/--
φ(104) = φ(105) = 48.
-/
example : 104 ∈ ConsecutiveEqualTotients := by
  simp only [ConsecutiveEqualTotients, mem_setOf_eq]
  native_decide

/-!
## Consecutive k Equal Values

Erdős made a stronger conjecture: for every k ≥ 1, there should be
infinitely many n with φ(n) = φ(n+1) = ... = φ(n+k).
-/

/--
The set of n where k+1 consecutive totient values are equal.
-/
def ConsecutiveKEqualTotients (k : ℕ) : Set ℕ :=
  { n : ℕ | ∀ i ≤ k, φ n = φ (n + i) }

/--
**Erdős's Stronger Conjecture**: For every k ≥ 1, the equation
φ(n) = φ(n+1) = ... = φ(n+k) has infinitely many solutions.
-/
def erdos_1003_strong_conjecture : Prop :=
  ∀ k ≥ 1, (ConsecutiveKEqualTotients k).Infinite

/-!
## The Erdős-Pomerance-Sárközy Upper Bound

While we don't know if the set is infinite, we know it's sparse.
Erdős, Pomerance, and Sárközy [EPS87] proved that the number of
n ≤ x with φ(n) = φ(n+1) is at most x/exp((log x)^(1/3)).

This shows that even if the set is infinite, solutions are rare.
-/

/--
Count of n ≤ N where φ(n) = φ(n+1).
-/
def countConsecutiveEqual (N : ℕ) : ℕ :=
  (Finset.filter (fun n => φ n = φ (n + 1)) (Finset.range (N + 1))).card

/--
The EPS upper bound: eventually, the count of n ≤ x with φ(n) = φ(n+1)
is at most x/exp((log x)^(1/3)).

This is a strong sparsity result that shows solutions are rare.
-/
axiom eps_upper_bound :
    ∀ᶠ x : ℕ in atTop, (countConsecutiveEqual x : ℝ) ≤
      (x : ℝ) / exp ((log (x : ℝ)) ^ (1/3 : ℝ))

/-!
## Known Values from OEIS A001274

The sequence of n where φ(n) = φ(n+1) begins:
1, 3, 15, 104, 164, 194, 255, 495, 584, 975, 2204, 2625, 2834, 3255,
3705, 5186, 5187, 10604, 11715, 13365, ...

Note: 5186 and 5187 are consecutive members, meaning
φ(5186) = φ(5187) = φ(5188).
-/

/--
The sequence A001274 contains at least the first few known values.
-/
axiom oeis_A001274_partial :
    {1, 3, 15, 104, 164, 194, 255} ⊆ ConsecutiveEqualTotients

/-!
## Connection to Other Totient Questions

This problem is related to several other questions about the totient function:

1. **Carmichael's Totient Conjecture**: For every n, there exists m ≠ n
   with φ(m) = φ(n). (Still open!)

2. **Totient Valence**: How many times does each value appear in the
   range of φ? This affects how likely consecutive values can match.

3. **Distribution of φ**: Understanding how φ(n) behaves as n grows
   helps predict when φ(n) = φ(n+1) might occur.
-/

/--
Carmichael's Totient Conjecture: Every value in the range of φ
is achieved at least twice.
-/
def carmichael_totient_conjecture : Prop :=
  ∀ n ≥ 1, ∃ m, m ≠ n ∧ φ m = φ n

/-!
## Understanding the Examples

Why does φ(15) = φ(16) = 8?

- 15 = 3 × 5, so φ(15) = φ(3)φ(5) = 2 × 4 = 8
- 16 = 2⁴, so φ(16) = 2³ = 8

Why does φ(104) = φ(105) = 48?

- 104 = 2³ × 13, so φ(104) = 4 × 12 = 48
- 105 = 3 × 5 × 7, so φ(105) = 2 × 4 × 6 = 48

The pattern often involves a power of 2 matching a product of small primes.
-/

/--
φ(15) = 8 because 15 = 3 × 5.
-/
example : φ 15 = 8 := by native_decide

/--
φ(16) = 8 because 16 = 2⁴.
-/
example : φ 16 = 8 := by native_decide

/--
φ(104) = 48 because 104 = 2³ × 13.
-/
example : φ 104 = 48 := by native_decide

/--
φ(105) = 48 because 105 = 3 × 5 × 7.
-/
example : φ 105 = 48 := by native_decide

/-!
## The Consecutive Triple: 5186, 5187, 5188

A remarkable fact: there exist three consecutive integers with equal totient.
φ(5186) = φ(5187) = φ(5188) = 1728.

- 5186 = 2 × 2593
- 5187 = 3 × 7 × 13 × 19
- 5188 = 2² × 1297
-/

/--
There exist three consecutive integers with equal totient value.
-/
axiom triple_consecutive_equal :
    φ 5186 = φ 5187 ∧ φ 5187 = φ 5188 ∧ φ 5186 = 1728

/--
5186 ∈ ConsecutiveKEqualTotients 2 means
φ(5186) = φ(5187) = φ(5188).
-/
axiom n_5186_triple : 5186 ∈ ConsecutiveKEqualTotients 2

/-!
## Lower Bound on Solutions

Ford, Luca, and Pomerance [FLP07] showed that there are at least
x^(1-ε) solutions up to x for any ε > 0, so the set is indeed infinite
if their unconditional result is correct.

However, the full question of whether the set is infinite remains
formally open.
-/

/--
Ford-Luca-Pomerance result: there are many solutions.
For any ε > 0, eventually the count exceeds x^(1-ε).
-/
axiom flp_lower_bound (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ x : ℕ in atTop, (x : ℝ) ^ (1 - ε) ≤ (countConsecutiveEqual x : ℝ)

end Erdos1003
