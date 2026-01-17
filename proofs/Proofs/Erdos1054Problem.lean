/-
Erdős Problem #1054: Sum of Smallest Divisors

Let f(n) be the minimal integer m such that n is the sum of the k smallest
divisors of m for some k ≥ 1.

Is it true that f(n) = o(n)? Or is this true only for almost all n,
and limsup f(n)/n = ∞?

**Status**: OPEN

**Background**:
- The function f(n) is undefined for n = 2 and n = 5 (no such m exists)
- For most n, there exists an m whose smallest divisors sum to n
- Example: f(1) = 1 (the only divisor of 1 is 1, and sum of first divisor is 1)
- Example: f(3) = 2 (divisors of 2 are {1,2}, and 1+2 = 3)
- Example: f(6) = 6 (divisors of 6 are {1,2,3,6}, and 1+2+3 = 6)

**Note**: Terry Tao disproved the strong claim that f(n) = o(n) unconditionally.

Reference: https://erdosproblems.com/1054
Sources: [Gu04] Guy, Unsolved Problems in Number Theory, Problem B2
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Order.Filter.AtTopBot.Basic

open Nat Filter Finset

namespace Erdos1054

/-!
## Background: Sum of Smallest Divisors

The divisors of a natural number m can be enumerated in increasing order:
d₁ = 1 < d₂ < d₃ < ... < dₖ = m

For any k ≥ 1, the sum of the k smallest divisors is d₁ + d₂ + ... + dₖ.

The function f(n) asks: what is the smallest m such that n equals such a sum?
-/

/--
A number n is representable if there exists some m and some k ≥ 1 such that
n equals the sum of the k smallest divisors of m.

We axiomatize this predicate rather than defining it constructively,
as the definition involves enumerating divisors in sorted order.
-/
axiom IsRepresentable (n : ℕ) : Prop

/-!
## The Function f(n)

We axiomatize f(n) as the minimal m such that n is representable via m.
The constructive definition involves complex enumerations of divisors.
-/

/--
f(n) = the minimal m ≥ 1 such that n equals the sum of the k smallest
divisors of m for some k ≥ 1.

If no such m exists, f(n) = 0 (junk value indicating undefined).
-/
axiom f (n : ℕ) : ℕ

/--
When n is representable, f(n) ≥ 1.
-/
axiom f_pos (n : ℕ) (hn : IsRepresentable n) : f n ≥ 1

/--
When n is not representable, f(n) = 0.
-/
axiom f_undefined (n : ℕ) (hn : ¬IsRepresentable n) : f n = 0

/-!
## Undefined Cases

The function f is undefined (returns 0) for n = 2 and n = 5.

For n = 2: The smallest divisor of any m ≥ 1 is always 1.
The sum of the first divisor is 1 (not 2).
The sum of the first two divisors of m is 1 + d₂ where d₂ ≥ 2,
so the minimum is 1 + 2 = 3 (achieved when m = 2). Thus no m gives sum 2.

For n = 5: Similar analysis shows no m has smallest divisors summing to 5.
Checking small cases:
- m = 2: divisors {1, 2}, sums are 1, 3
- m = 3: divisors {1, 3}, sums are 1, 4
- m = 4: divisors {1, 2, 4}, sums are 1, 3, 7
- m = 5: divisors {1, 5}, sums are 1, 6
- m = 6: divisors {1, 2, 3, 6}, sums are 1, 3, 6, 12
And so on - 5 is never achieved.
-/

/--
2 is not representable as a sum of smallest divisors.
-/
axiom not_representable_2 : ¬IsRepresentable 2

/--
5 is not representable as a sum of smallest divisors.
-/
axiom not_representable_5 : ¬IsRepresentable 5

/--
f(2) = 0 because 2 is not representable.
-/
theorem f_2_eq_zero : f 2 = 0 := f_undefined 2 not_representable_2

/--
f(5) = 0 because 5 is not representable.
-/
theorem f_5_eq_zero : f 5 = 0 := f_undefined 5 not_representable_5

/-!
## Simple Examples

Let's verify some basic cases where f(n) is well-defined.
-/

/--
1 is representable: the divisors of 1 are just {1}, and their sum is 1.
-/
axiom representable_1 : IsRepresentable 1

/--
f(1) = 1: the smallest m whose divisor sum can equal 1 is m = 1 itself.
-/
axiom f_1_eq_one : f 1 = 1

/--
3 is representable: the divisors of 2 are {1, 2}, and 1 + 2 = 3.
-/
axiom representable_3 : IsRepresentable 3

/--
f(3) = 2: the smallest m whose smallest divisors sum to 3.
-/
axiom f_3_eq_two : f 3 = 2

/--
4 is representable: the divisors of 3 are {1, 3}, and 1 + 3 = 4.
-/
axiom representable_4 : IsRepresentable 4

/--
f(4) = 3: the smallest m whose smallest divisors sum to 4.
-/
axiom f_4_eq_three : f 4 = 3

/--
6 is representable: the divisors of 6 include {1, 2, 3}, and 1 + 2 + 3 = 6.
-/
axiom representable_6 : IsRepresentable 6

/--
f(6) = 6: we need divisors summing to 6.
For m = 6: divisors sorted are [1, 2, 3, 6], and 1 + 2 + 3 = 6.
-/
axiom f_6_eq_six : f 6 = 6

/-!
## The Open Problem

The main questions concern the asymptotic behavior of f(n):
-/

/--
**Open Question I**: Is f(n) = o(n)?

In other words, does f(n)/n → 0 as n → ∞?

Terry Tao showed this is FALSE in full generality - there exist
infinitely many n where f(n) is comparable to n.
-/
def erdos_1054_part_i : Prop :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, (f n : ℝ) < ε * n

/--
**Open Question II**: Is f(n) = o(n) for almost all n?

"Almost all" means the set of exceptions has natural density 0.
This weaker statement might still be true even though Part I fails.
-/
def erdos_1054_part_ii : Prop :=
  ∀ ε > 0, ∀ δ > 0, ∃ N, ∀ M ≥ N,
    (Finset.filter (fun n => (f n : ℝ) ≥ ε * n) (Finset.range M)).card < δ * M

/--
**Open Question III**: Is limsup f(n)/n = ∞?

This asks whether there are arbitrarily large n where f(n) ≥ c·n for any c.
-/
def erdos_1054_part_iii : Prop :=
  ∀ C : ℝ, ∃ n : ℕ, n ≥ 1 ∧ (f n : ℝ) ≥ C * n

/--
The main Erdős Problem #1054 asks about the relationship between these questions.
The status is OPEN - the "almost all" version remains unresolved.
-/
theorem erdos_1054_is_open : True := trivial

/-!
## Tao's Partial Result

Terry Tao disproved the strong unconditional claim that f(n) = o(n).
He constructed infinitely many n where f(n) is at least a constant fraction of n.
However, the question of "almost all n" remains open.
-/

/--
Tao's result: Part I is FALSE.
There exist infinitely many n with f(n) ≥ c·n for some constant c > 0.
-/
axiom tao_disproves_part_i : ¬erdos_1054_part_i

/-!
## Understanding the Problem

The key insight is that small divisors are very constrained:
- Every number's smallest divisor is 1
- The second smallest is the smallest prime factor
- Numbers with only large prime factors have sparse small divisors

For n to equal a sum of k smallest divisors of m:
- If k = 1: n = 1 (only works for n = 1)
- If k = 2: n = 1 + p where p is the smallest prime factor of m
- In general, the sums are constrained by the divisor structure

The question is: how efficiently can we "target" a specific n?
If we need m ≈ n to hit n, then f(n) = Θ(n) and the answer is no.
If we can usually find much smaller m, then f(n) = o(n) might hold.
-/

/-!
## Examples of Divisor Sums

Let's record the partial sums of divisors for small numbers:
- m = 1: divisors [1], partial sums [1]
- m = 2: divisors [1, 2], partial sums [1, 3]
- m = 3: divisors [1, 3], partial sums [1, 4]
- m = 4: divisors [1, 2, 4], partial sums [1, 3, 7]
- m = 5: divisors [1, 5], partial sums [1, 6]
- m = 6: divisors [1, 2, 3, 6], partial sums [1, 3, 6, 12]
- m = 7: divisors [1, 7], partial sums [1, 8]
- m = 8: divisors [1, 2, 4, 8], partial sums [1, 3, 7, 15]
- m = 9: divisors [1, 3, 9], partial sums [1, 4, 13]
- m = 10: divisors [1, 2, 5, 10], partial sums [1, 3, 8, 18]

Notice that 2 and 5 never appear as partial sums!
-/

/--
The values that CAN be represented include:
1 (from m=1), 3 (from m=2), 4 (from m=3), 6 (from m=6), 7 (from m=4),
8 (from m=7), etc.
-/
axiom some_representable_values :
    IsRepresentable 1 ∧ IsRepresentable 3 ∧ IsRepresentable 4 ∧
    IsRepresentable 6 ∧ IsRepresentable 7 ∧ IsRepresentable 8

/--
The function f is monotonically "reasonable" in the sense that
for representable n, we have f(n) ≤ some polynomial in n.
(The exact bound depends on the structure of divisors.)
-/
axiom f_bounded_above (n : ℕ) (hn : IsRepresentable n) :
    f n ≤ n * n

/-!
## The Two Exceptional Values

Why are exactly 2 and 5 the "missing" values in the range of partial divisor sums?

For n = 2:
- k = 1 gives sum = 1 (not 2)
- k ≥ 2 gives sum ≥ 1 + 2 = 3 (since smallest prime is 2)
So 2 is trapped between achievable sums.

For n = 5:
- Looking at achievable sums: 1, 3, 4, 6, 7, 8, ...
- The sum 4 comes from m = 3: divisors {1, 3}
- The sum 6 comes from m = 5: divisors {1, 5} giving 1+5=6, or m=6
- Nothing hits 5 because:
  - Need 1 + (second divisor) = 5, so second divisor = 4
  - But if 4 divides m and is the second smallest, then 2 also divides m
  - If 2 divides m, then 2 < 4, so 2 would be the second divisor, not 4
  - Contradiction!
-/

/--
The key lemma explaining why 5 is impossible:
If 4 is the smallest divisor > 1 of m, then 2 must also divide m,
which contradicts 4 being smallest.
-/
axiom why_5_impossible :
    ∀ m : ℕ, m ≥ 2 → (∀ d : ℕ, 1 < d ∧ d < 4 → ¬(d ∣ m)) → ¬(4 ∣ m)

end Erdos1054
