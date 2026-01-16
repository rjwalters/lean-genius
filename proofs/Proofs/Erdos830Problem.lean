/-
Erdős Problem #830: Amicable Pairs

Two natural numbers a and b are **amicable** if σ(a) = σ(b) = a + b, where σ(n)
is the sum of divisors of n. The classic example is (220, 284).

**Questions** (OPEN):
1. Are there infinitely many amicable pairs?
2. Is A(x) > x^{1-o(1)}, where A(x) counts amicable pairs up to x?

**Known Upper Bounds** (SOLVED):
- Erdős (1955): A(x) = o(x)
- Pomerance (1981): A(x) ≤ x·exp(-(log x)^{1/3})
- Pomerance (2015): A(x) ≤ x·exp(-(1/2+o(1))√(log x · log log x))

Reference: https://erdosproblems.com/830
-/

import Mathlib

namespace Erdos830

open Filter Real
open scoped Classical

/-!
## Sum of Divisors Function

The sum of divisors function σ(n) sums all positive divisors of n.
In Mathlib, this is `ArithmeticFunction.sigma 1 n`.
For amicable numbers, we need σ(a) = a + b and σ(b) = a + b.
-/

/-- The sum of divisors of n: σ(n) = Σ_{d|n} d -/
abbrev sumDivisors (n : ℕ) : ℕ := ArithmeticFunction.sigma 1 n

/-- Two natural numbers are **amicable** if the sum of divisors of each
equals their sum. Equivalently, σ(a) - a = b and σ(b) - b = a. -/
structure IsAmicable (a b : ℕ) : Prop where
  /-- σ(a) = a + b -/
  sum_div_a : sumDivisors a = a + b
  /-- σ(b) = a + b -/
  sum_div_b : sumDivisors b = a + b

/-!
## Classic Example: 220 and 284

The pair (220, 284) is the smallest amicable pair, known since antiquity.
- Divisors of 220: 1, 2, 4, 5, 10, 11, 20, 22, 44, 55, 110, 220 → sum = 504 = 220 + 284
- Divisors of 284: 1, 2, 4, 71, 142, 284 → sum = 504 = 220 + 284
-/

/-- The divisors of 220 sum to 504. -/
theorem sigma_220 : sumDivisors 220 = 504 := by native_decide

/-- The divisors of 284 sum to 504. -/
theorem sigma_284 : sumDivisors 284 = 504 := by native_decide

/-- 220 and 284 form an amicable pair. -/
theorem amicable_220_284 : IsAmicable 220 284 := ⟨sigma_220, sigma_284⟩

/-!
## The Counting Function A(x)

A(x) counts the number of amicable pairs (a, b) with 1 ≤ a ≤ b ≤ x.
The central question is the growth rate of A(x).
-/

/-- A(x) counts amicable pairs (a, b) with 1 ≤ a ≤ b ≤ x. -/
noncomputable def A (x : ℝ) : ℝ :=
  Finset.card <| (Finset.Icc 1 ⌊x⌋₊ ×ˢ Finset.Icc 1 ⌊x⌋₊).filter fun (a, b) ↦
    a ≤ b ∧ IsAmicable a b

/-!
## Open Questions

The main questions of Problem #830 remain open:
1. Are there infinitely many amicable pairs?
2. Does A(x) grow faster than x^{1-ε} for all ε > 0?
-/

/-- **Erdős Problem #830, Part 1** (OPEN)

Are there infinitely many amicable pairs?

This ancient question remains unsolved. While many amicable pairs
have been found computationally, no proof of infinitude exists. -/
axiom erdos830_infinitely_many :
    {p : ℕ × ℕ | IsAmicable p.1 p.2}.Infinite

/-- **Erdős Problem #830, Part 2** (OPEN)

Is A(x) > x^{1-o(1)}? That is, does the count of amicable pairs up to x
grow nearly as fast as x itself?

This would follow from proving infinitely many amicable pairs with
a positive density, but current bounds are far from this. -/
axiom erdos830_lower_bound :
    ∃ o : ℝ → ℝ, o =o[atTop] (1 : ℝ → ℝ) ∧
    ∀ᶠ x in atTop, x ^ (1 - o x) < A x

/-!
## Proven Upper Bounds

While the lower bound questions are open, significant progress has
been made on upper bounds for A(x).
-/

/-- **Erdős Upper Bound** (1955)

A(x) = o(x): the count of amicable pairs grows slower than linearly.
This was the first non-trivial upper bound. -/
axiom erdos_1955_upper_bound : A =o[atTop] id

/-- **Pomerance Upper Bound** (1981)

A(x) ≤ x · exp(-(log x)^{1/3}) for large x.
A significant improvement over the Erdős bound. -/
axiom pomerance_1981_upper_bound :
    ∀ᶠ x in atTop, A x ≤ x * rexp (- (x.log) ^ (1/3 : ℝ))

/-- **Pomerance Improved Upper Bound** (2015)

A(x) ≤ x · exp(-(1/2 + o(1))√(log x · log log x)) for large x.
The current best known upper bound. -/
axiom pomerance_2015_upper_bound :
    ∃ o : ℝ → ℝ, o =o[atTop] (1 : ℝ → ℝ) ∧
    ∀ᶠ x in atTop, A x ≤ x * rexp (- (1/2 + o x) * √(x.log * x.log.log))

/-!
## Additional Amicable Pairs

Beyond (220, 284), other small amicable pairs include:
- (1184, 1210) - discovered by Nicolo Paganini at age 16 in 1866
- (2620, 2924)
- (5020, 5564)
- (6232, 6368)
-/

/-- σ(1184) = 2394 -/
theorem sigma_1184 : sumDivisors 1184 = 2394 := by native_decide

/-- σ(1210) = 2394 -/
theorem sigma_1210 : sumDivisors 1210 = 2394 := by native_decide

/-- 1184 and 1210 form an amicable pair (discovered 1866). -/
theorem amicable_1184_1210 : IsAmicable 1184 1210 := ⟨sigma_1184, sigma_1210⟩

/-- σ(2620) = 5544 -/
theorem sigma_2620 : sumDivisors 2620 = 5544 := by native_decide

/-- σ(2924) = 5544 -/
theorem sigma_2924 : sumDivisors 2924 = 5544 := by native_decide

/-- 2620 and 2924 form an amicable pair. -/
theorem amicable_2620_2924 : IsAmicable 2620 2924 := ⟨sigma_2620, sigma_2924⟩

end Erdos830
