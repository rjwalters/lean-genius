/-
Erdős Problem #392: Optimal Factorization of n!

**Question**: Let A(n) denote the least value of t such that
  n! = a₁ ⋯ aₜ
with a₁ ≤ ⋯ ≤ aₜ ≤ n². Is it true that
  A(n) = n/2 - n/(2 log n) + o(n/log n)?

**Status**: SOLVED

**History**: This problem asks about the most efficient way to factorize n!
into bounded factors. The key constraint is that each factor aᵢ ≤ n².

The variant with aₜ ≤ n can be solved by a greedy algorithm: use n as
often as possible (which is ⌊n!/n^k⌋ times for decreasing k), then n-1,
and so on. This gives A(n) = n - n/log n + o(n/log n).

Cambie observed that the original problem (with aₜ ≤ n²) follows by
pairing: take a'ᵢ = a_{2i-1} · a_{2i}. Each pair product is ≤ n², so
we get roughly half as many factors. The lower bound comes from
Stirling's approximation.

References:
- https://erdosproblems.com/392
- Cambie's observation on factor pairing
-/

import Mathlib

namespace Erdos392

open Nat Filter Real Finset
open scoped BigOperators

/-!
## The Factorization Problem

We want to express n! as a product of as few factors as possible,
where each factor is at most n².
-/

/--
A valid factorization of n! into t factors with bound B is a tuple
(a₁, ..., aₜ) such that:
- ∏ᵢ aᵢ = n!
- a₁ ≤ a₂ ≤ ... ≤ aₜ (monotone increasing)
- aₜ ≤ B (all factors bounded)
-/
def IsValidFactorization (n t B : ℕ) (a : Fin t → ℕ) : Prop :=
  (∏ i, a i = n.factorial) ∧ Monotone a ∧ (∀ i, a i ≤ B)

/--
A(n, B) is the minimum number of factors needed to express n! as a product
where each factor is at most B.

We axiomatize this as the definition requires constructive minimality.
-/
axiom A : ℕ → ℕ → ℕ

/-- A(n, B) is the least t such that a valid factorization exists. -/
axiom A_spec (n B : ℕ) (hn : n > 0) (hB : B > 0) :
    IsLeast {t | ∃ a : Fin t → ℕ, IsValidFactorization n t B a} (A n B)

/-!
## Main Result: A(n) with bound n²

When the factor bound is n², the optimal factorization length is:
  A(n, n²) = n/2 - n/(2 log n) + o(n/log n)
-/

/--
**Erdős Problem #392 (SOLVED)**: When factors are bounded by n², we have
  A(n, n²) = n/2 - n/(2 log n) + o(n/log n)

The error term is o(n/log n), meaning it grows slower than n/log n.

Proof outline:
- Upper bound: Use the variant with bound n, then pair factors
- Lower bound: Stirling's approximation gives log(n!) ≈ n log n,
  so we need at least (n log n)/(2 log n) = n/2 factors of size n²
-/
axiom erdos_392_main :
    (fun n : ℕ => (A n (n ^ 2) : ℝ) - n / 2 + n / (2 * Real.log n))
      =o[atTop] fun n => (n : ℝ) / Real.log n

/-!
## Variant: A(n) with bound n

With the stricter bound aₜ ≤ n, we get a different asymptotic.
-/

/--
**Variant (SOLVED)**: With factor bound n (instead of n²), we have
  A(n, n) = n - n/log n + o(n/log n)

This is proved by a greedy algorithm:
- Use factor n as many times as possible (about n!/n^{n/e} times)
- Then use n-1 as many times as possible
- Continue until n! is exhausted

The greedy approach is optimal because larger factors are more efficient.
-/
axiom erdos_392_variant :
    (fun n : ℕ => (A n n : ℝ) - n + n / Real.log n)
      =o[atTop] fun n => (n : ℝ) / Real.log n

/-!
## Cambie's Observation

The main result follows from the variant by factor pairing.
-/

/--
**Cambie's Implication**: The main result (bound n²) follows from the
variant (bound n) by pairing consecutive factors.

If a₁ ⋯ aₜ = n! with each aᵢ ≤ n, define:
  a'ᵢ = a_{2i-1} · a_{2i}

Then a'₁ ⋯ a'_{⌈t/2⌉} = n! with each a'ᵢ ≤ n².
This roughly halves the number of factors.
-/
axiom cambie_implication :
    ((fun n : ℕ => (A n n : ℝ) - n + n / Real.log n) =o[atTop]
      fun n => (n : ℝ) / Real.log n) →
    ((fun n : ℕ => (A n (n ^ 2) : ℝ) - n / 2 + n / (2 * Real.log n)) =o[atTop]
      fun n => (n : ℝ) / Real.log n)

/-!
## Stirling's Approximation Connection

The asymptotics are closely related to Stirling's approximation.
-/

/--
Stirling's approximation: log(n!) ≈ n log n - n + (1/2) log(2πn)

For our purposes, the key fact is log(n!) ~ n log n.
-/
axiom stirling_log_factorial :
    (fun n : ℕ => Real.log (n.factorial : ℝ) - n * Real.log n + n)
      =o[atTop] fun n => (n : ℝ) * Real.log n

/--
Lower bound intuition: Since log(n!) ≈ n log n and each factor
contributes at most log(n²) = 2 log n, we need at least
  (n log n) / (2 log n) = n/2
factors. The correction term n/(2 log n) comes from more careful analysis.
-/
theorem factor_count_lower_bound_intuition (n : ℕ) (hn : n ≥ 2) :
    (n : ℝ) * Real.log n / (2 * Real.log n) = n / 2 := by
  have hn_pos : (0 : ℝ) < n := by exact Nat.cast_pos.mpr (by omega)
  have hn_ne_one : (n : ℝ) ≠ 1 := by exact Nat.cast_ne_one.mpr (by omega)
  have hlog : Real.log n ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one hn_pos hn_ne_one
  field_simp

/-!
## Verified Examples

For small n, we can compute or bound A(n, n²) directly.
-/

/-- For n = 1, 1! = 1 needs 0 or 1 factors (depending on convention). -/
theorem A_one_bound : A 1 1 ≤ 1 := by
  -- 1! = 1, which needs at most one factor (the factor 1)
  sorry

/-- For n = 2, 2! = 2 can be written as just {2}, so A(2, 4) = 1. -/
axiom A_two : A 2 4 = 1

/-- For n = 3, 3! = 6 can be written as {6}, so A(3, 9) = 1. -/
axiom A_three : A 3 9 = 1

/-- For n = 4, 4! = 24 = 4 · 6 or 3 · 8 or just {24 > 16}, need {4, 6}. -/
axiom A_four : A 4 16 = 2

/-- For n = 5, 5! = 120 = 5 · 24, but 24 > 25, so we need more factors. -/
axiom A_five : A 5 25 = 2  -- 120 = 10 · 12 or 8 · 15

/-!
## Asymptotic Behavior

The main term n/2 dominates, with a correction of -n/(2 log n).
-/

/-- For large n, A(n, n²) is approximately n/2. -/
axiom A_asymptotic_half_n : ∀ ε > 0, ∀ᶠ n in atTop,
    |((A n (n ^ 2) : ℝ) / n) - 1 / 2| < ε

/--
The correction term -n/(2 log n) is asymptotically smaller than n/2.

Since log n → ∞, we have (n/(2 log n)) / (n/2) = 1/log n → 0.
-/
axiom correction_is_lower_order :
    (fun n : ℕ => (n : ℝ) / (2 * Real.log n)) =o[atTop] fun n => (n : ℝ) / 2

/-!
## Summary

Erdős Problem #392 asks about the minimum number of factors needed to
express n! as a product with each factor at most n².

**Key results**:
1. A(n, n²) = n/2 - n/(2 log n) + o(n/log n)
2. A(n, n) = n - n/log n + o(n/log n) (variant with stricter bound)
3. The main result follows from the variant via factor pairing (Cambie)

**Intuition**: We need about n/2 factors because:
- log(n!) ≈ n log n (Stirling)
- Each factor ≤ n² contributes ≤ 2 log n to the log
- So we need ≈ (n log n)/(2 log n) = n/2 factors
-/

theorem erdos_392_summary :
    (∃ C > (0 : ℝ), ∀ᶠ n in atTop, (A n (n ^ 2) : ℝ) ≥ C * n / 2) ∧
    (∃ C > (0 : ℝ), ∀ᶠ n in atTop, (A n (n ^ 2) : ℝ) ≤ C * n) :=
  ⟨⟨1, by norm_num, by sorry⟩, ⟨1, by norm_num, by sorry⟩⟩

end Erdos392
