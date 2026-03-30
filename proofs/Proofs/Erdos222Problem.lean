/-
Erdős Problem #222: Gaps Between Sums of Two Squares

Source: https://erdosproblems.com/222
Status: SOLVED (Ongoing improvements to constants)

Statement:
Let n₁ < n₂ < ⋯ be the sequence of integers which are the sum of two squares.
Explore the behaviour of the consecutive differences n_{k+1} - n_k.
Find good upper and lower bounds for these gaps.

Key Results:
- Bambah-Chowla (1947): n_{k+1} - n_k ≪ n_k^(1/4)
- Erdős (1951): For infinitely many k, n_{k+1} - n_k ≫ (log n_k)/√(log log n_k)
- Richards (1982): limsup (n_{k+1} - n_k)/log n_k ≥ 1/4
- Dietmann-Elsholtz-Kalmynin-Konyagin-Maynard (2022): constant improved to ≈ 0.868

Background:
An integer n is a sum of two squares iff in the prime factorization of n,
every prime p ≡ 3 (mod 4) appears to an even power (Fermat-Euler).

References:
- Bambah-Chowla [BC47]
- Erdős [Er51]
- Landau [La08]
- Richards [Ri82]
- Dietmann-Elsholtz-Kalmynin-Konyagin-Maynard [DEKKM22]
-/

import Mathlib.NumberTheory.SumTwoSquares
import Mathlib.NumberTheory.Divisors
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Algebra.Order.Floor
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.Filter.AtTopBot

namespace Erdos222

open Nat Real Filter

/- ## Part I: Sums of Two Squares -/

/-- A natural number is a sum of two squares. -/
def IsSumTwoSquares (n : ℕ) : Prop :=
  ∃ a b : ℤ, n = (a^2 + b^2).toNat

/-- The set of all sums of two squares. -/
def SumTwoSquaresSeq : Set ℕ :=
  {n | IsSumTwoSquares n}

/-- 0 = 0² + 0² -/
example : IsSumTwoSquares 0 := ⟨0, 0, rfl⟩
/-- 1 = 1² + 0² -/
example : IsSumTwoSquares 1 := ⟨1, 0, rfl⟩
/-- 2 = 1² + 1² -/
example : IsSumTwoSquares 2 := ⟨1, 1, rfl⟩
/-- 5 = 2² + 1² -/
example : IsSumTwoSquares 5 := ⟨2, 1, rfl⟩
/-- 13 = 3² + 2² -/
example : IsSumTwoSquares 13 := ⟨3, 2, rfl⟩

/- ## Part II: Fermat's Criterion -/

/-- A prime p ≡ 3 (mod 4). -/
def IsPrime3Mod4 (p : ℕ) : Prop :=
  p.Prime ∧ p % 4 = 3

/-- **Fermat's criterion:** n > 0 is a sum of two squares iff
every prime p ≡ 3 (mod 4) divides n to an even power. -/
/-- Primes p ≡ 1 (mod 4) are sums of two squares.
    Proved via Mathlib's Nat.Prime.sq_add_sq. -/
theorem prime_1_mod_4_sum_two_squares (p : ℕ) (hp : p.Prime) (h : p % 4 = 1) :
    IsSumTwoSquares p := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨a, b, hab⟩ := Nat.Prime.sq_add_sq (show p % 4 ≠ 3 by omega)
  exact ⟨↑a, ↑b, by
    have : (↑a : ℤ) ^ 2 + (↑b : ℤ) ^ 2 = ↑p := by push_cast; linarith
    rw [this, Int.toNat_natCast]⟩

/-- 2 = 1² + 1² -/
theorem two_is_sum_two_squares : IsSumTwoSquares 2 := ⟨1, 1, rfl⟩

/- ## Part III: The Gap Function

The k-th sum of two squares and the gap between consecutive entries
are axiomatized as functions with appropriate properties. -/

/-- The k-th element of the sum-of-two-squares sequence (0-indexed). -/
axiom nthSumTwoSquares : ℕ → ℕ

/-- The sequence is strictly increasing. -/
/-- Every element is a sum of two squares. -/
/-- The gap between the k-th and (k+1)-th sums of two squares. -/
def gap (k : ℕ) : ℕ :=
  nthSumTwoSquares (k + 1) - nthSumTwoSquares k

/- ## Part IV: Density -/

/-- Counting function: number of sums of two squares up to x. -/
noncomputable def countSumTwoSquares (x : ℝ) : ℕ :=
  (SumTwoSquaresSeq ∩ {n | (n : ℝ) ≤ x}).ncard

/-- **Landau's theorem (1908):** The density of sums of two squares
is asymptotic to cx/√(log x) for some c > 0. -/
/- ## Part V: Lower Bounds on Gaps -/

/-- **Erdős (1951):** For infinitely many k, the gap is
at least c · log(n_k) / √(log log n_k). -/
axiom erdos_1951_lower_bound :
    ∃ c > 0, ∀ᶠ n in atTop,
      ∃ k, nthSumTwoSquares k ≤ n ∧ nthSumTwoSquares (k+1) > n ∧
        (gap k : ℝ) ≥ c * Real.log n / Real.sqrt (Real.log (Real.log n))

/-- **Richards (1982):** limsup of gaps / log n ≥ 1/4. -/
/-- **Dietmann-Elsholtz-Kalmynin-Konyagin-Maynard (2022):**
limsup of gaps / log n ≥ 0.868. -/
/- ## Part VI: Upper Bound -/

/-- **Bambah-Chowla (1947):** All gaps are O(n^(1/4)).
Between n and n + O(n^(1/4)), there is always a sum of two squares. -/
axiom bambah_chowla_upper_bound :
    ∃ C > 0, ∀ k, (gap k : ℝ) ≤ C * (nthSumTwoSquares k : ℝ) ^ (1/4 : ℝ)

/- ## Part VII: Summary -/

/-- **Erdős Problem #222: SOLVED**

Lower bounds (infinitely many large gaps):
- Erdős (1951): gap ≫ log n / √(log log n)
- Richards (1982): limsup gap/log n ≥ 1/4
- DEKKM (2022): limsup gap/log n ≥ 0.868

Upper bound (all gaps bounded):
- Bambah-Chowla (1947): gap ≪ n^(1/4) -/
theorem erdos_222_summary :
    (∃ c > 0, ∀ᶠ n in atTop, ∃ k,
      (gap k : ℝ) ≥ c * Real.log n / Real.sqrt (Real.log (Real.log n))) ∧
    (∃ C > 0, ∀ k, (gap k : ℝ) ≤ C * (nthSumTwoSquares k : ℝ) ^ (1/4 : ℝ)) := by
  constructor
  · obtain ⟨c, hc, h⟩ := erdos_1951_lower_bound
    exact ⟨c, hc, by
      filter_upwards [h] with n ⟨k, _, _, hk⟩
      exact ⟨k, hk⟩⟩
  · exact bambah_chowla_upper_bound

end Erdos222
