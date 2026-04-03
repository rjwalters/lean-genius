/-
  Aristotle targets for Erdős Problem #318 (Signed Unit Fractions with Zero Sum)
  Routine supporting lemmas for automated proof search.
  See Erdos318Problem.lean for the main formalization.

  Criteria for inclusion:
  - sum_reciprocal_squares_less_than_one: ∑_{k≥2} 1/k² < 1 (key bound for squares case)
  - odd_count_lower_bound: count of odds in {0,...,n} is at least n/2
  - counterexample_positive_density: odd numbers ∪ {2m} has positive density ≥ 1/4
  - zero_sum_integer_form: clearing denominators in a rational zero-sum
  - NOT counterexample_fails_P1 (deep parity obstruction, beyond Aristotle)
  - NOT HasPropertyP1 results (main theorems backed by published papers)

  Mathematical context:
  ∑_{k≥2} 1/k² < 1 justifies excluding 1 from the squares set: no finite signed
  sum of 1/k² can equal 1 = |(-1)/1|, so -1/1 cannot be canceled by +1/k² terms.
  The bound follows from 1/k² < 1/(k*(k-1)) = 1/(k-1) - 1/k, whose sum telescopes to 1.
  Density of the counterexample follows from odd numbers having density 1/2.
-/
import Mathlib

namespace Erdos318Aristotle

open Finset BigOperators

/- ## Definitions (mirrored from Erdos318Problem.lean) -/

/-- Signed sum of unit fractions. -/
def signedUnitSum (S : Finset ℕ) (f : ℕ → ℤ) : ℚ :=
  ∑ n ∈ S, (f n : ℚ) / (n : ℚ)

/-- A set A ⊆ ℕ has positive density if lim inf |A ∩ [0,n]| / n > 0. -/
def hasPositiveDensity (A : Set ℕ) : Prop :=
  ∃ δ : ℝ, δ > 0 ∧ ∃ N : ℕ, ∀ n ≥ N,
    (Finset.filter (· ∈ A) (Finset.range (n + 1))).card ≥ δ * n

/-- Counterexample: odd numbers plus one even number. -/
def counterexampleSet (m : ℕ) : Set ℕ :=
  {n : ℕ | n % 2 = 1 ∨ n = 2 * m}

/- ## Supporting Lemmas -/

/-- The count of odd numbers in {0, 1, ..., n} is at least n / 2.
    Used to establish that the counterexample set has positive density ≥ 1/4. -/
lemma odd_count_lower_bound (n : ℕ) :
    (Finset.filter (fun k => k % 2 = 1) (Finset.range (n + 1))).card * 2 ≥ n := by
  sorry

/-- Pointwise bound: 1/k² ≤ 1/(k*(k-1)) for k ≥ 2.
    Since k*(k-1) ≤ k² for k ≥ 1, taking reciprocals reverses the inequality. -/
lemma one_div_sq_le_one_div_mul_pred (k : ℕ) (hk : k ≥ 2) :
    (1 : ℝ) / (k : ℝ)^2 ≤ 1 / ((k : ℝ) * ((k : ℝ) - 1)) := by
  sorry

/-- ∑_{k≥2} 1/k² < 1.
    Proof sketch: 1/k² < 1/(k*(k-1)) = 1/(k-1) - 1/k (telescoping), so
    ∑_{k≥2} 1/k² < ∑_{k≥2} (1/(k-1) - 1/k) = 1. -/
theorem sum_reciprocal_squares_less_than_one :
    ∑' (k : ℕ), (if k ≥ 2 then (1 : ℝ) / k^2 else 0) < 1 := by
  sorry

/-- The counterexample set (odd numbers ∪ {2m}) has positive density.
    Since at least half of naturals are odd, density ≥ 1/4 for large n. -/
theorem counterexample_positive_density (m : ℕ) (hm : m ≥ 1) :
    hasPositiveDensity (counterexampleSet m) := by
  sorry

/-- Clearing denominators: if ∑_{n ∈ S} f(n)/n = 0 as rationals, then
    ∑_{n ∈ S} f(n) * (∏_{m ∈ S} m) / n = 0 as integers.
    Key: each n ∈ S divides ∏_{m ∈ S} m, making integer division exact. -/
theorem zero_sum_integer_form (S : Finset ℕ) (f : ℕ → ℤ) (hS : S.Nonempty)
    (h0 : ∀ n ∈ S, n ≠ 0) (hzero : signedUnitSum S f = 0) :
    ∑ n ∈ S, f n * (∏ m ∈ S, m) / n = 0 := by
  sorry

end Erdos318Aristotle
