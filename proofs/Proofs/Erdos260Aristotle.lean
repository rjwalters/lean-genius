/-
  Aristotle targets for Erdos Problem #260
  Routine supporting lemmas for automated proof search.
  See Erdos260Problem.lean for the main formalization.

  Criteria for inclusion:
  - NOT the hard irrationality results (those are deep number theory)
  - Routine analysis facts: n/2^n summability, exponential domination, limit comparisons
  - Helper lemmas for series_converges, fastGrowth_of_gapsToInfinity, fastGrowth_of_superlogarithmic
  - No axioms, no definition sorries, no open conjectures
  - No /-! docstring sections
-/
import Mathlib

namespace Erdos260.Aristotle

open Filter Topology Real

/-
  ## Section 1: Series Convergence Helpers

  series_converges needs: the series sum_n a_n / 2^{a_n} converges.
  Key idea: since a is strictly monotone, a(n) >= n, so a_n / 2^{a_n} <= n / 2^n.
  The dominating series sum n/2^n converges.
-/

-- Aristotle target: strictly monotone nat sequence satisfies a(n) >= n
theorem strictMono_nat_ge (f : ℕ → ℕ) (hf : StrictMono f) (n : ℕ) :
    n ≤ f n := by sorry

-- Aristotle target: n / 2^n is summable over naturals
theorem summable_nat_div_two_pow :
    Summable (fun n : ℕ => (n : ℝ) / (2 : ℝ) ^ n) := by sorry

-- Aristotle target: 0 < 2^n for all natural n (in reals)
theorem two_pow_pos (n : ℕ) : (0 : ℝ) < (2 : ℝ) ^ n := by sorry

-- Aristotle target: n / 2^n >= 0 for natural n
theorem nat_div_two_pow_nonneg (n : ℕ) :
    (0 : ℝ) ≤ (n : ℝ) / (2 : ℝ) ^ n := by sorry

-- Aristotle target: if a >= n then a / 2^a <= a / 2^n (monotone denominator)
-- Actually: if a >= n then 2^n <= 2^a
theorem two_pow_mono {a n : ℕ} (h : n ≤ a) :
    (2 : ℝ) ^ n ≤ (2 : ℝ) ^ a := by sorry

-- Aristotle target: a / 2^a <= a / 2^a is trivial but we need
-- the domination a/2^a <= n/2^n when a >= n doesn't directly give this.
-- Instead: a/2^a -> 0 as a -> infinity
theorem nat_div_two_pow_tendsto_zero :
    Tendsto (fun n : ℕ => (n : ℝ) / (2 : ℝ) ^ n) atTop (nhds 0) := by sorry

/-
  ## Section 2: Helpers for fastGrowth_of_gapsToInfinity

  If gaps a(n+1) - a(n) -> infinity, then a(n)/n -> infinity.
  Key idea: if gaps eventually exceed M, then a(n) >= M*n eventually,
  so a(n)/n >= M. Since M is arbitrary, a(n)/n -> infinity.
-/

-- Aristotle target: telescoping sum - a(n) = a(0) + sum of gaps
theorem strictMono_telescope (f : ℕ → ℕ) (hf : StrictMono f) (n : ℕ) :
    f n = f 0 + ∑ i in Finset.range n, (f (i + 1) - f i) := by sorry

-- Aristotle target: if all terms in a sum are >= M then sum >= M * n
theorem finset_sum_ge_of_ge {M : ℝ} {f : ℕ → ℝ} {n : ℕ}
    (hf : ∀ i ∈ Finset.range n, f i ≥ M) :
    ∑ i in Finset.range n, f i ≥ M * n := by sorry

-- Aristotle target: if a(n)/n >= M for all large n and all M, then a(n)/n -> infty
-- More precisely: constant / n -> 0
theorem const_div_n_tendsto_zero (c : ℝ) :
    Tendsto (fun n : ℕ => c / (n : ℝ)) atTop (nhds 0) := by sorry

/-
  ## Section 3: Helpers for fastGrowth_of_superlogarithmic

  If a(n) >= C * n * sqrt(log n * log(log n)), then a(n)/n -> infty.
  Key idea: a(n)/n >= C * sqrt(log n * log(log n)) -> infty.
-/

-- Aristotle target: log n -> infinity
theorem real_log_tendsto_atTop :
    Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop := by sorry

-- Aristotle target: if f -> infty and g -> infty then f * g -> infty (for eventually positive)
theorem tendsto_mul_atTop_of_pos {f g : ℕ → ℝ}
    (hf : Tendsto f atTop atTop) (hg : ∀ᶠ n in atTop, g n > 0)
    (hg' : Tendsto g atTop atTop) :
    Tendsto (fun n => f n * g n) atTop atTop := by sorry

-- Aristotle target: sqrt is monotone on nonneg reals
theorem sqrt_mono {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    Real.sqrt a ≤ Real.sqrt b := by sorry

-- Aristotle target: sqrt(x) -> infty as x -> infty
theorem sqrt_tendsto_atTop :
    Tendsto (fun x : ℝ => Real.sqrt x) atTop atTop := by sorry

end Erdos260.Aristotle
