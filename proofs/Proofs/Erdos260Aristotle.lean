/-
  Aristotle targets for Erdos Problem #260
  Routine supporting lemmas for automated proof search.
  See Erdos260Problem.lean for the main formalization.

  Criteria for inclusion:
  - NOT the hard irrationality results (those are deep number theory)
  - Routine analysis facts: n/2^n summability, exponential domination, limit comparisons
  - Helper lemmas for series_converges, fastGrowth_of_gapsToInfinity, fastGrowth_of_superlogarithmic
  - No axioms, no definition sorries, no open conjectures
  - Use only block comments, not module docstrings
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
    n ≤ f n := hf.id_le n

-- Aristotle target: n / 2^n is summable over naturals
theorem summable_nat_div_two_pow :
    Summable (fun n : ℕ => (n : ℝ) / (2 : ℝ) ^ n) := by
  -- n/2^n = n^1 * (1/2)^n; apply summable_pow_mul_geometric
  have hsumm : Summable (fun n : ℕ => (n : ℝ) ^ 1 * ((1 : ℝ) / 2) ^ n) :=
    summable_pow_mul_geometric_of_norm_lt_one 1 (by norm_num)
  exact hsumm.congr (fun n => by rw [pow_one, one_div, inv_pow, div_eq_mul_inv])

-- Aristotle target: 0 < 2^n for all natural n (in reals)
theorem two_pow_pos (n : ℕ) : (0 : ℝ) < (2 : ℝ) ^ n := by positivity

-- Aristotle target: n / 2^n >= 0 for natural n
theorem nat_div_two_pow_nonneg (n : ℕ) :
    (0 : ℝ) ≤ (n : ℝ) / (2 : ℝ) ^ n := by positivity

-- Aristotle target: if a >= n then 2^n <= 2^a
theorem two_pow_mono {a n : ℕ} (h : n ≤ a) :
    (2 : ℝ) ^ n ≤ (2 : ℝ) ^ a := by
  exact pow_le_pow_right (by norm_num : (1 : ℝ) ≤ 2) h

-- Aristotle target: n/2^n -> 0 as n -> infinity
theorem nat_div_two_pow_tendsto_zero :
    Tendsto (fun n : ℕ => (n : ℝ) / (2 : ℝ) ^ n) atTop (nhds 0) :=
  summable_nat_div_two_pow.tendsto_atTop_zero

/-
  ## Section 2: Helpers for fastGrowth_of_gapsToInfinity

  If gaps a(n+1) - a(n) -> infinity, then a(n)/n -> infinity.
-/

-- Aristotle target: telescoping sum - a(n) = a(0) + sum of gaps
theorem strictMono_telescope (f : ℕ → ℕ) (hf : StrictMono f) (n : ℕ) :
    f n = f 0 + ∑ i in Finset.range n, (f (i + 1) - f i) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ← Nat.add_sub_cancel (f (n + 1)),
        show f (n + 1) - f (n + 1) + f (n + 1) = f (n + 1) from by omega]
    have : f n < f (n + 1) := hf (by omega)
    omega

-- Aristotle target: if all terms in a sum are >= M then sum >= M * n
theorem finset_sum_ge_of_ge {M : ℝ} {f : ℕ → ℝ} {n : ℕ}
    (hf : ∀ i ∈ Finset.range n, f i ≥ M) :
    ∑ i in Finset.range n, f i ≥ M * n := by
  calc ∑ i in Finset.range n, f i ≥ ∑ _ in Finset.range n, M :=
        Finset.sum_le_sum hf
    _ = M * n := by simp [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

-- Aristotle target: constant / n -> 0
theorem const_div_n_tendsto_zero (c : ℝ) :
    Tendsto (fun n : ℕ => c / (n : ℝ)) atTop (nhds 0) := by
  apply tendsto_const_div_atTop_nhds_0_nat

/-
  ## Section 3: Helpers for fastGrowth_of_superlogarithmic
-/

-- Aristotle target: log n -> infinity
theorem real_log_tendsto_atTop :
    Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
  Real.tendsto_log_nat_atTop

-- Aristotle target: if f -> infty and g -> infty then f * g -> infty (for eventually positive)
theorem tendsto_mul_atTop_of_pos {f g : ℕ → ℝ}
    (hf : Tendsto f atTop atTop) (hg : ∀ᶠ n in atTop, g n > 0)
    (hg' : Tendsto g atTop atTop) :
    Tendsto (fun n => f n * g n) atTop atTop :=
  Filter.Tendsto.atTop_mul_atTop hf hg'

-- Aristotle target: sqrt is monotone on nonneg reals
theorem sqrt_mono {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    Real.sqrt a ≤ Real.sqrt b :=
  Real.sqrt_le_sqrt hab

-- Aristotle target: sqrt(x) -> infty as x -> infty
theorem sqrt_tendsto_atTop :
    Tendsto (fun x : ℝ => Real.sqrt x) atTop atTop :=
  Real.tendsto_sqrt_atTop

end Erdos260.Aristotle
