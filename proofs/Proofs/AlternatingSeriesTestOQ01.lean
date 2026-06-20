import Mathlib

/-
# The Alternating Series Test with a Two-Sided Error Bound

Mathlib provides the convergence of an alternating series `∑ (-1)^i • f i` for an antitone
`f → 0`, and the one-directional bracketing lemmas (even partial sums underestimate the
limit, odd partial sums overestimate it). It does **not** package the symmetric *remainder
estimate* that makes the alternating series test so useful in practice:

`|S_N - l| ≤ f N`,    where `S_N = ∑_{i<N} (-1)^i f i` and `l = lim S_N`.

This file proves that bound (`abs_partialSum_sub_limit_le`) by combining the two
bracketing lemmas with the one-step recurrence `S_{N+1} = S_N + (-1)^N f N`, splitting on
the parity of `N`. As a capstone it specialises to the **alternating harmonic series**
`∑ (-1)^i/(i+1)`: the series converges and the partial sums approximate the limit with
error at most `1/(N+1)` (`abs_alternatingHarmonic_sub_limit_le`).

All results are over `ℝ`. The limit value (here `log 2`) is not needed for the estimate.
Absent from Mathlib.
-/

namespace AlternatingSeriesTestOQ01

open Finset Filter Topology

variable {f : ℕ → ℝ} {l : ℝ}

/-- The partial sums of an alternating series satisfy the one-step recurrence
`S_{n+1} = S_n + (-1)^n f n`. -/
theorem partialSum_succ (n : ℕ) :
    (∑ i ∈ range (n + 1), (-1) ^ i * f i)
      = (∑ i ∈ range n, (-1) ^ i * f i) + (-1) ^ n * f n := by
  rw [Finset.sum_range_succ]

/-- **Two-sided remainder bound for the alternating series test.** If `f` is antitone and
tends to `0`, and the alternating series `S_N = ∑_{i<N} (-1)^i f i` converges to `l`, then
the `N`-th partial sum approximates `l` with error at most `f N`:
`|S_N - l| ≤ f N`. -/
theorem abs_partialSum_sub_limit_le (hfa : Antitone f) (hf0 : Tendsto f atTop (𝓝 0))
    (hl : Tendsto (fun n => ∑ i ∈ range n, (-1) ^ i * f i) atTop (𝓝 l)) (N : ℕ) :
    |(∑ i ∈ range N, (-1) ^ i * f i) - l| ≤ f N := by
  set S : ℕ → ℝ := fun n => ∑ i ∈ range n, (-1) ^ i * f i with hS
  rcases Nat.even_or_odd N with ⟨k, hk⟩ | ⟨k, hk⟩
  · -- N = 2k : even number of terms, `S N ≤ l ≤ S N + f N`
    have hN : N = 2 * k := by omega
    have h1 : S (2 * k) ≤ l := hfa.alternating_series_le_tendsto hl k
    have h2 : l ≤ S (2 * k + 1) := hfa.tendsto_le_alternating_series hl k
    have h3 : S (2 * k + 1) = S (2 * k) + f (2 * k) := by
      have := partialSum_succ (f := f) (2 * k)
      rw [show (-1 : ℝ) ^ (2 * k) = 1 by rw [pow_mul, neg_one_sq, one_pow], one_mul] at this
      exact this
    rw [hN, abs_of_nonpos (by linarith)]
    linarith
  · -- N = 2k+1 : odd number of terms, `S N - f N ≤ l ≤ S N`
    have hN : N = 2 * k + 1 := by omega
    have h1 : S (2 * (k + 1)) ≤ l := hfa.alternating_series_le_tendsto hl (k + 1)
    have h1' : S (2 * k + 2) ≤ l := by rwa [show 2 * (k + 1) = 2 * k + 2 by ring] at h1
    have h2 : l ≤ S (2 * k + 1) := hfa.tendsto_le_alternating_series hl k
    have h3 : S (2 * k + 2) = S (2 * k + 1) - f (2 * k + 1) := by
      have := partialSum_succ (f := f) (2 * k + 1)
      rw [show (-1 : ℝ) ^ (2 * k + 1) = -1 by
        rw [pow_succ, pow_mul, neg_one_sq, one_pow, one_mul]] at this
      rw [show 2 * k + 1 + 1 = 2 * k + 2 by ring] at this
      linarith [this]
    rw [hN, abs_of_nonneg (by linarith)]
    linarith

/-- The alternating harmonic coefficients `f i = 1/(i+1)` are antitone. -/
theorem antitone_one_div_succ : Antitone (fun i : ℕ => 1 / ((i : ℝ) + 1)) := by
  intro i j hij
  have hi : (0 : ℝ) < (i : ℝ) + 1 := by positivity
  apply one_div_le_one_div_of_le hi
  exact_mod_cast by simpa using hij

/-- **Alternating harmonic series with error bound.** The alternating harmonic series
`∑ (-1)^i/(i+1)` converges to a limit `l` (namely `log 2`), and its `N`-th partial sum
approximates `l` with error at most `1/(N+1)`. -/
theorem abs_alternatingHarmonic_sub_limit_le :
    ∃ l : ℝ, Tendsto (fun n => ∑ i ∈ range n, (-1) ^ i * (1 / ((i : ℝ) + 1))) atTop (𝓝 l) ∧
      ∀ N : ℕ, |(∑ i ∈ range N, (-1) ^ i * (1 / ((i : ℝ) + 1))) - l| ≤ 1 / ((N : ℝ) + 1) := by
  have hfa : Antitone (fun i : ℕ => 1 / ((i : ℝ) + 1)) := antitone_one_div_succ
  have hf0 : Tendsto (fun i : ℕ => 1 / ((i : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  obtain ⟨l, hl⟩ := hfa.tendsto_alternating_series_of_tendsto_zero hf0
  exact ⟨l, hl, fun N => abs_partialSum_sub_limit_le hfa hf0 hl N⟩

end AlternatingSeriesTestOQ01
