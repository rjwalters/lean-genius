import Mathlib

/-
# Two-Sided, Two-Term Error Trapping for the Alternating Series Test

The classical alternating series test (Leibniz) bounds the truncation error of an
alternating series `S_N = ∑_{i<N} (-1)^i f i` with antitone `f → 0` by the first omitted
term: `|S_N - l| ≤ f N`, where `l = lim S_N`. This one-term bound is the parent result
(`AlternatingSeriesTestOQ01`).

This file proves the matching **lower** bound, giving a *two-sided* trap of the error by
*two* consecutive terms:

`f N - f (N+1) ≤ |S_N - l| ≤ f N`.

The lower bound is the new content: it shows the Leibniz estimate is essentially sharp —
the error is never smaller than the gap between the first two omitted terms. The mechanism
is the *nesting* of partial sums: the limit `l` lies between **every** pair of consecutive
partial sums, so in particular between `S_{N+1}` and `S_{N+2}`. Since `S_{N+2}` differs
from `S_N` by exactly `±(f N - f (N+1))`, the limit is pushed at least that far from `S_N`.

As a capstone we specialise to the **alternating harmonic series** `∑ (-1)^i/(i+1)`,
obtaining the two-sided quantitative rate

`1/((N+1)(N+2)) ≤ |S_N - l| ≤ 1/(N+1)`.

All results are over `ℝ`; the limit value (`log 2`) is irrelevant to either estimate.
The lower bound is absent from Mathlib.
-/

namespace AlternatingSeriesTestOQ01OQ01

open Finset Filter Topology

variable {f : ℕ → ℝ} {l : ℝ}

/-- One-step recurrence for alternating partial sums: `S_{n+1} = S_n + (-1)^n f n`. -/
theorem partialSum_succ (n : ℕ) :
    (∑ i ∈ range (n + 1), (-1) ^ i * f i)
      = (∑ i ∈ range n, (-1) ^ i * f i) + (-1) ^ n * f n := by
  rw [Finset.sum_range_succ]

/-- Two-step recurrence for alternating partial sums:
`S_{n+2} = S_n + (-1)^n (f n - f (n+1))`. Iterating `partialSum_succ` twice and using
`(-1)^{n+1} = -(-1)^n`, the two newly added signed terms collapse to `(-1)^n (f n - f (n+1))`. -/
theorem partialSum_add_two (n : ℕ) :
    (∑ i ∈ range (n + 2), (-1) ^ i * f i)
      = (∑ i ∈ range n, (-1) ^ i * f i) + (-1) ^ n * (f n - f (n + 1)) := by
  rw [partialSum_succ, partialSum_succ, pow_succ]
  ring

/-- The even/odd bracket gap, two steps out. For even `N = 2k`,
`S_{N+2} = S_N + (f N - f (N+1))`. -/
theorem partialSum_even_add_two (k : ℕ) :
    (∑ i ∈ range (2 * k + 2), (-1) ^ i * f i)
      = (∑ i ∈ range (2 * k), (-1) ^ i * f i) + (f (2 * k) - f (2 * k + 1)) := by
  have h := partialSum_add_two (f := f) (2 * k)
  rwa [show (-1 : ℝ) ^ (2 * k) = 1 by rw [pow_mul, neg_one_sq, one_pow], one_mul] at h

/-- For odd `N = 2k+1`, `S_{N+2} = S_N - (f N - f (N+1))`. -/
theorem partialSum_odd_add_two (k : ℕ) :
    (∑ i ∈ range (2 * k + 3), (-1) ^ i * f i)
      = (∑ i ∈ range (2 * k + 1), (-1) ^ i * f i)
        - (f (2 * k + 1) - f (2 * k + 2)) := by
  have h := partialSum_add_two (f := f) (2 * k + 1)
  rw [show (-1 : ℝ) ^ (2 * k + 1) = -1 by
    rw [pow_succ, pow_mul, neg_one_sq, one_pow, one_mul]] at h
  rw [show 2 * k + 1 + 2 = 2 * k + 3 by ring] at h
  linarith [h]

/-- **Two-sided, two-term error trap for the alternating series test.** If `f` is antitone
and tends to `0`, and the alternating series `S_N = ∑_{i<N} (-1)^i f i` converges to `l`,
then the truncation error after `N` terms is trapped between two consecutive terms:

`f N - f (N+1) ≤ |S_N - l| ≤ f N`.

The upper bound is the classical Leibniz estimate; the lower bound — the sharpness
statement — follows because the limit lies between `S_{N+1}` and `S_{N+2}`, and the latter
sits a full `f N - f (N+1)` past `S_N`. -/
theorem abs_partialSum_sub_limit_trapped (hfa : Antitone f) (hf0 : Tendsto f atTop (𝓝 0))
    (hl : Tendsto (fun n => ∑ i ∈ range n, (-1) ^ i * f i) atTop (𝓝 l)) (N : ℕ) :
    f N - f (N + 1) ≤ |(∑ i ∈ range N, (-1) ^ i * f i) - l|
      ∧ |(∑ i ∈ range N, (-1) ^ i * f i) - l| ≤ f N := by
  set S : ℕ → ℝ := fun n => ∑ i ∈ range n, (-1) ^ i * f i with hS
  rcases Nat.even_or_odd N with ⟨k, hk⟩ | ⟨k, hk⟩
  · -- N = 2k : S N ≤ S_{N+2} ≤ l ≤ S_{N+1} = S N + f N
    have hN : N = 2 * k := by omega
    have h1 : S (2 * k) ≤ l := hfa.alternating_series_le_tendsto hl k
    have h2 : l ≤ S (2 * k + 1) := hfa.tendsto_le_alternating_series hl k
    -- one-step: S_{N+1} = S_N + f N
    have hstep : S (2 * k + 1) = S (2 * k) + f (2 * k) := by
      have := partialSum_succ (f := f) (2 * k)
      rw [show (-1 : ℝ) ^ (2 * k) = 1 by rw [pow_mul, neg_one_sq, one_pow], one_mul] at this
      exact this
    -- two-step: S_{N+2} ≤ l, and S_{N+2} = S_N + (f N - f (N+1))
    have h3 : S (2 * (k + 1)) ≤ l := hfa.alternating_series_le_tendsto hl (k + 1)
    have h3' : S (2 * k + 2) ≤ l := by rwa [show 2 * (k + 1) = 2 * k + 2 by ring] at h3
    have htwo : S (2 * k + 2) = S (2 * k) + (f (2 * k) - f (2 * k + 1)) :=
      partialSum_even_add_two (f := f) k
    rw [hN, abs_of_nonpos (by linarith)]
    constructor
    · linarith
    · linarith
  · -- N = 2k+1 : S_{N+1} = S N - f N ≤ S_{N+2} ... l ≤ S_N, with l between S_{N+1},S_{N+2}
    have hN : N = 2 * k + 1 := by omega
    have h2 : l ≤ S (2 * k + 1) := hfa.tendsto_le_alternating_series hl k
    -- one-step: S_{N+1} = S_N - f N, and S_{N+1} ≤ l
    have h1 : S (2 * (k + 1)) ≤ l := hfa.alternating_series_le_tendsto hl (k + 1)
    have h1' : S (2 * k + 2) ≤ l := by rwa [show 2 * (k + 1) = 2 * k + 2 by ring] at h1
    have hstep : S (2 * k + 2) = S (2 * k + 1) - f (2 * k + 1) := by
      have := partialSum_succ (f := f) (2 * k + 1)
      rw [show (-1 : ℝ) ^ (2 * k + 1) = -1 by
        rw [pow_succ, pow_mul, neg_one_sq, one_pow, one_mul]] at this
      rw [show 2 * k + 1 + 1 = 2 * k + 2 by ring] at this
      linarith [this]
    -- two-step: l ≤ S_{N+2}'s successor odd bracket: l ≤ S_{2k+3} = S_N - (f N - f (N+1))
    have h3 : l ≤ S (2 * (k + 1) + 1) := hfa.tendsto_le_alternating_series hl (k + 1)
    have h3' : l ≤ S (2 * k + 3) := by rwa [show 2 * (k + 1) + 1 = 2 * k + 3 by ring] at h3
    have htwo : S (2 * k + 3) = S (2 * k + 1) - (f (2 * k + 1) - f (2 * k + 2)) :=
      partialSum_odd_add_two (f := f) k
    rw [hN, abs_of_nonneg (by linarith)]
    constructor
    · linarith
    · linarith

/-- The upper (Leibniz) half of the trap, extracted for convenience: `|S_N - l| ≤ f N`. -/
theorem abs_partialSum_sub_limit_le (hfa : Antitone f) (hf0 : Tendsto f atTop (𝓝 0))
    (hl : Tendsto (fun n => ∑ i ∈ range n, (-1) ^ i * f i) atTop (𝓝 l)) (N : ℕ) :
    |(∑ i ∈ range N, (-1) ^ i * f i) - l| ≤ f N :=
  (abs_partialSum_sub_limit_trapped hfa hf0 hl N).2

/-- The lower (sharpness) half of the trap, extracted: `f N - f (N+1) ≤ |S_N - l|`. -/
theorem sub_le_abs_partialSum_sub_limit (hfa : Antitone f) (hf0 : Tendsto f atTop (𝓝 0))
    (hl : Tendsto (fun n => ∑ i ∈ range n, (-1) ^ i * f i) atTop (𝓝 l)) (N : ℕ) :
    f N - f (N + 1) ≤ |(∑ i ∈ range N, (-1) ^ i * f i) - l| :=
  (abs_partialSum_sub_limit_trapped hfa hf0 hl N).1

/-- The alternating harmonic coefficients `f i = 1/(i+1)` are antitone. -/
theorem antitone_one_div_succ : Antitone (fun i : ℕ => 1 / ((i : ℝ) + 1)) := by
  intro i j hij
  have hi : (0 : ℝ) < (i : ℝ) + 1 := by positivity
  apply one_div_le_one_div_of_le hi
  exact_mod_cast by simpa using hij

/-- The two-term gap of the harmonic coefficients telescopes to the product form:
`1/(N+1) - 1/(N+2) = 1/((N+1)(N+2))`. -/
theorem oneDiv_gap (N : ℕ) :
    1 / ((N : ℝ) + 1) - 1 / ((N : ℝ) + 2) = 1 / (((N : ℝ) + 1) * ((N : ℝ) + 2)) := by
  have h1 : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have h2 : (0 : ℝ) < (N : ℝ) + 2 := by positivity
  field_simp
  ring

/-- **Two-sided quantitative rate for the alternating harmonic series.** The series
`∑ (-1)^i/(i+1)` converges to a limit `l` (namely `log 2`), and its `N`-th partial sum
approximates `l` with error trapped between the consecutive-term gap and the first omitted
term:

`1/((N+1)(N+2)) ≤ |S_N - l| ≤ 1/(N+1)`.

In particular the convergence is exactly first-order: the error neither beats
`1/((N+1)(N+2)) = Θ(1/N²)` from below nor `1/(N+1) = Θ(1/N)` from above. -/
theorem alternatingHarmonic_error_trapped :
    ∃ l : ℝ, Tendsto (fun n => ∑ i ∈ range n, (-1) ^ i * (1 / ((i : ℝ) + 1))) atTop (𝓝 l) ∧
      ∀ N : ℕ,
        1 / (((N : ℝ) + 1) * ((N : ℝ) + 2))
            ≤ |(∑ i ∈ range N, (-1) ^ i * (1 / ((i : ℝ) + 1))) - l|
          ∧ |(∑ i ∈ range N, (-1) ^ i * (1 / ((i : ℝ) + 1))) - l| ≤ 1 / ((N : ℝ) + 1) := by
  have hfa : Antitone (fun i : ℕ => 1 / ((i : ℝ) + 1)) := antitone_one_div_succ
  have hf0 : Tendsto (fun i : ℕ => 1 / ((i : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  obtain ⟨l, hl⟩ := hfa.tendsto_alternating_series_of_tendsto_zero hf0
  refine ⟨l, hl, fun N => ⟨?_, ?_⟩⟩
  · -- lower bound: rewrite the coefficient gap into product form
    have hlow := sub_le_abs_partialSum_sub_limit hfa hf0 hl N
    -- hlow : (1/(N+1)) - (1/((N+1)+1)) ≤ |S_N - l|
    have hcast : ((N : ℝ) + 1) + 1 = (N : ℝ) + 2 := by ring
    rw [show (((N : ℕ) + 1 : ℕ) : ℝ) = (N : ℝ) + 1 by push_cast; ring] at hlow
    rw [hcast] at hlow
    rw [oneDiv_gap N] at hlow
    exact hlow
  · -- upper bound: the Leibniz estimate at index N
    have hup := abs_partialSum_sub_limit_le hfa hf0 hl N
    simpa using hup

end AlternatingSeriesTestOQ01OQ01
