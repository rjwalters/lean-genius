/-
  Laws of Large Numbers — OQ-01-OQ-02-OQ-01
  Marcinkiewicz–Zygmund SLLN: infrastructure increment (Kronecker's lemma)

  Chain:
    laws-of-large-numbers
      → -oq-01        (heavy-tailed LLN)
      → -oq-01-oq-02  (SLLN rate of convergence)
      → -oq-01-oq-02-oq-01  (this leaf: Marcinkiewicz–Zygmund SLLN, 1 ≤ p < 2)

  The full Marcinkiewicz–Zygmund strong law is a multi-session build; its
  classical proof (truncation + Kolmogorov's convergence criterion) closes with
  a purely analytic step:

    **Kronecker's lemma.** If `a n` is a positive, nondecreasing sequence with
    `a n → ∞` and the series `∑ x n / a n` converges, then the Cesàro-type
    average `(∑_{i<n} x i) / a n → 0`.

  Mathlib has the *unweighted* Cesàro mean (`Filter.Tendsto.cesaro`) and Abel
  summation (`Finset.sum_range_by_parts`), but **no Kronecker lemma** and no
  weighted Toeplitz mean. This file supplies both:

    * `tendsto_weighted_average_zero` — a Toeplitz/Silverman step: nonnegative
      weights whose partial sums are dominated by a normaliser `A n → ∞`,
      applied to a null sequence, give a null weighted average. Independently
      useful and the reusable core.
    * `kronecker_lemma` — Kronecker's lemma for real sequences, via Abel
      summation + the weighted average step.

  Verified: 0 sorry, 0 axiom.
-/
import Mathlib

open Filter Finset
open scoped Topology

namespace LawsOfLargeNumbers.MZ

/-- **Weighted-average / Toeplitz null step.** Let `c i ≥ 0` be weights whose
partial sums `∑_{i<n} c i` are dominated by a normaliser `A n > 0` with
`A n → ∞`. If `e n → 0`, then the normalised weighted sum
`(∑_{i<n} c i * e i) / A n → 0`.

This is the analytic heart of Kronecker's lemma: for large `i` the factor
`e i` is uniformly small, contributing at most `ε · (∑ c i) ≤ ε · A n`, while
the fixed head `∑_{i<N} c i * e i` is a constant washed out by `A n → ∞`. -/
theorem tendsto_weighted_average_zero
    (c e A : ℕ → ℝ)
    (hc : ∀ i, 0 ≤ c i)
    (hA_pos : ∀ n, 0 < A n)
    (hA_top : Tendsto A atTop atTop)
    (hdom : ∀ n, ∑ i ∈ range n, c i ≤ A n)
    (he : Tendsto e atTop (𝓝 0)) :
    Tendsto (fun n => (∑ i ∈ range n, c i * e i) / A n) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  -- `e` is eventually smaller than `ε / 2`.
  have he' := Metric.tendsto_atTop.mp he (ε / 2) (by positivity)
  obtain ⟨N, hN⟩ := he'
  -- the fixed head, a constant once `n ≥ N`
  set H : ℝ := |∑ i ∈ range N, c i * e i| with hHdef
  have hHnonneg : 0 ≤ H := abs_nonneg _
  -- pick a threshold past which `A n` dwarfs the head: `H / A n < ε / 2`
  have hbig : ∀ᶠ n in atTop, 2 * H / ε < A n :=
    hA_top.eventually (eventually_gt_atTop (2 * H / ε))
  obtain ⟨M, hM⟩ := eventually_atTop.mp (hbig.and (eventually_ge_atTop N))
  refine ⟨M, fun n hn => ?_⟩
  obtain ⟨hAn, hnN⟩ := hM n hn
  have hApos := hA_pos n
  -- split the sum at `N`
  have hsplit : ∑ i ∈ range n, c i * e i
      = (∑ i ∈ range N, c i * e i) + ∑ i ∈ Ico N n, c i * e i := by
    rw [Finset.sum_range_add_sum_Ico _ hnN]
  -- bound the tail sum in absolute value by `(ε/2) * ∑_{i<n} c i`
  have htail : |∑ i ∈ Ico N n, c i * e i| ≤ (ε / 2) * ∑ i ∈ range n, c i := by
    calc |∑ i ∈ Ico N n, c i * e i|
        ≤ ∑ i ∈ Ico N n, |c i * e i| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ Ico N n, c i * (ε / 2) := by
            apply Finset.sum_le_sum
            intro i hi
            rw [abs_mul, abs_of_nonneg (hc i)]
            have : |e i| ≤ ε / 2 := by
              have := hN i (mem_Ico.1 hi).1
              rw [Real.dist_eq, sub_zero] at this
              exact this.le
            exact mul_le_mul_of_nonneg_left this (hc i)
      _ = (ε / 2) * ∑ i ∈ Ico N n, c i := by
            rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun i _ => by ring)
      _ ≤ (ε / 2) * ∑ i ∈ range n, c i := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            apply Finset.sum_le_sum_of_subset_of_nonneg
            · rw [range_eq_Ico]; exact Ico_subset_Ico (Nat.zero_le _) le_rfl
            · exact fun i _ _ => hc i
  -- assemble the bound on the whole normalised sum
  rw [Real.dist_eq, sub_zero, abs_div, abs_of_pos hApos]
  rw [div_lt_iff₀ hApos]
  calc |∑ i ∈ range n, c i * e i|
      = |(∑ i ∈ range N, c i * e i) + ∑ i ∈ Ico N n, c i * e i| := by rw [hsplit]
    _ ≤ H + |∑ i ∈ Ico N n, c i * e i| := by
          rw [hHdef]; exact abs_add_le _ _
    _ ≤ H + (ε / 2) * ∑ i ∈ range n, c i := by linarith [htail]
    _ ≤ H + (ε / 2) * A n := by
          have := hdom n
          have : (ε / 2) * ∑ i ∈ range n, c i ≤ (ε / 2) * A n :=
            mul_le_mul_of_nonneg_left this (by positivity)
          linarith
    _ < ε * A n := by
          -- from `2 * H / ε < A n` we get `H < (ε/2) * A n`, hence total `< ε * A n`
          have hHlt : H < (ε / 2) * A n := by
            rw [div_lt_iff₀ hε] at hAn
            nlinarith [hApos, hε]
          linarith

/-- **Kronecker's lemma** for real sequences. If `a` is positive, nondecreasing
and tends to `∞`, and the series `∑ x n / a n` converges, then the weighted
average `(∑_{i<n} x i) / a n → 0`.

At `a n = n` this is the classical fact that convergence of `∑ x n / n` forces
`(∑_{i<n} x i)/n → 0`; the general statement is the analytic engine that turns
a.s. convergence of `∑ (Yᵢ − 𝔼Yᵢ)/i^{1/p}` into the Marcinkiewicz–Zygmund
normalisation `n^{-1/p} ∑_{i<n}(Yᵢ − 𝔼Yᵢ) → 0`. -/
theorem kronecker_lemma
    (a x : ℕ → ℝ) (s : ℝ)
    (ha_pos : ∀ n, 0 < a n)
    (ha_mono : Monotone a)
    (ha_top : Tendsto a atTop atTop)
    (hconv : Tendsto (fun n => ∑ i ∈ range n, x i / a i) atTop (𝓝 s)) :
    Tendsto (fun n => (∑ i ∈ range n, x i) / a n) atTop (𝓝 0) := by
  -- partial sums of the convergent series
  set S : ℕ → ℝ := fun n => ∑ i ∈ range n, x i / a i with hSdef
  have hS : Tendsto S atTop (𝓝 s) := hconv
  -- it suffices to prove the shifted statement (avoids `n - 1` in Abel summation)
  rw [← tendsto_add_atTop_iff_nat 1]
  -- Abel summation, evaluated at `n = m + 1`
  have habel : ∀ m : ℕ,
      (∑ i ∈ range (m + 1), x i)
        = a m * S (m + 1) - ∑ i ∈ range m, (a (i + 1) - a i) * S (i + 1) := by
    intro m
    have hx : ∀ i, a i * (x i / a i) = x i := by
      intro i; have h : a i ≠ 0 := (ha_pos i).ne'; field_simp
    have key := Finset.sum_range_by_parts a (fun i => x i / a i) (m + 1)
    simp only [smul_eq_mul, Nat.add_sub_cancel] at key
    -- `key : ∑ i in range (m+1), a i * (x i / a i)
    --          = a m * (∑ i in range (m+1), x i / a i)
    --            - ∑ i in range m, (a (i+1) - a i) * (∑ j in range (i+1), x j / a j)`
    rw [Finset.sum_congr rfl (fun i _ => hx i)] at key
    exact key
  -- telescoping identity for the weight partial sums
  have hcsum : ∀ m : ℕ, ∑ i ∈ range m, (a (i + 1) - a i) = a m - a 0 :=
    fun m => Finset.sum_range_sub a m
  -- rewrite `(∑_{i≤m} x i) / a (m+1)` via the "telescoped" identity (★):
  --   ∑_{i<m+1} x i = ∑_{i<m} (a(i+1)-a i)*(S(m+1) - S(i+1)) + a 0 * S(m+1)
  have hstar : ∀ m : ℕ,
      (∑ i ∈ range (m + 1), x i)
        = (∑ i ∈ range m, (a (i + 1) - a i) * (S (m + 1) - S (i + 1)))
            + a 0 * S (m + 1) := by
    intro m
    rw [habel m]
    have : ∑ i ∈ range m, (a (i + 1) - a i) * (S (m + 1) - S (i + 1))
        = (∑ i ∈ range m, (a (i + 1) - a i)) * S (m + 1)
          - ∑ i ∈ range m, (a (i + 1) - a i) * S (i + 1) := by
      rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _; ring
    rw [this, hcsum m]; ring
  -- now decompose the two contributions of (★) after dividing by `a (m+1)`
  -- Piece 1 : `a 0 * S (m+1) / a (m+1) → 0`
  have hpiece2 : Tendsto (fun m => a 0 * S (m + 1) / a (m + 1)) atTop (𝓝 0) := by
    have hSshift : Tendsto (fun m => S (m + 1)) atTop (𝓝 s) :=
      hS.comp (tendsto_add_atTop_nat 1)
    have hinv : Tendsto (fun m => (a (m + 1))⁻¹) atTop (𝓝 0) :=
      (ha_top.comp (tendsto_add_atTop_nat 1)).inv_tendsto_atTop
    have : Tendsto (fun m => a 0 * S (m + 1) * (a (m + 1))⁻¹) atTop
        (𝓝 (a 0 * s * 0)) :=
      ((tendsto_const_nhds.mul hSshift).mul hinv)
    simp only [mul_zero] at this
    refine this.congr (fun m => ?_)
    rw [div_eq_mul_inv, mul_assoc]
  -- Piece 2 : `(∑_{i<m} (a(i+1)-a i)*(S(m+1)-S(i+1))) / a (m+1) → 0`
  -- Split `S(m+1)-S(i+1) = (S(m+1)-s) - (S(i+1)-s)`:
  --   = (S(m+1)-s) * ((a m - a 0)/a(m+1))                          [→ 0, bounded × null]
  --     - (∑_{i<m} (a(i+1)-a i)*(S(i+1)-s)) / a(m+1)               [weighted-average step]
  have hSshift : Tendsto (fun m => S (m + 1)) atTop (𝓝 s) :=
    hS.comp (tendsto_add_atTop_nat 1)
  -- Piece 2a
  have hpiece2a :
      Tendsto (fun m => (S (m + 1) - s) * ((a m - a 0) / a (m + 1))) atTop (𝓝 0) := by
    apply squeeze_zero_norm (a := fun m => |S (m + 1) - s|)
    · intro m
      rw [Real.norm_eq_abs, abs_mul]
      have hr : |(a m - a 0) / a (m + 1)| ≤ 1 := by
        rw [abs_div, abs_of_pos (ha_pos (m + 1))]
        rw [div_le_one (ha_pos (m + 1))]
        have h1 : a m ≤ a (m + 1) := ha_mono (Nat.le_succ m)
        have h2 : 0 < a 0 := ha_pos 0
        have h0m : a 0 ≤ a m := ha_mono (Nat.zero_le m)
        rw [abs_le]
        constructor <;> nlinarith [ha_pos (m + 1)]
      calc |S (m + 1) - s| * |(a m - a 0) / a (m + 1)|
          ≤ |S (m + 1) - s| * 1 :=
            mul_le_mul_of_nonneg_left hr (abs_nonneg _)
        _ = |S (m + 1) - s| := by ring
    · have h0 : Tendsto (fun m => S (m + 1) - s) atTop (𝓝 0) := by
        have := hSshift.sub_const s; simpa using this
      simpa using h0.abs
  -- Piece 2b : the weighted-average step with `c i = a(i+1)-a i`, `e i = S(i+1)-s`
  have hpiece2b :
      Tendsto (fun m => (∑ i ∈ range m, (a (i + 1) - a i) * (S (i + 1) - s)) / a (m + 1))
        atTop (𝓝 0) := by
    -- reindex normaliser to `A m = a (m + 1)`
    have hstep := tendsto_weighted_average_zero
      (fun i => a (i + 1) - a i) (fun i => S (i + 1) - s) (fun m => a (m + 1))
      (fun i => by have := ha_mono (Nat.le_succ i); linarith)
      (fun m => ha_pos (m + 1))
      (ha_top.comp (tendsto_add_atTop_nat 1))
      (fun m => by
        rw [hcsum m]
        have h1 : a m ≤ a (m + 1) := ha_mono (Nat.le_succ m)
        have h2 : 0 < a 0 := ha_pos 0
        linarith)
      (by
        have : Tendsto (fun m => S (m + 1) - s) atTop (𝓝 0) := by
          have := hSshift.sub_const s; simpa using this
        exact this)
    exact hstep
  -- combine everything
  -- target function `= piece2a - piece2b + piece2` after dividing (★) by `a (m+1)`
  have hcombine : Tendsto
      (fun m => (S (m + 1) - s) * ((a m - a 0) / a (m + 1))
        - (∑ i ∈ range m, (a (i + 1) - a i) * (S (i + 1) - s)) / a (m + 1)
        + a 0 * S (m + 1) / a (m + 1)) atTop (𝓝 0) := by
    have := (hpiece2a.sub hpiece2b).add hpiece2
    simpa using this
  refine hcombine.congr (fun m => ?_)
  -- pointwise identity: rewrite target using (★) and the S-shift split
  rw [hstar m]
  have hApos := (ha_pos (m + 1)).ne'
  have hsplitnum :
      (∑ i ∈ range m, (a (i + 1) - a i) * (S (m + 1) - S (i + 1)))
        = (S (m + 1) - s) * (a m - a 0)
          - ∑ i ∈ range m, (a (i + 1) - a i) * (S (i + 1) - s) := by
    rw [← hcsum m, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _; ring
  rw [hsplitnum]
  field_simp

end LawsOfLargeNumbers.MZ
