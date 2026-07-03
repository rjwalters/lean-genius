/-
  Laws of Large Numbers — OQ-01-OQ-02-OQ-01
  Marcinkiewicz–Zygmund SLLN: infrastructure increment (Kronecker's lemma)

  Chain:
    laws-of-large-numbers
      → -oq-01        (heavy-tailed LLN)
      → -oq-01-oq-02  (SLLN rate of convergence)
      → -oq-01-oq-02-oq-01  (this leaf: Marcinkiewicz–Zygmund SLLN, 1 ≤ p < 2)

  The full Marcinkiewicz–Zygmund strong law is a multi-session build; its
  classical proof factors into a purely analytic passage (Kronecker's lemma)
  and a probabilistic engine (Kolmogorov's convergence criterion). This file
  supplies the reusable infrastructure for both.

  **Analytic core — Kronecker's lemma.** If `a n` is a positive, nondecreasing
  sequence with `a n → ∞` and the series `∑ x n / a n` converges, then the
  Cesàro-type average `(∑_{i<n} x i) / a n → 0`. Mathlib has the *unweighted*
  Cesàro mean (`Filter.Tendsto.cesaro`) and Abel summation
  (`Finset.sum_range_by_parts`), but **no Kronecker lemma** and no weighted
  Toeplitz mean; we supply both:

    * `tendsto_weighted_average_zero` — a Toeplitz/Silverman step: nonnegative
      weights whose partial sums are dominated by a normaliser `A n → ∞`,
      applied to a null sequence, give a null weighted average. Reusable core.
    * `kronecker_lemma` — Kronecker's lemma for real sequences, via Abel
      summation + the weighted average step.
    * `ae_tendsto_kronecker_average_zero` — the a.e. lift of `kronecker_lemma`
      across a sample space (S3 → S4 glue).

  **Probabilistic engine — Kolmogorov's convergence criterion (§ Kolmogorov).**
  For independent mean-zero `L²` variables with `∑ Var < ∞`, the series `∑ Xᵢ`
  converges a.s. We assemble this from Mathlib's a.e. martingale-convergence
  theorem, contributing the two pieces the S3 survey flagged as missing:

    * `martingale_sum_of_indep_mean_zero` — the shifted partial sums form a
      martingale w.r.t. the natural filtration (increment independent of the
      past ⟹ conditional expectation collapses to the vanishing mean).
    * `ae_tendsto_sum_of_indep_of_eLpNorm_bdd` — Kolmogorov's criterion reduced
      to a uniform `L¹` bound on the partial sums, via
      `Submartingale.exists_ae_tendsto_of_bdd`.

  **Truncation input — discrete layer cake (§ TailSum, step 2).** The MZ
  truncation `Yᵢ = Xᵢ·𝟙{|Xᵢ| ≤ i^{1/p}}` is justified by Borel–Cantelli, whose
  input is the summable tail `∑ᵢ P(|Xᵢ| > i^{1/p}) < ∞`. For `Z = |X₀|ᵖ` this is
  the deterministic tail-sum bound below; Mathlib has the continuous layer cake
  but no discrete companion, so we supply it:

    * `tsum_measure_add_one_le_lintegral` — `∑ₙ μ{Z ≥ n+1} ≤ ∫⁻ ofReal Z` for
      measurable `Z ≥ 0`, via `lintegral_tsum` and the pointwise count
      `∑ₙ 𝟙{n+1 ≤ Z} = ⌊Z⌋₊ ≤ Z`.
    * `tsum_measure_add_one_ne_top` — the finiteness corollary that feeds the
      first Borel–Cantelli lemma.

  **Capstone — Kolmogorov + Kronecker (§ KolmogorovKronecker).** The analytic and
  probabilistic halves are finally composed into the normalisation step of the
  Marcinkiewicz–Zygmund law itself:

    * `ae_tendsto_average_zero_of_variance_weighted_bdd` — for independent
      mean-zero `L²` variables `Yᵢ` and a positive nondecreasing weight `aₙ → ∞`
      with `∑ᵢ Var(Yᵢ)/aᵢ² < ∞`, almost surely `aₙ⁻¹ ∑_{i<n} Yᵢ → 0`. Obtained by
      running Kolmogorov's criterion on the rescaled `Xᵢ = aᵢ⁻¹·Yᵢ` and feeding
      its a.s.-convergence output through the a.e. Kronecker lift.

  Verified: 0 sorry, 0 axiom (only `propext`/`Classical.choice`/`Quot.sound`).
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

/-! ## Almost-everywhere Kronecker lift (S3 → S4 glue)

The Marcinkiewicz–Zygmund strong law is assembled from two pieces:

* **Kolmogorov's convergence criterion** (probabilistic, still to build): for
  independent mean-zero `L²` variables `Yᵢ` with `∑ Var(Yᵢ)/aᵢ² < ∞`, the series
  `∑ Yᵢ / aᵢ` converges *almost surely*.
* **Kronecker's lemma** (`kronecker_lemma`, deterministic, above): pointwise,
  convergence of `∑ xᵢ / aᵢ` forces `(∑_{i<n} xᵢ) / aₙ → 0`.

The lemma below is the deterministic *glue* between them: it lifts
`kronecker_lemma` across the sample space, turning the criterion's a.s.-
convergence output directly into the M–Z normalisation conclusion. With this in
place, the only remaining gap for the full M–Z SLLN is the probabilistic
criterion itself; the analytic passage to the conclusion is complete and
axiom-free. -/

open MeasureTheory in
/-- **A.e. Kronecker lift.** Fix a positive, nondecreasing weight sequence `a`
with `a n → ∞`. If, for almost every sample point `ω`, the real series
`∑ x i ω / a i` converges, then for almost every `ω` the Kronecker average
`(∑_{i<n} x i ω) / a n → 0`. This is the pointwise lift of `kronecker_lemma`
that connects Kolmogorov's a.s.-convergence criterion to the
Marcinkiewicz–Zygmund conclusion. -/
theorem ae_tendsto_kronecker_average_zero
    {Ω : Type*} {_ : MeasurableSpace Ω} {μ : Measure Ω}
    (a : ℕ → ℝ) (x : ℕ → Ω → ℝ)
    (ha_pos : ∀ n, 0 < a n)
    (ha_mono : Monotone a)
    (ha_top : Tendsto a atTop atTop)
    (hconv : ∀ᵐ ω ∂μ,
      ∃ s : ℝ, Tendsto (fun n => ∑ i ∈ range n, x i ω / a i) atTop (𝓝 s)) :
    ∀ᵐ ω ∂μ,
      Tendsto (fun n => (∑ i ∈ range n, x i ω) / a n) atTop (𝓝 0) := by
  filter_upwards [hconv] with ω hω
  obtain ⟨s, hs⟩ := hω
  exact kronecker_lemma a (fun i => x i ω) s ha_pos ha_mono ha_top hs

/-! ## Kolmogorov's a.s.-convergence criterion — martingale assembly (S3)

The probabilistic engine of the Marcinkiewicz–Zygmund proof (step 4 of the
classical decomposition) is **Kolmogorov's convergence criterion**: for
independent mean-zero `L²` random variables `Xᵢ` with `∑ Var(Xᵢ) < ∞`, the
series `∑ Xᵢ` converges almost surely.

The route is the a.e. martingale-convergence theorem. The shifted partial sums
`f n = ∑_{i≤n} Xᵢ` form a **martingale** with respect to the natural filtration
`ℱ = natural X` (`ℱ n = σ(X₀,…,Xₙ)`): the increment `f (n+1) − f n = X (n+1)` is
independent of the past σ-algebra `ℱ n`, so `𝔼[X (n+1) | ℱ n] = 𝔼[X (n+1)] = 0`.
An `L¹`-bounded submartingale converges a.s. by
`MeasureTheory.Submartingale.exists_ae_tendsto_of_bdd`; on a probability space a
uniform `L¹` bound on the partial sums follows from a uniform `L²` bound, i.e.
from `∑ Var(Xᵢ) < ∞`.

This section supplies the two *assembly* bricks flagged by the S3 survey — the
martingale construction and the reduction to the convergence engine — leaving
only the deterministic `∑ Var → L²`-bound bookkeeping (via
`ProbabilityTheory.IndepFun.variance_sum`) for the final step. Neither brick
introduces an axiom; the leaf stays on the 0-axiom track. -/

section Kolmogorov

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- **Independent mean-zero partial sums are a martingale.** For independent,
integrable random variables `X i` with `𝔼[X i] = 0`, the shifted partial sums
`f n = ∑_{i < n+1} X i` form a martingale with respect to the natural filtration
of `X`.

This is the probabilistic heart of Kolmogorov's convergence criterion: the
martingale increment `f (n+1) − f n = X (n+1)` is independent of the past
σ-algebra `ℱ n = σ(X₀,…,Xₙ)`, so its conditional expectation collapses to the
(vanishing) mean. Built from Mathlib's `iIndepFun.condExp_natural_ae_eq_of_lt`
and the increment criterion `martingale_of_condExp_sub_eq_zero_nat`. -/
theorem martingale_sum_of_indep_mean_zero [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hmeas : ∀ i, StronglyMeasurable (X i))
    (hindep : iIndepFun X μ) (hint : ∀ i, Integrable (X i) μ)
    (hmean : ∀ i, μ[X i] = 0) :
    Martingale (fun n => ∑ i ∈ range (n + 1), X i)
      (Filtration.natural X hmeas) μ := by
  -- adaptedness: each `Xᵢ` (i ≤ n) is `ℱ n`-measurable, so is the finite sum
  have hadp : Adapted (Filtration.natural X hmeas)
      (fun n => ∑ i ∈ range (n + 1), X i) := by
    intro n
    refine Finset.stronglyMeasurable_sum _ (fun i hi => ?_)
    have hi' : i ≤ n := by simp only [Finset.mem_range] at hi; omega
    exact (Filtration.adapted_natural hmeas i).mono
      ((Filtration.natural X hmeas).mono hi')
  refine martingale_of_condExp_sub_eq_zero_nat hadp ?_ ?_
  · -- integrability of each partial sum
    intro n
    exact integrable_finset_sum' _ (fun i _ => hint i)
  · -- the increment's conditional expectation given the past vanishes
    intro n
    have hincr : (fun n => ∑ i ∈ range (n + 1), X i) (n + 1)
        - (fun n => ∑ i ∈ range (n + 1), X i) n = X (n + 1) := by
      funext ω
      simp only [Pi.sub_apply, Finset.sum_apply]
      rw [Finset.sum_range_succ]
      ring
    rw [hincr]
    have hcond := iIndepFun.condExp_natural_ae_eq_of_lt hmeas hindep (Nat.lt_succ_self n)
    filter_upwards [hcond] with ω hω
    simp only [hω, Pi.zero_apply]
    exact hmean (n + 1)

/-- **Kolmogorov's a.s.-convergence criterion, reduced to the `L¹` bound.** For
independent mean-zero integrable random variables `X i` whose shifted partial
sums `∑_{i≤n} Xᵢ` are uniformly bounded in `L¹`, the series `∑ i, X i` converges
almost surely.

This is Kolmogorov's convergence criterion modulo the deterministic `L¹` bound
`hbdd` (which on a probability space follows from `∑ Var(X i) < ∞` via a uniform
`L²` bound and `eLpNorm` monotonicity in the exponent). The proof feeds the
partial-sum martingale into `Submartingale.exists_ae_tendsto_of_bdd` and shifts
the index back from `∑_{i≤n}` to `∑_{i<n}`. Composing this with the a.e.
Kronecker lift `ae_tendsto_kronecker_average_zero` yields the normalisation
conclusion of the Marcinkiewicz–Zygmund strong law. -/
theorem ae_tendsto_sum_of_indep_of_eLpNorm_bdd [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hmeas : ∀ i, StronglyMeasurable (X i))
    (hindep : iIndepFun X μ) (hint : ∀ i, Integrable (X i) μ)
    (hmean : ∀ i, μ[X i] = 0) (R : ℝ≥0)
    (hbdd : ∀ n, eLpNorm (fun ω => ∑ i ∈ range (n + 1), X i ω) 1 μ ≤ (R : ℝ≥0∞)) :
    ∀ᵐ ω ∂μ, ∃ c : ℝ, Tendsto (fun n => ∑ i ∈ range n, X i ω) atTop (𝓝 c) := by
  have hmg := martingale_sum_of_indep_mean_zero X hmeas hindep hint hmean
  have hsub := hmg.submartingale
  -- put the `L¹` bound in the shape the engine expects (sum-of-functions form)
  have hbdd' : ∀ n, eLpNorm ((fun n => ∑ i ∈ range (n + 1), X i) n) 1 μ ≤ (R : ℝ≥0∞) := by
    intro n
    have hfun : ((fun n => ∑ i ∈ range (n + 1), X i) n)
        = (fun ω => ∑ i ∈ range (n + 1), X i ω) := by
      funext ω; simp only [Finset.sum_apply]
    rw [hfun]; exact hbdd n
  have hconv := hsub.exists_ae_tendsto_of_bdd hbdd'
  filter_upwards [hconv] with ω hω
  obtain ⟨c, hc⟩ := hω
  refine ⟨c, ?_⟩
  -- rewrite the pointwise partial sums and shift the index down by one
  have hc' : Tendsto (fun n => ∑ i ∈ range (n + 1), X i ω) atTop (𝓝 c) := by
    refine hc.congr (fun n => ?_)
    simp only [Finset.sum_apply]
  exact (tendsto_add_atTop_iff_nat 1).mp hc'

/-! ## S4a — discharging the `L¹` bound from a variance-sum bound

The convergence engine `ae_tendsto_sum_of_indep_of_eLpNorm_bdd` requires a uniform
`L¹` bound `hbdd` on the partial sums.  On a probability space this is exactly what a
bound on the variance sums `∑ Var(Xᵢ)` provides, via `‖·‖₁ ≤ ‖·‖₂` and the
orthogonality identity `Var(∑ Xᵢ) = ∑ Var(Xᵢ)` for independent variables.  The one
missing link is the mean-zero bridge `‖X‖₂² = eVar[X]` (Mathlib has `evariance` and
`eLpNorm` but no lemma connecting them), supplied here. -/

/-- **`L²` seminorm squared equals the extended variance, for a mean-zero variable.**
For `X` with `𝔼[X] = 0`,

    eLpNorm X 2 μ ^ 2 = evariance X μ.

Mathlib defines `evariance X μ = ∫⁻ ‖X - 𝔼[X]‖ₑ²` and `eLpNorm X 2 μ` separately with no
bridge between them; when `𝔼[X] = 0` the centering is trivial and the two coincide after
the standard `(∫⁻ ‖X‖ₑ²)^{1/2}` unfolding of the `L²` seminorm.  This is the crux that
turns a variance bound into the `L¹` hypothesis of the Kolmogorov engine. -/
theorem eLpNorm_two_sq_eq_evariance {X : Ω → ℝ} (h0 : μ[X] = 0) :
    eLpNorm X 2 μ ^ 2 = evariance X μ := by
  rw [eLpNorm_eq_lintegral_rpow_enorm (by norm_num) (by norm_num), evariance]
  simp only [h0, sub_zero, ENNReal.toReal_ofNat]
  rw [← ENNReal.rpow_natCast ((∫⁻ x, ‖X x‖ₑ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ))) 2,
    ← ENNReal.rpow_mul, show (1 / (2 : ℝ)) * ((2 : ℕ) : ℝ) = 1 by norm_num, ENNReal.rpow_one]
  simp_rw [ENNReal.rpow_two]

/-- **Uniform `L²` bound on the partial sums from a variance-sum bound.**  For
independent mean-zero `L²` variables `X i` with `∑_{i≤n} Var(Xᵢ) ≤ V` for all `n`,
every shifted partial sum satisfies

    eLpNorm (∑_{i≤n} Xᵢ) 2 μ ≤ ENNReal.ofReal (√V).

Proof: `‖Sₙ‖₂² = eVar[Sₙ] = ofReal(Var Sₙ) = ofReal(∑_{i≤n} Var Xᵢ) ≤ ofReal V` using the
mean-zero bridge `eLpNorm_two_sq_eq_evariance`, `ofReal_variance`, and the independence
orthogonality identity `IndepFun.variance_sum`; then take square roots by the monotone
`ℝ≥0∞`-power `·^{1/2}`. -/
theorem eLpNorm_two_partialSum_le [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hindep : iIndepFun X μ) (hmemLp : ∀ i, MemLp (X i) 2 μ)
    (hmean : ∀ i, μ[X i] = 0) (V : ℝ)
    (hV : ∀ n, ∑ i ∈ range (n + 1), variance (X i) μ ≤ V) (n : ℕ) :
    eLpNorm (fun ω => ∑ i ∈ range (n + 1), X i ω) 2 μ ≤ ENNReal.ofReal (Real.sqrt V) := by
  have hint : ∀ i, Integrable (X i) μ := fun i => (hmemLp i).integrable one_le_two
  have hSpt : (fun ω => ∑ i ∈ range (n + 1), X i ω) = ∑ i ∈ range (n + 1), X i := by
    funext ω; simp only [Finset.sum_apply]
  rw [hSpt]
  set S : Ω → ℝ := ∑ i ∈ range (n + 1), X i with hSdef
  have hSmemLp : MemLp S 2 μ := memLp_finset_sum' _ (fun i _ => hmemLp i)
  have hSmean : μ[S] = 0 := by
    have h1 : μ[S] = ∑ i ∈ range (n + 1), μ[X i] := by
      simp_rw [hSdef, Finset.sum_apply]
      exact integral_finset_sum _ (fun i _ => hint i)
    rw [h1]; simp only [hmean, Finset.sum_const_zero]
  have hpair : Set.Pairwise (↑(range (n + 1)) : Set ℕ)
      (fun i j => IndepFun (X i) (X j) μ) := fun i _ j _ hij => hindep.indepFun hij
  have hvar : variance S μ = ∑ i ∈ range (n + 1), variance (X i) μ := by
    rw [hSdef]; exact IndepFun.variance_sum (fun i _ => hmemLp i) hpair
  have hV0 : 0 ≤ V := le_trans (variance_nonneg (X 0) μ) (by simpa using hV 0)
  have hsq : eLpNorm S 2 μ ^ 2 ≤ ENNReal.ofReal V := by
    rw [eLpNorm_two_sq_eq_evariance hSmean, ← ofReal_variance hSmemLp, hvar]
    exact ENNReal.ofReal_le_ofReal (hV n)
  have hmono := ENNReal.rpow_le_rpow hsq (by norm_num : (0 : ℝ) ≤ 1 / 2)
  rw [← ENNReal.rpow_natCast (eLpNorm S 2 μ) 2, ← ENNReal.rpow_mul,
    show ((2 : ℕ) : ℝ) * (1 / (2 : ℝ)) = 1 by norm_num, ENNReal.rpow_one] at hmono
  -- rewrite the `L²` bound `(ofReal V)^{1/2}` as `ofReal √V`
  have hrw : ENNReal.ofReal V ^ (1 / 2 : ℝ) = ENNReal.ofReal (Real.sqrt V) := by
    rw [Real.sqrt_eq_rpow, ENNReal.ofReal_rpow_of_nonneg hV0 (by norm_num)]
  exact hmono.trans_eq hrw

/-- **Kolmogorov's a.s.-convergence criterion (variance-sum form).**  For independent
mean-zero `L²` random variables `X i` whose variance partial sums are uniformly bounded,
`∑_{i≤n} Var(Xᵢ) ≤ V`, the series `∑ i, X i` converges almost surely.

This discharges the deterministic `L¹` hypothesis `hbdd` of
`ae_tendsto_sum_of_indep_of_eLpNorm_bdd` from the variance-sum bound, via
`eLpNorm_two_partialSum_le` and `‖·‖₁ ≤ ‖·‖₂` on a probability space
(`eLpNorm_le_eLpNorm_of_exponent_le`).  It is the clean statement of Kolmogorov's
convergence theorem; composing it with the a.e. Kronecker lift
`ae_tendsto_kronecker_average_zero` gives the normalisation step of the
Marcinkiewicz–Zygmund strong law. -/
theorem ae_tendsto_sum_of_indep_of_variance_bdd [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hmeas : ∀ i, StronglyMeasurable (X i))
    (hindep : iIndepFun X μ) (hmemLp : ∀ i, MemLp (X i) 2 μ)
    (hmean : ∀ i, μ[X i] = 0) (V : ℝ)
    (hV : ∀ n, ∑ i ∈ range (n + 1), variance (X i) μ ≤ V) :
    ∀ᵐ ω ∂μ, ∃ c : ℝ, Tendsto (fun n => ∑ i ∈ range n, X i ω) atTop (𝓝 c) := by
  have hint : ∀ i, Integrable (X i) μ := fun i => (hmemLp i).integrable one_le_two
  refine ae_tendsto_sum_of_indep_of_eLpNorm_bdd X hmeas hindep hint hmean
    (Real.sqrt V).toNNReal (fun n => ?_)
  have hasm : AEStronglyMeasurable (fun ω => ∑ i ∈ range (n + 1), X i ω) μ := by
    have hEq : (fun ω => ∑ i ∈ range (n + 1), X i ω) = ∑ i ∈ range (n + 1), X i := by
      funext ω; simp only [Finset.sum_apply]
    rw [hEq]; exact (memLp_finset_sum' _ (fun i _ => hmemLp i)).aestronglyMeasurable
  have h12 : eLpNorm (fun ω => ∑ i ∈ range (n + 1), X i ω) 1 μ
      ≤ eLpNorm (fun ω => ∑ i ∈ range (n + 1), X i ω) 2 μ :=
    eLpNorm_le_eLpNorm_of_exponent_le (by norm_num) hasm
  have hcoe : ((Real.sqrt V).toNNReal : ℝ≥0∞) = ENNReal.ofReal (Real.sqrt V) := rfl
  rw [hcoe]
  exact h12.trans (eLpNorm_two_partialSum_le X hindep hmemLp hmean V hV n)

end Kolmogorov

/-! ## S4b (step 2) — the tail-sum / Borel–Cantelli input

The Marcinkiewicz–Zygmund truncation `Yᵢ = Xᵢ·𝟙{|Xᵢ| ≤ i^{1/p}}` is justified by the
first Borel–Cantelli lemma: `∑ᵢ P(Xᵢ ≠ Yᵢ) = ∑ᵢ P(|Xᵢ| > i^{1/p}) < ∞`, so a.s.
`Xᵢ = Yᵢ` eventually and it suffices to prove the law for the truncations.  For
identically distributed `Xᵢ` and `Z := |X₀|ᵖ ≥ 0`, this reduces to the deterministic
measure-theoretic fact that the **tail sum** `∑ₙ μ{Z ≥ n+1}` is dominated by the first
moment `∫⁻ ofReal Z` — the discrete companion of the layer-cake formula.  Mathlib has
the continuous layer cake (`lintegral_eq_lintegral_meas_le`) but no discrete tail-sum
bound; we supply it, together with the finiteness corollary that feeds Borel–Cantelli. -/

section TailSum

open MeasureTheory
open scoped ENNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- **Pointwise tail count is bounded by the value.**  For `z ≥ 0`, the number of
positive integers `n+1 ≤ z` — counted in `ℝ≥0∞` as `∑ₙ 𝟙{n+1 ≤ z}` — equals `⌊z⌋₊`,
and hence is at most `z`. -/
theorem tsum_indicator_add_one_le (z : ℝ) (hz : 0 ≤ z) :
    ∑' n : ℕ, (if (n : ℝ) + 1 ≤ z then (1 : ℝ≥0∞) else 0) ≤ ENNReal.ofReal z := by
  have hiff : ∀ n : ℕ, ((n : ℝ) + 1 ≤ z) ↔ n < ⌊z⌋₊ := by
    intro n
    rw [show (n : ℝ) + 1 = ((n + 1 : ℕ) : ℝ) by push_cast; ring,
      ← Nat.le_floor_iff hz, Nat.add_one_le_iff]
  have hcount : ∑' n : ℕ, (if (n : ℝ) + 1 ≤ z then (1 : ℝ≥0∞) else 0) = (⌊z⌋₊ : ℝ≥0∞) := by
    have hcongr : ∀ n : ℕ, (if (n : ℝ) + 1 ≤ z then (1 : ℝ≥0∞) else 0)
        = (if n < ⌊z⌋₊ then (1 : ℝ≥0∞) else 0) := fun n => by simp only [hiff n]
    simp_rw [hcongr]
    rw [tsum_eq_sum (s := Finset.range ⌊z⌋₊) fun n hn => if_neg (by simpa using hn),
      Finset.sum_congr rfl fun n hn => if_pos (Finset.mem_range.mp hn),
      Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  rw [hcount, ← ENNReal.ofReal_natCast]
  exact ENNReal.ofReal_le_ofReal (Nat.floor_le hz)

/-- **Discrete tail-sum bound (discrete layer cake / first-moment estimate).**  For a
measurable `Z ≥ 0`, the tail sum of super-level measures is dominated by the first
moment:

    ∑ₙ μ {ω | (n : ℝ) + 1 ≤ Z ω}  ≤  ∫⁻ ω, ENNReal.ofReal (Z ω) ∂μ.

This is the discrete companion of the layer-cake formula and the analytic core of the
Marcinkiewicz–Zygmund truncation step (step 2): applied to `Z = |X₀|ᵖ` it turns the
finite `p`-th moment `𝔼|X₀|ᵖ < ∞` into a summable tail `∑ᵢ P(|Xᵢ| > i^{1/p}) < ∞`.
Proof: write each `μ Aₙ` as the integral of `𝟙_{Aₙ}`, swap sum and integral
(`lintegral_tsum`), and bound the pointwise tail count `∑ₙ 𝟙{n+1 ≤ Z ω} = ⌊Z ω⌋₊ ≤ Z ω`. -/
theorem tsum_measure_add_one_le_lintegral {Z : Ω → ℝ}
    (hZmeas : Measurable Z) (hZnn : 0 ≤ Z) :
    ∑' n : ℕ, μ {x | (n : ℝ) + 1 ≤ Z x} ≤ ∫⁻ ω, ENNReal.ofReal (Z ω) ∂μ := by
  have hA : ∀ n : ℕ, MeasurableSet {x | (n : ℝ) + 1 ≤ Z x} := fun n =>
    measurableSet_le measurable_const hZmeas
  have hswap : ∑' n : ℕ, μ {x | (n : ℝ) + 1 ≤ Z x}
      = ∫⁻ ω, ∑' n : ℕ, ({x | (n : ℝ) + 1 ≤ Z x}.indicator 1) ω ∂μ :=
    calc ∑' n : ℕ, μ {x | (n : ℝ) + 1 ≤ Z x}
        = ∑' n : ℕ, ∫⁻ ω, ({x | (n : ℝ) + 1 ≤ Z x}.indicator 1) ω ∂μ :=
          tsum_congr fun n => (lintegral_indicator_one (hA n)).symm
      _ = ∫⁻ ω, ∑' n : ℕ, ({x | (n : ℝ) + 1 ≤ Z x}.indicator 1) ω ∂μ :=
          (lintegral_tsum fun n => (measurable_const.indicator (hA n)).aemeasurable).symm
  rw [hswap]
  refine lintegral_mono fun ω => ?_
  have hpt : (∑' n : ℕ, ({x | (n : ℝ) + 1 ≤ Z x}.indicator (1 : Ω → ℝ≥0∞)) ω)
      = ∑' n : ℕ, (if (n : ℝ) + 1 ≤ Z ω then (1 : ℝ≥0∞) else 0) :=
    tsum_congr fun n => by rw [Set.indicator_apply]; simp [Set.mem_setOf_eq]
  rw [hpt]
  exact tsum_indicator_add_one_le (Z ω) (hZnn ω)

/-- **Summable tail from a finite first moment.**  If `Z ≥ 0` is measurable with finite
first moment `∫⁻ ofReal Z < ∞`, the super-level tail sum is finite:
`∑ₙ μ{Z ≥ n+1} ≠ ∞`.  This is exactly the hypothesis consumed by the first
Borel–Cantelli lemma (`MeasureTheory.measure_limsup_eq_zero`), which then gives
`Z < n+1` eventually a.s. — i.e. the MZ truncation `|Xᵢ| ≤ i^{1/p}` holds eventually. -/
theorem tsum_measure_add_one_ne_top {Z : Ω → ℝ}
    (hZmeas : Measurable Z) (hZnn : 0 ≤ Z)
    (hZint : ∫⁻ ω, ENNReal.ofReal (Z ω) ∂μ ≠ ∞) :
    ∑' n : ℕ, μ {x | (n : ℝ) + 1 ≤ Z x} ≠ ∞ :=
  ((tsum_measure_add_one_le_lintegral hZmeas hZnn).trans_lt hZint.lt_top).ne

end TailSum

/-! ## S5 — Kolmogorov + Kronecker: the SLLN normalisation step

The two engines built above are finally composed. Kolmogorov's criterion
(`ae_tendsto_sum_of_indep_of_variance_bdd`) turns a variance-sum bound into a.s.
convergence of a series `∑ Xᵢ`; the a.e. Kronecker lift
(`ae_tendsto_kronecker_average_zero`) turns a.s. convergence of `∑ Yᵢ/aᵢ` into
the normalised average `(∑_{i<n} Yᵢ)/aₙ → 0`. Feeding the rescaled variables
`Xᵢ = aᵢ⁻¹·Yᵢ` into the former and its output into the latter yields, in one
clean statement, the **normalisation step of the Marcinkiewicz–Zygmund strong
law**: for independent mean-zero `L²` variables `Yᵢ` and a positive nondecreasing
weight `aₙ → ∞` with `∑ᵢ Var(Yᵢ)/aᵢ² < ∞`, almost surely `aₙ⁻¹ ∑_{i<n} Yᵢ → 0`.

At `aₙ = n` and `Yᵢ = Xᵢ − 𝔼Xᵢ` this is Kolmogorov's classical SLLN under the
`∑ Var(Xᵢ)/i² < ∞` hypothesis; the general weight is precisely the normaliser
the MZ truncation feeds in. This is the capstone tying the file's analytic and
probabilistic halves together — still on the 0-axiom track. -/

section KolmogorovKronecker

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- **Kolmogorov–Kronecker normalisation step of the Marcinkiewicz–Zygmund SLLN.**
For independent mean-zero `L²` random variables `Y i`, and a positive,
nondecreasing weight sequence `a` with `a n → ∞` whose weighted variance partial
sums are uniformly bounded, `∑_{i≤n} Var(Yᵢ)/aᵢ² ≤ V`, the normalised averages
converge to zero almost surely:

    (∑_{i<n} Yᵢ) / aₙ → 0     a.s.

Proof: apply Kolmogorov's criterion `ae_tendsto_sum_of_indep_of_variance_bdd` to
the rescaled variables `Xᵢ = aᵢ⁻¹·Yᵢ` — independence is preserved by
`iIndepFun.comp`, the `L²` and mean-zero properties by `MemLp.const_mul` and
`integral_const_mul`, and `Var(Xᵢ) = aᵢ⁻²·Var(Yᵢ)` by `variance_const_mul`, so
the weighted-variance hypothesis becomes the plain variance-sum bound the engine
needs — obtaining a.s. convergence of `∑ᵢ Yᵢ/aᵢ`; then feed that into the a.e.
Kronecker lift `ae_tendsto_kronecker_average_zero`. -/
theorem ae_tendsto_average_zero_of_variance_weighted_bdd [IsProbabilityMeasure μ]
    (Y : ℕ → Ω → ℝ) (a : ℕ → ℝ)
    (hmeas : ∀ i, StronglyMeasurable (Y i))
    (hindep : iIndepFun Y μ) (hmemLp : ∀ i, MemLp (Y i) 2 μ)
    (hmean : ∀ i, μ[Y i] = 0)
    (ha_pos : ∀ n, 0 < a n) (ha_mono : Monotone a) (ha_top : Tendsto a atTop atTop)
    (V : ℝ)
    (hV : ∀ n, ∑ i ∈ range (n + 1), variance (Y i) μ / (a i) ^ 2 ≤ V) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => (∑ i ∈ range n, Y i ω) / a n) atTop (𝓝 0) := by
  -- rescaled variables `Xᵢ = aᵢ⁻¹ · Yᵢ`
  set X : ℕ → Ω → ℝ := fun i ω => (a i)⁻¹ * Y i ω with hXdef
  have hXmeas : ∀ i, StronglyMeasurable (X i) := fun i => (hmeas i).const_mul _
  have hXindep : iIndepFun X μ := by
    have h := hindep.comp (fun i (y : ℝ) => (a i)⁻¹ * y)
      (fun i => measurable_const.mul measurable_id)
    simpa [hXdef, Function.comp] using h
  have hXmemLp : ∀ i, MemLp (X i) 2 μ := fun i => (hmemLp i).const_mul _
  have hXmean : ∀ i, μ[X i] = 0 := by
    intro i
    simp only [hXdef, integral_const_mul, hmean i, mul_zero]
  -- `Var(Xᵢ) = aᵢ⁻² · Var(Yᵢ) = Var(Yᵢ)/aᵢ²`
  have hXvar : ∀ i, variance (X i) μ = variance (Y i) μ / (a i) ^ 2 := by
    intro i
    rw [hXdef, variance_const_mul, inv_pow, div_eq_inv_mul]
  -- Kolmogorov's criterion for the rescaled variables gives a.s. convergence of `∑ Xᵢ`
  have hconv := ae_tendsto_sum_of_indep_of_variance_bdd X hXmeas hXindep hXmemLp hXmean V
    (fun n => by simp_rw [hXvar]; exact hV n)
  -- rewrite `∑ Xᵢ ω = ∑ Yᵢ ω / aᵢ` to feed the Kronecker lift
  have hconv' : ∀ᵐ ω ∂μ, ∃ s : ℝ,
      Tendsto (fun n => ∑ i ∈ range n, Y i ω / a i) atTop (𝓝 s) := by
    filter_upwards [hconv] with ω hω
    obtain ⟨c, hc⟩ := hω
    refine ⟨c, hc.congr (fun n => ?_)⟩
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp only [hXdef, div_eq_inv_mul]
  exact ae_tendsto_kronecker_average_zero a Y ha_pos ha_mono ha_top hconv'

end KolmogorovKronecker

end LawsOfLargeNumbers.MZ
