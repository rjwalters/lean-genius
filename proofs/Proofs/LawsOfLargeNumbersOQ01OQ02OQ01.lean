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
  The trailing § TruncationMomentKernels (the two S4b step-3/4 pointwise `rpow`
  kernels) is now machine-checked: `docker-build.sh Proofs.LawsOfLargeNumbersOQ01OQ02OQ01`
  → Built (7743 jobs, exit 0). Pure `Real.rpow` real-analysis, no
  `decide`/`native_decide`/`sorry`/`axiom`, so 0-axiom by construction.
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

/-! ## S4b (step 1) — i.i.d. truncation reduction via first Borel–Cantelli

The Marcinkiewicz–Zygmund proof replaces `Xᵢ` by the truncation
`Yᵢ = Xᵢ·𝟙{|Xᵢ| ≤ i^{1/p}}`.  The replacement is justified by the **first
Borel–Cantelli lemma**: if the tail sum `∑ᵢ P(|Xᵢ| > i^{1/p})` is finite then a.s.
`Xᵢ = Yᵢ` for all large `i`, so it suffices to prove the law for the truncations.

For identically distributed `Xᵢ` the tail probability transfers to `X₀`:

    P(|Xᵢ| > i^{1/p}) = P(|X₀| > i^{1/p}) = P(|X₀|ᵖ > i),

using `IdentDistrib.measure_mem_eq` and the elementary equivalence
`i^{1/p} < |x| ↔ i < |x|ᵖ` (for `i ≥ 0`, `p > 0`).  The resulting sum
`∑ᵢ P(|X₀|ᵖ > i)` is then bounded by the first moment `𝔼|X₀|ᵖ < ∞` via the discrete
layer cake of § TailSum (step 2).  Feeding the finiteness into
`MeasureTheory.ae_eventually_notMem` yields the a.s. eventual truncation
`∀ᵐ ω, ∀ᶠ i, |Xᵢ ω| ≤ i^{1/p}`, the Borel–Cantelli conclusion that step 1 needs. -/

section TruncationReduction

open MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- **Power/root reindexing of a truncation threshold.**  For `0 < p` and `0 ≤ a`,
`0 ≤ b`, the root inequality `a^{1/p} < b` is equivalent to the power inequality
`a < bᵖ`.  Applied to `a = i` and `b = |Xᵢ ω|` this turns the truncation event
`{|Xᵢ| > i^{1/p}}` into the moment event `{|Xᵢ|ᵖ > i}`. -/
theorem rpow_inv_lt_iff_lt_rpow {p : ℝ} (hp : 0 < p) {a b : ℝ} (ha : 0 ≤ a)
    (hb : 0 ≤ b) : a ^ (1 / p) < b ↔ a < b ^ p := by
  have key := Real.rpow_lt_rpow_iff (x := a ^ (1 / p)) (y := b) (z := p)
    (Real.rpow_nonneg ha _) hb hp
  rw [one_div, Real.rpow_inv_rpow ha hp.ne'] at key
  rw [one_div]
  exact key.symm

/-- **Tail-sum finiteness for i.i.d. variables with a finite `p`-th moment.**  If the
`Xᵢ` are identically distributed to `X₀` and `𝔼|X₀|ᵖ < ∞` (encoded as the finite
lintegral `∫⁻ ofReal |X₀|ᵖ`), then the Marcinkiewicz–Zygmund truncation tail sum is
finite:

    ∑ᵢ μ {ω | i^{1/p} < |Xᵢ ω|}  ≠  ∞.

Proof: transfer each tail measure to `X₀` (`IdentDistrib.measure_mem_eq`), reindex the
threshold to the power event `{i < |X₀|ᵖ}` (`rpow_inv_lt_iff_lt_rpow`), split off the
`i = 0` term (bounded by `1` on a probability space), and dominate the rest by the
discrete layer-cake bound `tsum_measure_add_one_ne_top` applied to `Z = |X₀|ᵖ`. -/
theorem tsum_measure_truncation_ne_top_of_identDistrib [IsProbabilityMeasure μ]
    {X : ℕ → Ω → ℝ} {p : ℝ} (hp : 0 < p) (hmeas : ∀ i, Measurable (X i))
    (hident : ∀ i, IdentDistrib (X i) (X 0) μ μ)
    (hmom : ∫⁻ ω, ENNReal.ofReal (|X 0 ω| ^ p) ∂μ ≠ ∞) :
    ∑' i : ℕ, μ {ω | (i : ℝ) ^ (1 / p) < |X i ω|} ≠ ∞ := by
  have hX0 : Measurable (X 0) := hmeas 0
  have hZmeas : Measurable (fun ω => |X 0 ω| ^ p) := by fun_prop
  have hZnn : (0 : Ω → ℝ) ≤ fun ω => |X 0 ω| ^ p :=
    fun ω => Real.rpow_nonneg (abs_nonneg _) p
  -- The threshold set `{y | i^{1/p} < |y|}` is measurable and used to transfer via i.i.d.
  have hthr : ∀ i : ℕ, MeasurableSet {y : ℝ | (i : ℝ) ^ (1 / p) < |y|} := fun i =>
    measurableSet_lt measurable_const _root_.continuous_abs.measurable
  -- Transfer + reindex: each tail measure equals `μ {ω | i < |X₀ ω|ᵖ}`.
  have hstep : ∀ i : ℕ,
      μ {ω | (i : ℝ) ^ (1 / p) < |X i ω|} = μ {ω | (i : ℝ) < |X 0 ω| ^ p} := by
    intro i
    have hpre_i : {ω | (i : ℝ) ^ (1 / p) < |X i ω|}
        = (X i) ⁻¹' {y : ℝ | (i : ℝ) ^ (1 / p) < |y|} := rfl
    have hpre_0 : {ω | (i : ℝ) < |X 0 ω| ^ p}
        = (X 0) ⁻¹' {y : ℝ | (i : ℝ) ^ (1 / p) < |y|} := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_preimage]
      exact (rpow_inv_lt_iff_lt_rpow hp (Nat.cast_nonneg i) (abs_nonneg _)).symm
    rw [hpre_i, hpre_0]
    exact (hident i).measure_mem_eq (hthr i)
  simp_rw [hstep]
  -- Split off the `i = 0` term and dominate the tail by the discrete layer cake.
  -- (`tsum_eq_zero_add'` is the ENNReal-robust peel; the `Summable.tsum_eq_zero_add`
  -- dot form triggers a `whnf` blow-up on the measure-of-set summand.)
  rw [tsum_eq_zero_add' ENNReal.summable]
  refine ENNReal.add_ne_top.mpr ⟨measure_ne_top μ _, ?_⟩
  have hbig : ∑' n : ℕ, μ {x | (n : ℝ) + 1 ≤ |X 0 x| ^ p} ≠ ∞ :=
    tsum_measure_add_one_ne_top hZmeas hZnn hmom
  have hle : ∑' b : ℕ, μ {ω | ((b + 1 : ℕ) : ℝ) < |X 0 ω| ^ p}
      ≤ ∑' n : ℕ, μ {x | (n : ℝ) + 1 ≤ |X 0 x| ^ p} := by
    refine ENNReal.tsum_le_tsum fun b => measure_mono fun ω hω => ?_
    simp only [Set.mem_setOf_eq] at hω ⊢
    push_cast at hω
    linarith
  exact (lt_of_le_of_lt hle hbig.lt_top).ne

/-- **Almost-sure eventual truncation (first Borel–Cantelli, MZ step 1).**  For i.i.d.
`Xᵢ` with a finite `p`-th moment (`𝔼|X₀|ᵖ < ∞`), almost surely `|Xᵢ| ≤ i^{1/p}` holds
for all large `i` — hence the truncation `Yᵢ = Xᵢ·𝟙{|Xᵢ| ≤ i^{1/p}}` agrees with `Xᵢ`
eventually a.s.  This is the Borel–Cantelli output that reduces the Marcinkiewicz–Zygmund
strong law to its truncated version.  Combines the tail-sum finiteness
`tsum_measure_truncation_ne_top_of_identDistrib` with `MeasureTheory.ae_eventually_notMem`. -/
theorem ae_eventually_abs_le_rpow_of_identDistrib [IsProbabilityMeasure μ]
    {X : ℕ → Ω → ℝ} {p : ℝ} (hp : 0 < p) (hmeas : ∀ i, Measurable (X i))
    (hident : ∀ i, IdentDistrib (X i) (X 0) μ μ)
    (hmom : ∫⁻ ω, ENNReal.ofReal (|X 0 ω| ^ p) ∂μ ≠ ∞) :
    ∀ᵐ ω ∂μ, ∀ᶠ i in atTop, |X i ω| ≤ (i : ℝ) ^ (1 / p) := by
  have h := MeasureTheory.ae_eventually_notMem
    (tsum_measure_truncation_ne_top_of_identDistrib hp hmeas hident hmom)
  filter_upwards [h] with ω hω
  filter_upwards [hω] with i hi
  simpa only [Set.mem_setOf_eq, not_lt] using hi

end TruncationReduction

/-! ## S4b (steps 3–4) — the two truncation-moment kernels

With step 1 (the a.s. eventual truncation `|Xᵢ| ≤ i^{1/p}`) in hand, the
Marcinkiewicz–Zygmund proof reduces to two analytic estimates on the truncated
variables `Yᵢ = Xᵢ·𝟙{|Xᵢ| ≤ i^{1/p}}`:

* **step 3 (centering).** `n^{-1/p} ∑_{i<n} 𝔼Yᵢ → 0`.  Since `𝔼X = 0`, one has
  `|𝔼Yᵢ| ≤ 𝔼[|X|·𝟙{|X| > i^{1/p}}]`, and on the tail `{|X| > i^{1/p}}` the bound
  `|x| ≤ i^{(1-p)/p}·|x|^p` turns this into a `Toeplitz`-summable null sequence.
* **step 4 (variance).** `∑ᵢ Var(Yᵢ)/i^{2/p} < ∞`.  On the truncation
  `{|X| ≤ i^{1/p}}` the bound `x² ≤ i^{(2-p)/p}·|x|^p` gives
  `𝔼[Yᵢ²] ≤ i^{(2-p)/p}·𝔼|X|^p`, so the weighted sum is controlled by
  `𝔼|X|^p · ∑ᵢ i^{-2/p}`, convergent precisely because `p < 2` (`2/p > 1`).

Both estimates rest on a single pointwise `rpow` inequality apiece; those two
kernels are supplied here.  They are pure real-analysis facts (no measure theory),
elementary, and reused verbatim by the integral-level estimates of the two steps.
The `1 ≤ p` / `p < 2` hypotheses enter through the sign of the scaling exponent
(`1 - p ≤ 0` makes the tail factor sub-linear; `2 - p ≥ 0` makes the truncation
factor super-linear). -/

section TruncationMomentKernels

/-- **Tail moment kernel (MZ step 3, centering).**  For an exponent `1 ≤ p`, a
threshold `0 < t`, and a point on the tail `t < |x|`, the absolute value is
dominated by the `p`-th power scaled by the sub-linear factor `t^{1-p}`:

    |x| ≤ t^{1-p} · |x|^p.

Applied with `t = i^{1/p}` (so `t^{1-p} = i^{(1-p)/p}`) this is the pointwise
inequality behind the centering estimate
`|𝔼Yᵢ| ≤ 𝔼[|X|·𝟙{|X| > i^{1/p}}] ≤ i^{(1-p)/p}·𝔼|X|^p`, whose right-hand side
is a `tendsto_weighted_average_zero`-summable null sequence.

Proof: split `|x| = |x|^p · |x|^{1-p}` (`rpow_add`), and since `1 - p ≤ 0` and
`0 < t < |x|`, the antitone rpow bound `|x|^{1-p} ≤ t^{1-p}`
(`rpow_le_rpow_of_nonpos`) finishes it. -/
theorem abs_le_rpow_mul_rpow_of_tail {p t x : ℝ} (hp : 1 ≤ p) (ht : 0 < t)
    (hx : t < |x|) : |x| ≤ t ^ (1 - p) * |x| ^ p := by
  have hxpos : 0 < |x| := ht.trans hx
  have hexp : 1 - p ≤ 0 := by linarith
  have hstep : |x| ^ (1 - p) ≤ t ^ (1 - p) :=
    Real.rpow_le_rpow_of_nonpos ht hx.le hexp
  have hsplit : |x| ^ p * |x| ^ (1 - p) = |x| := by
    rw [← Real.rpow_add hxpos, show p + (1 - p) = 1 by ring, Real.rpow_one]
  calc |x| = |x| ^ p * |x| ^ (1 - p) := hsplit.symm
    _ ≤ |x| ^ p * t ^ (1 - p) :=
        mul_le_mul_of_nonneg_left hstep (Real.rpow_nonneg hxpos.le p)
    _ = t ^ (1 - p) * |x| ^ p := by ring

/-- **Truncated second-moment kernel (MZ step 4, variance).**  For an exponent
`p < 2`, a threshold `0 < t`, and a point inside the truncation `|x| ≤ t`, the
square is dominated by the `p`-th power scaled by the super-linear factor `t^{2-p}`:

    x² ≤ t^{2-p} · |x|^p.

Applied with `t = i^{1/p}` (so `t^{2-p} = i^{(2-p)/p}`) this is the pointwise
inequality behind the second-moment estimate `𝔼[Yᵢ²] ≤ i^{(2-p)/p}·𝔼|X|^p`; summed
against `i^{-2/p}` it yields `∑ᵢ Var(Yᵢ)/i^{2/p} ≤ 𝔼|X|^p · ∑ᵢ i^{-2/p} < ∞`, the
convergent series (using `p < 2`, i.e. `2/p > 1`) that Kolmogorov's criterion
consumes.

Proof: the `x = 0` case is nonnegativity of the right-hand side; otherwise split
`x² = |x|^2 = |x|^p · |x|^{2-p}` (`rpow_add`, `sq_abs`), and since `0 ≤ 2 - p` and
`0 < |x| ≤ t`, the monotone rpow bound `|x|^{2-p} ≤ t^{2-p}` (`rpow_le_rpow`)
finishes it. -/
theorem sq_le_rpow_mul_rpow_of_trunc {p t x : ℝ} (hp : p < 2) (ht : 0 < t)
    (hx : |x| ≤ t) : x ^ 2 ≤ t ^ (2 - p) * |x| ^ p := by
  rcases eq_or_ne x 0 with h0 | h0
  · subst h0
    rw [show (0 : ℝ) ^ 2 = 0 by norm_num]
    exact mul_nonneg (Real.rpow_nonneg ht.le _) (Real.rpow_nonneg (abs_nonneg _) _)
  · have hxpos : 0 < |x| := abs_pos.mpr h0
    have hexp : 0 ≤ 2 - p := by linarith
    have hstep : |x| ^ (2 - p) ≤ t ^ (2 - p) := Real.rpow_le_rpow hxpos.le hx hexp
    have hsplit : |x| ^ p * |x| ^ (2 - p) = x ^ 2 := by
      rw [← Real.rpow_add hxpos, show p + (2 - p) = 2 by ring,
        show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, sq_abs]
    calc x ^ 2 = |x| ^ p * |x| ^ (2 - p) := hsplit.symm
      _ ≤ |x| ^ p * t ^ (2 - p) :=
          mul_le_mul_of_nonneg_left hstep (Real.rpow_nonneg hxpos.le p)
      _ = t ^ (2 - p) * |x| ^ p := by ring

end TruncationMomentKernels

/-! ## S4b (steps 3–4) — the integral lifts of the two truncation-moment kernels

The two pointwise `rpow` kernels of the previous section are lifted here to the
integral (expectation) level by monotonicity of the Bochner integral
(`integral_mono_of_nonneg`, which needs integrability only of the dominating
side).  For a measurable `X` whose `p`-th absolute moment `∫ |X|ᵖ` is finite, and a
threshold `t > 0`:

* **step 4 (variance).**  `∫ (𝟙{|X| ≤ t}·X)² ≤ t^{2-p}·∫|X|ᵖ`
  (`integral_trunc_sq_le`, `p < 2`).  With `t = i^{1/p}` this is the truncated
  second-moment estimate `𝔼[Yᵢ²] ≤ i^{(2-p)/p}·𝔼|X|ᵖ`; summed against `i^{-2/p}` it
  gives the finite variance sum Kolmogorov's criterion consumes.
* **step 3 (centering).**  `∫ 𝟙{t < |X|}·|X| ≤ t^{1-p}·∫|X|ᵖ`
  (`integral_tail_abs_le`, `1 ≤ p`).  With `t = i^{1/p}` this bounds the centering
  tail `𝔼[|X|·𝟙{|X| > i^{1/p}}] ≤ i^{(1-p)/p}·𝔼|X|ᵖ`, the null sequence feeding
  `tendsto_weighted_average_zero`.

Both are pure measure theory over an arbitrary measure `μ` — no probability,
independence, or finiteness of `μ` is used (the truncated integrand may itself be
non-integrable when `μ` is infinite, which `integral_mono_of_nonneg` absorbs by
returning `0` for the undefined integral, still `≤` the finite bound). -/

section TruncationIntegralLifts

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- **Truncated second-moment integral lift (MZ step 4, variance).**  Integrating the
pointwise kernel `sq_le_rpow_mul_rpow_of_trunc` over any measure `μ`: for `p < 2`, a
threshold `0 < t`, and `X` with finite `p`-th absolute moment, the truncation
`Y = 𝟙{|X| ≤ t}·X` satisfies

    ∫ Y² ≤ t^{2-p} · ∫ |X|ᵖ.

With `t = i^{1/p}` (so `t^{2-p} = i^{(2-p)/p}`) this is the second-moment estimate
`𝔼[Yᵢ²] ≤ i^{(2-p)/p}·𝔼|X|ᵖ` behind the variance sum `∑ᵢ Var(Yᵢ)/i^{2/p} < ∞`. -/
theorem integral_trunc_sq_le
    (X : Ω → ℝ) {p t : ℝ} (hp : p < 2) (ht : 0 < t)
    (hint : Integrable (fun ω => |X ω| ^ p) μ) :
    ∫ ω, ({ω | |X ω| ≤ t}.indicator X ω) ^ 2 ∂μ
      ≤ t ^ (2 - p) * ∫ ω, |X ω| ^ p ∂μ := by
  have hpt : ∀ ω, ({ω | |X ω| ≤ t}.indicator X ω) ^ 2 ≤ t ^ (2 - p) * |X ω| ^ p := by
    intro ω
    rw [Set.indicator_apply]
    split_ifs with h
    · rw [Set.mem_setOf_eq] at h
      exact sq_le_rpow_mul_rpow_of_trunc hp ht h
    · rw [show ((0 : ℝ)) ^ 2 = 0 by norm_num]
      exact mul_nonneg (Real.rpow_nonneg ht.le _) (Real.rpow_nonneg (abs_nonneg _) _)
  calc ∫ ω, ({ω | |X ω| ≤ t}.indicator X ω) ^ 2 ∂μ
      ≤ ∫ ω, t ^ (2 - p) * |X ω| ^ p ∂μ :=
        integral_mono_of_nonneg
          (ae_of_all _ (fun ω => sq_nonneg _))
          (hint.const_mul _)
          (ae_of_all _ hpt)
    _ = t ^ (2 - p) * ∫ ω, |X ω| ^ p ∂μ := integral_const_mul _ _

/-- **Tail absolute-moment integral lift (MZ step 3, centering).**  Integrating the
pointwise kernel `abs_le_rpow_mul_rpow_of_tail` over any measure `μ`: for `1 ≤ p`, a
threshold `0 < t`, and `X` with finite `p`-th absolute moment,

    ∫ 𝟙{t < |X|}·|X| ≤ t^{1-p} · ∫ |X|ᵖ.

With `t = i^{1/p}` (so `t^{1-p} = i^{(1-p)/p}`) this bounds the centering tail
`𝔼[|X|·𝟙{|X| > i^{1/p}}] ≤ i^{(1-p)/p}·𝔼|X|ᵖ`, the `tendsto_weighted_average_zero`
null sequence. -/
theorem integral_tail_abs_le
    (X : Ω → ℝ) {p t : ℝ} (hp : 1 ≤ p) (ht : 0 < t)
    (hint : Integrable (fun ω => |X ω| ^ p) μ) :
    ∫ ω, {ω | t < |X ω|}.indicator (fun ω => |X ω|) ω ∂μ
      ≤ t ^ (1 - p) * ∫ ω, |X ω| ^ p ∂μ := by
  have hpt : ∀ ω, {ω | t < |X ω|}.indicator (fun ω => |X ω|) ω
      ≤ t ^ (1 - p) * |X ω| ^ p := by
    intro ω
    rw [Set.indicator_apply]
    split_ifs with h
    · rw [Set.mem_setOf_eq] at h
      exact abs_le_rpow_mul_rpow_of_tail hp ht h
    · exact mul_nonneg (Real.rpow_nonneg ht.le _) (Real.rpow_nonneg (abs_nonneg _) _)
  calc ∫ ω, {ω | t < |X ω|}.indicator (fun ω => |X ω|) ω ∂μ
      ≤ ∫ ω, t ^ (1 - p) * |X ω| ^ p ∂μ :=
        integral_mono_of_nonneg
          (ae_of_all _ (fun ω => Set.indicator_nonneg (fun _ _ => abs_nonneg _) ω))
          (hint.const_mul _)
          (ae_of_all _ hpt)
    _ = t ^ (1 - p) * ∫ ω, |X ω| ^ p ∂μ := integral_const_mul _ _

#check @integral_trunc_sq_le
#check @integral_tail_abs_le

-- Axiom audit: foundational axioms only (propext / Classical.choice / Quot.sound);
-- no `sorryAx`, no `Lean.ofReduceBool`, no `decide` / `native_decide`.
#print axioms integral_trunc_sq_le
#print axioms integral_tail_abs_le

end TruncationIntegralLifts

/-! ## Tail bound for the real `p`-series (arithmetic backbone of the MZ variance sum)

The MZ variance sum `∑ᵢ Var(Yᵢ)/i^{2/p}` (`p < 2`, so `s := 2/p > 1`) is finite **not** by
the per-term kernel bound `𝔼[Yᵢ²] ≤ i^{(2-p)/p}·𝔼|X|ᵖ`: dividing that by `aᵢ² = i^{2/p}`
leaves `𝔼|X|ᵖ · i⁻¹`, whose sum **diverges**.  (This corrects the naive per-term plan: the
step-4 kernel `integral_trunc_sq_le` is a valid bound but is *not* summable term-by-term.)
The correct route is a Tonelli interchange of `∑ᵢ` and `𝔼`, keeping the truncated moment
`𝔼[X²·𝟙{|X| ≤ i^{1/p}}]` intact and summing the *weight* `i^{-2/p}` against it; the
deterministic input is then the tail estimate `∑_{j > N} j^{-s} ≤ N^{1-s}/(s-1)` for `s > 1`.

We prove that tail estimate here by integral comparison
(`AntitoneOn.sum_le_integral_Ico` against `∫ x^{-s} = x^{1-s}/(1-s)`, `Analysis/PSeries`
supplies only *summability*, not this quantitative tail); it is the reusable arithmetic
backbone the interchange consumes.  0-sorry / 0-`axiom`. -/
section TailPSeries

open MeasureTheory Set

/-- **Integral-comparison block bound.**  For `1 < s`, `N ≥ 1` and any `K`, the shifted block
`∑_{k < K} (k+N+1)^{-s}` (equivalently `∑_{N < j ≤ N+K} j^{-s}`) is bounded, uniformly in `K`,
by the tail-integral value `N^{1-s}/(s-1)`.  Proof: `x ↦ x^{-s}` is antitone on `(0,∞)`, so the
right-endpoint Riemann sum underestimates `∫_N^{N+K} x^{-s} = (N^{1-s} - (N+K)^{1-s})/(s-1)`,
which is at most `N^{1-s}/(s-1)`. -/
theorem sum_range_shift_rpow_neg_le {s : ℝ} (hs : 1 < s) {N : ℕ} (hN : 1 ≤ N) (K : ℕ) :
    ∑ k ∈ Finset.range K, ((k + N + 1 : ℕ) : ℝ) ^ (-s)
      ≤ (N : ℝ) ^ (1 - s) / (s - 1) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast Nat.lt_of_lt_of_le zero_lt_one hN
  have hle : (N : ℝ) ≤ ((N + K : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_right N K
  -- `x ↦ x^{-s}` is antitone on `[N, N+K] ⊆ (0, ∞)`.
  have hanti : AntitoneOn (fun x : ℝ => x ^ (-s)) (Set.Icc (N : ℝ) ((N + K : ℕ) : ℝ)) :=
    (Real.antitoneOn_rpow_Ioi_of_exponent_nonpos (by linarith : (-s : ℝ) ≤ 0)).mono
      (fun x hx => lt_of_lt_of_le hNpos hx.1)
  -- integral comparison: the `(i+1)`-shifted `Ico` sum ≤ `∫` over `[N, N+K]`.
  have hcomp := AntitoneOn.sum_le_integral_Ico (f := fun x : ℝ => x ^ (-s))
    (Nat.le_add_right N K) hanti
  -- reindex `range K` to the `Ico N (N+K)` shifted sum.
  have hreindex :
      ∑ k ∈ Finset.range K, ((k + N + 1 : ℕ) : ℝ) ^ (-s)
        = ∑ i ∈ Finset.Ico N (N + K), ((i + 1 : ℕ) : ℝ) ^ (-s) := by
    rw [Finset.sum_Ico_eq_sum_range]
    have hKK : N + K - N = K := by omega
    rw [hKK]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    congr 1
    push_cast
    ring
  -- evaluate the tail integral.
  have hne_exp : (-s : ℝ) ≠ -1 := by intro h; linarith
  have hne : (0 : ℝ) ∉ Set.uIcc (N : ℝ) ((N + K : ℕ) : ℝ) := by
    rw [Set.uIcc_of_le hle, Set.mem_Icc]
    rintro ⟨h1, _⟩; linarith
  have hintval : (∫ x in (N : ℝ)..((N + K : ℕ) : ℝ), x ^ (-s))
      = (((N + K : ℕ) : ℝ) ^ (-s + 1) - (N : ℝ) ^ (-s + 1)) / (-s + 1) :=
    integral_rpow (Or.inr ⟨hne_exp, hne⟩)
  -- chain: `range`-sum = `Ico`-sum ≤ `∫` = value ≤ bound.
  rw [hreindex]
  refine hcomp.trans ?_
  dsimp only
  rw [hintval]
  have he : (-s : ℝ) + 1 = 1 - s := by ring
  rw [he]
  set A := (N : ℝ) ^ (1 - s) with hAdef
  set B := ((N + K : ℕ) : ℝ) ^ (1 - s) with hBdef
  have hB : (0 : ℝ) ≤ B := by rw [hBdef]; exact Real.rpow_nonneg (by positivity) _
  have h1s : (1 : ℝ) - s ≠ 0 := by linarith
  have h2s : (s : ℝ) - 1 ≠ 0 := by linarith
  have hs1 : (0 : ℝ) < s - 1 := by linarith
  have key : (B - A) / (1 - s) = (A - B) / (s - 1) := by
    field_simp
    ring
  rw [key]
  exact div_le_div_of_nonneg_right (sub_le_self _ hB) hs1.le

/-- **Tail bound for the real `p`-series.**  For `1 < s` and `N ≥ 1`,
`∑ₖ (k+N+1)^{-s} = ∑_{j > N} j^{-s} ≤ N^{1-s}/(s-1)`, by integral comparison — the
deterministic input to the Tonelli interchange behind the MZ variance sum.  Mathlib's
`Analysis/PSeries` gives only *summability* of the `p`-series (`summable_nat_rpow_inv`),
not this quantitative tail bound. -/
theorem tsum_shift_rpow_neg_le {s : ℝ} (hs : 1 < s) {N : ℕ} (hN : 1 ≤ N) :
    ∑' k : ℕ, ((k + N + 1 : ℕ) : ℝ) ^ (-s) ≤ (N : ℝ) ^ (1 - s) / (s - 1) := by
  refine Real.tsum_le_of_sum_range_le (fun k => Real.rpow_nonneg (by positivity) _) ?_
  intro K
  exact sum_range_shift_rpow_neg_le hs hN K

/-- **Inclusive tail bound for the real `p`-series.**  For `1 < s` and `N ≥ 1`,
`∑_{j ≥ N} j^{-s} = ∑ₖ (k+N)^{-s} ≤ N^{1-s}·s/(s-1)`.  The inclusive-from-`N` companion of
`tsum_shift_rpow_neg_le` (which starts the tail at `N+1`): splitting off the `j = N` term
`N^{-s} ≤ N^{1-s}` and adding the shifted tail `N^{1-s}/(s-1)` combines to the constant
`s/(s-1)`.  This is the shape the Tonelli interchange behind the MZ variance sum consumes after
replacing the real threshold `|X|ᵖ` by `⌈|X|ᵖ⌉` (the inner tail starts at the ceiling, inclusive,
not one past it). -/
theorem tsum_ge_rpow_neg_le {s : ℝ} (hs : 1 < s) {N : ℕ} (hN : 1 ≤ N) :
    ∑' k : ℕ, ((k + N : ℕ) : ℝ) ^ (-s) ≤ (N : ℝ) ^ (1 - s) * s / (s - 1) := by
  have hNR : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hs1 : (0 : ℝ) < s - 1 := by linarith
  refine Real.tsum_le_of_sum_range_le (fun k => Real.rpow_nonneg (by positivity) _) ?_
  intro K
  -- Partial sum ≤ the `j = N` term plus the shifted tail (adding the missing `(K+N)`-th term).
  have hstep : ∑ k ∈ Finset.range K, ((k + N : ℕ) : ℝ) ^ (-s)
      ≤ (N : ℝ) ^ (-s) + ∑ k ∈ Finset.range K, ((k + N + 1 : ℕ) : ℝ) ^ (-s) := by
    have hsub : ∑ k ∈ Finset.range K, ((k + N : ℕ) : ℝ) ^ (-s)
        ≤ ∑ k ∈ Finset.range (K + 1), ((k + N : ℕ) : ℝ) ^ (-s) := by
      rw [Finset.sum_range_succ]
      have : (0 : ℝ) ≤ ((K + N : ℕ) : ℝ) ^ (-s) := Real.rpow_nonneg (by positivity) _
      linarith
    refine hsub.trans (le_of_eq ?_)
    rw [Finset.sum_range_succ', add_comm]
    congr 1
    · norm_num
    · refine Finset.sum_congr rfl (fun k _ => ?_)
      congr 1
      push_cast; ring
  refine hstep.trans ?_
  have htail := sum_range_shift_rpow_neg_le hs hN K
  have hNs : (N : ℝ) ^ (-s) ≤ (N : ℝ) ^ (1 - s) :=
    Real.rpow_le_rpow_of_exponent_le hNR (by linarith)
  have hcomb : (N : ℝ) ^ (1 - s) + (N : ℝ) ^ (1 - s) / (s - 1)
      = (N : ℝ) ^ (1 - s) * s / (s - 1) := by
    field_simp
    ring
  calc (N : ℝ) ^ (-s) + ∑ k ∈ Finset.range K, ((k + N + 1 : ℕ) : ℝ) ^ (-s)
      ≤ (N : ℝ) ^ (1 - s) + (N : ℝ) ^ (1 - s) / (s - 1) := add_le_add hNs htail
    _ = (N : ℝ) ^ (1 - s) * s / (s - 1) := hcomb

/-- **Pointwise inner-tail bound for the MZ variance sum (Tonelli integrand).**  For `1 < s` and
any real `y`, the weighted tail of `i^{-s}` over the truncation region `{i : ℕ | y ≤ i}` is
controlled by a single power of `max 1 y`:

    ∑'_{i : y ≤ i} i^{-s} ≤ (max 1 y)^{1-s} · s/(s-1).

This is the deterministic integrand bound the Tonelli interchange behind the MZ variance sum
consumes.  After swapping `∑ᵢ` and `𝔼`, the inner `∑ᵢ` runs over the truncation region
`{i | |X| ≤ i^{1/p}} = {i | |X|ᵖ ≤ i}`; with `y = |X|ᵖ`, `s = 2/p (> 1)` this bounds it by
`(max 1 |X|ᵖ)^{1-2/p}·s/(s-1)`, whose `|X| ≥ 1` branch is `|X|^{p-2}` — exactly the factor that,
multiplied by `X²`, integrates to `𝔼|X|ᵖ` (the `|X| < 1` branch collapses to the constant
`s/(s-1)`, integrable on a probability space).

Proof: the region is `{i | ⌈y⌉₊ ≤ i}` (`Nat.ceil_le`); reindex the indicator tsum to the
inclusive tail `∑' k, (k+⌈y⌉₊)^{-s}` (`Summable.sum_add_tsum_nat_add`, the head over
`range ⌈y⌉₊` vanishing since the indicator is `0` below the threshold) and apply
`tsum_ge_rpow_neg_le`, then dominate `⌈y⌉₊^{1-s} ≤ (max 1 y)^{1-s}` by antitonicity of `·^{1-s}`
(`1 - s ≤ 0`, `max 1 y ≤ ⌈y⌉₊`).  The `⌈y⌉₊ = 0` (i.e. `y ≤ 0`) branch peels the vanishing
`i = 0` term and reuses the `N = 1` tail. -/
theorem tsum_indicator_ge_rpow_neg_le {s : ℝ} (hs : 1 < s) (y : ℝ) :
    ∑' i : ℕ, {i : ℕ | y ≤ (i : ℝ)}.indicator (fun i => (i : ℝ) ^ (-s)) i
      ≤ (max 1 y) ^ (1 - s) * s / (s - 1) := by
  have hs1 : (0 : ℝ) < s - 1 := by linarith
  have hexp : (1 : ℝ) - s ≤ 0 := by linarith
  have hf_summ : Summable (fun i : ℕ => (i : ℝ) ^ (-s)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  set N : ℕ := ⌈y⌉₊ with hN
  -- rewrite the truncation region `{i | y ≤ i}` as `{i | N ≤ i}`
  have hset : {i : ℕ | y ≤ (i : ℝ)} = {i : ℕ | N ≤ i} := by
    ext i; simp only [Set.mem_setOf_eq]; rw [hN]; exact Nat.ceil_le.symm
  rw [hset]
  -- reindex the indicator tsum to the inclusive tail `∑' k, (k + N)^{-s}`
  have hind_summ : Summable ({i : ℕ | N ≤ i}.indicator (fun i : ℕ => (i : ℝ) ^ (-s))) :=
    hf_summ.indicator _
  have hhead : ∑ i ∈ Finset.range N,
      {i : ℕ | N ≤ i}.indicator (fun i : ℕ => (i : ℝ) ^ (-s)) i = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    rw [Finset.mem_range] at hi
    exact Set.indicator_of_notMem (by simp only [Set.mem_setOf_eq]; omega) _
  have hshift := hind_summ.sum_add_tsum_nat_add N
  rw [hhead, zero_add] at hshift
  have hreidx : (∑' i, {i : ℕ | N ≤ i}.indicator (fun i : ℕ => (i : ℝ) ^ (-s)) (i + N))
      = ∑' i : ℕ, ((i + N : ℕ) : ℝ) ^ (-s) := by
    refine tsum_congr (fun i => ?_)
    rw [Set.indicator_of_mem (by simp only [Set.mem_setOf_eq]; omega)]
  rw [hreidx] at hshift
  rw [← hshift]
  rcases Nat.eq_zero_or_pos N with hN0 | hNpos
  · -- `N = 0` : `y ≤ 0`, so `max 1 y = 1` and the bound is `s/(s-1)`
    have hy0 : y ≤ 0 := Nat.ceil_eq_zero.mp (hN.symm.trans hN0)
    have hmax : max 1 y = 1 := max_eq_left (by linarith)
    rw [hmax, Real.one_rpow, one_mul, hN0]
    have hz0 : ((0 : ℕ) : ℝ) ^ (-s) = 0 := by
      rw [Nat.cast_zero, Real.zero_rpow (by linarith : -s ≠ 0)]
    calc ∑' i : ℕ, ((i + 0 : ℕ) : ℝ) ^ (-s)
        = ∑' i : ℕ, (i : ℝ) ^ (-s) := by norm_num
      _ = ((0 : ℕ) : ℝ) ^ (-s) + ∑' k : ℕ, ((k + 1 : ℕ) : ℝ) ^ (-s) := hf_summ.tsum_eq_zero_add
      _ = ∑' k : ℕ, ((k + 1 : ℕ) : ℝ) ^ (-s) := by rw [hz0, zero_add]
      _ ≤ s / (s - 1) := by
          have h := tsum_ge_rpow_neg_le hs (le_refl 1)
          rwa [Nat.cast_one, Real.one_rpow, one_mul] at h
  · -- `N ≥ 1`
    refine (tsum_ge_rpow_neg_le hs hNpos).trans ?_
    have hx : (0 : ℝ) < max 1 y := lt_of_lt_of_le zero_lt_one (le_max_left 1 y)
    have hxy : max 1 y ≤ (N : ℝ) :=
      max_le (by exact_mod_cast hNpos) (by rw [hN]; exact Nat.le_ceil y)
    have hpow : (N : ℝ) ^ (1 - s) ≤ (max 1 y) ^ (1 - s) :=
      Real.rpow_le_rpow_of_nonpos hx hxy hexp
    have hfac : (0 : ℝ) ≤ s / (s - 1) := div_nonneg (by linarith) (by linarith)
    calc (N : ℝ) ^ (1 - s) * s / (s - 1)
        = (N : ℝ) ^ (1 - s) * (s / (s - 1)) := by ring
      _ ≤ (max 1 y) ^ (1 - s) * (s / (s - 1)) := mul_le_mul_of_nonneg_right hpow hfac
      _ = (max 1 y) ^ (1 - s) * s / (s - 1) := by ring

/-- **Pointwise Tonelli integrand for the MZ variance sum.**  For `1 < s`, `0 < p` and any
real `x`, the `i^{-s}`-weighted truncated-square sum over the *root-form* truncation region
`{i | |x| ≤ i^{1/p}}` — exactly `∑ᵢ i^{-s}·(𝟙{|x| ≤ i^{1/p}}·x)²`, the per-`ω` summand of
the variance series after `t = i^{1/p}` — is bounded by a single power of `max 1 |x|ᵖ`:

    ∑'_i 𝟙{|x| ≤ i^{1/p}}·(i^{-s}·x²)  ≤  (max 1 |x|ᵖ)^{1-s}·s/(s-1) · x².

This is the deterministic integrand the Tonelli interchange behind `∑ᵢ Var(Yᵢ)/i^{2/p}`
consumes: with `s = 2/p (> 1 ⟺ p < 2)` the `|x| ≥ 1` branch of the bound is `x²·|x|^{p-2} =
|x|ᵖ`, integrating to `𝔼|X|ᵖ`; the `|x| < 1` branch collapses to `x²·s/(s-1)`, integrable on a
probability space.

Proof: pull `x²` out of the indicator (`Set.indicator_apply` + `ring`) and out of the tsum
(`tsum_mul_right`); rewrite the root-form region `{i | |x| ≤ i^{1/p}}` to the power-form region
`{i | |x|ᵖ ≤ i}` (complement of `rpow_inv_lt_iff_lt_rpow` via `not_lt`); then apply the
deterministic tail bound `tsum_indicator_ge_rpow_neg_le` at `y = |x|ᵖ` and multiply through by
`x² ≥ 0`. -/
theorem tsum_weight_trunc_sq_le {s p : ℝ} (hs : 1 < s) (hp : 0 < p) (x : ℝ) :
    ∑' i : ℕ, {i : ℕ | |x| ≤ (i : ℝ) ^ (1 / p)}.indicator
        (fun i => (i : ℝ) ^ (-s) * x ^ 2) i
      ≤ (max 1 (|x| ^ p)) ^ (1 - s) * s / (s - 1) * x ^ 2 := by
  set S : Set ℕ := {i : ℕ | |x| ≤ (i : ℝ) ^ (1 / p)} with hS
  -- pull `x²` out of the indicator, then out of the tsum
  have hpt : ∀ i : ℕ,
      S.indicator (fun i => (i : ℝ) ^ (-s) * x ^ 2) i
        = S.indicator (fun i => (i : ℝ) ^ (-s)) i * x ^ 2 := by
    intro i; simp only [Set.indicator_apply]; split_ifs <;> ring
  rw [tsum_congr hpt, tsum_mul_right]
  -- rewrite the root-form region `{i | |x| ≤ i^{1/p}}` to the power-form `{i | |x|ᵖ ≤ i}`
  have hSeq : S = {i : ℕ | |x| ^ p ≤ (i : ℝ)} := by
    rw [hS]; ext i
    simp only [Set.mem_setOf_eq]
    rw [← not_lt, ← not_lt]
    exact not_congr (rpow_inv_lt_iff_lt_rpow hp (Nat.cast_nonneg i) (abs_nonneg x))
  rw [hSeq]
  exact mul_le_mul_of_nonneg_right (tsum_indicator_ge_rpow_neg_le hs (|x| ^ p)) (sq_nonneg x)

/-- **The variance-integrand weight is dominated by an integrable function.**
For `0 < p < 2` and any real `x`, the pointwise weight produced by
`tsum_weight_trunc_sq_le` at `s = 2/p` — namely `(max 1 |x|ᵖ)^{1 - 2/p} · x²` — is
bounded by `|x|ᵖ + 1`:

    (max 1 |x|ᵖ)^{1 - 2/p} · x²  ≤  |x|ᵖ + 1.

On `|x| ≥ 1` the maximum is `|x|ᵖ` and the exponent arithmetic collapses the product
to `|x|ᵖ` **exactly**: `|x|^{p(1 - 2/p)} · x² = |x|^{p - 2} · |x|² = |x|^{(p-2)+2} = |x|ᵖ`
(this is the sole place `s = 2/p` is used — `p·(1 - 2/p) + 2 = p`). On `|x| < 1` the
maximum is `1`, so the left side is just `x² ≤ 1 ≤ |x|ᵖ + 1`.

Since `|x|ᵖ + 1` integrates to `𝔼|X|ᵖ + 1 < ∞` on a probability space, this is the
integrable dominating function the Tonelli interchange behind `∑ᵢ Var(Yᵢ)/i^{2/p}`
consumes; see `variance_integrand_le_moment`. -/
theorem weight_bound_le_moment_add_one {p : ℝ} (hp0 : 0 < p) (hp2 : p < 2) (x : ℝ) :
    (max 1 (|x| ^ p)) ^ (1 - 2 / p) * x ^ 2 ≤ |x| ^ p + 1 := by
  have hpne : p ≠ 0 := ne_of_gt hp0
  have hax : (0 : ℝ) ≤ |x| := abs_nonneg x
  rcases le_or_lt 1 |x| with hx1 | hx1
  · -- `|x| ≥ 1`: `max = |x|ᵖ`, and the left side collapses to `|x|ᵖ` exactly
    have hpos : (0 : ℝ) < |x| := lt_of_lt_of_le one_pos hx1
    have hxp1 : (1 : ℝ) ≤ |x| ^ p := by
      rw [← Real.one_rpow p]; exact Real.rpow_le_rpow (by norm_num) hx1 (le_of_lt hp0)
    rw [max_eq_right hxp1]
    have hexp : (|x| ^ p) ^ (1 - 2 / p) = |x| ^ (p - 2) := by
      rw [← Real.rpow_mul hax]; congr 1; field_simp
    have hx2 : x ^ 2 = |x| ^ (2 : ℝ) := by
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, sq_abs]
    rw [hexp, hx2, ← Real.rpow_add hpos, show p - 2 + 2 = p by ring]
    linarith
  · -- `|x| < 1`: `max = 1`, so the left side is `x² ≤ 1 ≤ |x|ᵖ + 1`
    have hxp1 : |x| ^ p ≤ 1 := Real.rpow_le_one hax (le_of_lt hx1) (le_of_lt hp0)
    rw [max_eq_left hxp1, Real.one_rpow, one_mul]
    have hx2le : x ^ 2 ≤ 1 := by nlinarith [sq_abs x, abs_nonneg x, hx1]
    have hxpnn : (0 : ℝ) ≤ |x| ^ p := Real.rpow_nonneg hax p
    linarith

/-- **Pointwise variance-sum integrand ≤ an integrable dominating function.**  For
`0 < p < 2` and any real `x`, the `i^{-2/p}`-weighted truncated-square sum over the
root-form region `{i | |x| ≤ i^{1/p}}` — exactly `∑ᵢ i^{-2/p}·(𝟙{|x| ≤ i^{1/p}}·x)²`,
the per-`ω` summand of `∑ᵢ Var(Yᵢ)/i^{2/p}` at `x = X(ω)` — is bounded by a fixed
constant times `|x|ᵖ + 1`:

    ∑'_i 𝟙{|x| ≤ i^{1/p}}·(i^{-2/p}·x²)  ≤  (2/p)/(2/p − 1) · (|x|ᵖ + 1).

This composes the deterministic tail bound `tsum_weight_trunc_sq_le` (at `s = 2/p`)
with `weight_bound_le_moment_add_one`.  The right side is integrable on a probability
space (it integrates to `(2/p)/(2/p−1)·(𝔼|X|ᵖ + 1)`), so this is the dominating
function `MeasureTheory.integral_tsum`/`lintegral_tsum` needs to justify the
`∑'ᵢ`–`∫` interchange and then bound the variance sum by `C·𝔼|X|ᵖ`. -/
theorem variance_integrand_le_moment {p : ℝ} (hp0 : 0 < p) (hp2 : p < 2) (x : ℝ) :
    ∑' i : ℕ, {i : ℕ | |x| ≤ (i : ℝ) ^ (1 / p)}.indicator
        (fun i => (i : ℝ) ^ (-(2 / p)) * x ^ 2) i
      ≤ 2 / p / (2 / p - 1) * (|x| ^ p + 1) := by
  have hs : (1 : ℝ) < 2 / p := (one_lt_div hp0).mpr hp2
  have hCnn : (0 : ℝ) ≤ 2 / p / (2 / p - 1) := div_nonneg (by positivity) (by linarith)
  calc ∑' i : ℕ, {i : ℕ | |x| ≤ (i : ℝ) ^ (1 / p)}.indicator
          (fun i => (i : ℝ) ^ (-(2 / p)) * x ^ 2) i
      ≤ (max 1 (|x| ^ p)) ^ (1 - 2 / p) * (2 / p) / (2 / p - 1) * x ^ 2 :=
        tsum_weight_trunc_sq_le hs hp0 x
    _ = 2 / p / (2 / p - 1) * ((max 1 (|x| ^ p)) ^ (1 - 2 / p) * x ^ 2) := by ring
    _ ≤ 2 / p / (2 / p - 1) * (|x| ^ p + 1) :=
        mul_le_mul_of_nonneg_left (weight_bound_le_moment_add_one hp0 hp2 x) hCnn

#check @sum_range_shift_rpow_neg_le
#check @tsum_shift_rpow_neg_le
#check @tsum_ge_rpow_neg_le
#check @tsum_indicator_ge_rpow_neg_le
#check @tsum_weight_trunc_sq_le
#check @weight_bound_le_moment_add_one
#check @variance_integrand_le_moment

-- Axiom audit: foundational axioms only (propext / Classical.choice / Quot.sound);
-- no `sorryAx`, no `Lean.ofReduceBool`, no `decide` / `native_decide`.
#print axioms sum_range_shift_rpow_neg_le
#print axioms tsum_shift_rpow_neg_le
#print axioms tsum_ge_rpow_neg_le
#print axioms tsum_indicator_ge_rpow_neg_le
#print axioms tsum_weight_trunc_sq_le
#print axioms weight_bound_le_moment_add_one
#print axioms variance_integrand_le_moment

end TailPSeries

/-! ## Tonelli interchange for the MZ variance sum (measure-theoretic lift of step 4)

The variance series `∑ᵢ Var(Yᵢ)/aᵢ^{2}` with `aᵢ = i^{1/p}` and truncations
`Yᵢ = 𝟙{|X| ≤ i^{1/p}}·X` is finite **not** term-by-term (that diverges — see the
`TailPSeries` note) but by a **Tonelli interchange** of `∑ᵢ` and `∫`.  For nonnegative
integrands the interchange is *unconditional*: `MeasureTheory.lintegral_tsum` pushes `∑'ᵢ`
through the lower integral needing only a per-term measurability side goal, sidestepping the
Bochner `integral_tsum` whose `∑'ᵢ ∫‖·‖ < ∞` hypothesis is *exactly* the finiteness we are
trying to establish.  The pointwise integrand is then dominated by the deterministic bound
`tsum_weight_trunc_sq_le` at `x = X ω`.

This yields the master estimate (in `ℝ≥0∞`, `s = 2/p`)

    ∑'ᵢ ∫⁻ i^{-s}·(𝟙{|X|≤i^{1/p}}·X)²  ≤  ∫⁻ (max 1 |X|ᵖ)^{1-s}·s/(s-1)·X²,

the lower-integral form of `∑ᵢ 𝔼[Yᵢ²]·i^{-2/p} ≤ 𝔼[(max 1 |X|ᵖ)^{1-2/p}·(2/p)/(2/p-1)·X²]`.
With `s = 2/p > 1` the RHS integrand is dominated by `s/(s-1)·max(X², |X|ᵖ)`, integrable on a
probability space with `𝔼|X|ᵖ < ∞`; so the whole variance sum is finite (that finiteness
extraction is the next leaf).  0-sorry / 0-`axiom`. -/
section TonelliInterchange

open MeasureTheory
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- **Tonelli interchange bound for the MZ variance series.**  For a measurable `X`, `1 < s`
and `0 < p`, the `i^{-s}`-weighted truncated second moments, summed in `ℝ≥0∞`, are bounded by
the integral of the deterministic pointwise majorant of `tsum_weight_trunc_sq_le`:

    ∑'ᵢ ∫⁻ ω, i^{-s}·(𝟙{|X|≤i^{1/p}}·X)²  ≤  ∫⁻ ω, (max 1 |X|ᵖ)^{1-s}·s/(s-1)·X².

Proof: `lintegral_tsum` (nonneg summand, per-term measurable) pushes `∑'ᵢ` inside the lower
integral; then `lintegral_mono` dominates the pointwise `∑'ᵢ` by `tsum_weight_trunc_sq_le` at
`x = X ω`, pulling `ENNReal.ofReal` through the real tsum via `ENNReal.ofReal_tsum_of_nonneg`
(the per-`ω` summand is summable: an indicator of the `p`-series `i^{-s}` scaled by `X ω ^ 2`). -/
theorem lintegral_tsum_trunc_sq_weight_le
    (X : Ω → ℝ) (hX : Measurable X) {s p : ℝ} (hs : 1 < s) (hp : 0 < p) :
    ∑' i : ℕ, ∫⁻ ω, ENNReal.ofReal
        ((i : ℝ) ^ (-s) * ({ω | |X ω| ≤ (i : ℝ) ^ (1 / p)}.indicator X ω) ^ 2) ∂μ
      ≤ ∫⁻ ω, ENNReal.ofReal
        ((max 1 (|X ω| ^ p)) ^ (1 - s) * s / (s - 1) * (X ω) ^ 2) ∂μ := by
  -- per-term measurability of `ω ↦ ofReal (i^{-s}·(𝟙{|X|≤i^{1/p}}·X)²)`
  have hmeas : ∀ i : ℕ, AEMeasurable
      (fun ω => ENNReal.ofReal
        ((i : ℝ) ^ (-s) * ({ω | |X ω| ≤ (i : ℝ) ^ (1 / p)}.indicator X ω) ^ 2)) μ := by
    intro i
    refine (ENNReal.measurable_ofReal.comp ?_).aemeasurable
    exact ((hX.indicator (measurableSet_le hX.abs measurable_const)).pow_const 2).const_mul _
  -- push `∑'ᵢ` inside the lower integral (unconditional for nonneg summands)
  rw [← lintegral_tsum hmeas]
  -- dominate pointwise by `tsum_weight_trunc_sq_le` at `x = X ω`
  apply lintegral_mono
  intro ω
  -- the real summand equals the root-form indicator summand of `tsum_weight_trunc_sq_le`
  have hri : ∀ i : ℕ,
      (i : ℝ) ^ (-s) * ({ω | |X ω| ≤ (i : ℝ) ^ (1 / p)}.indicator X ω) ^ 2
        = {j : ℕ | |X ω| ≤ (j : ℝ) ^ (1 / p)}.indicator
            (fun j => (j : ℝ) ^ (-s) * (X ω) ^ 2) i := by
    intro i
    simp only [Set.indicator_apply, Set.mem_setOf_eq]
    split_ifs <;> ring
  have hr_nonneg : ∀ i : ℕ,
      0 ≤ (i : ℝ) ^ (-s) * ({ω | |X ω| ≤ (i : ℝ) ^ (1 / p)}.indicator X ω) ^ 2 :=
    fun i => mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg i) _) (sq_nonneg _)
  have hclean_summ : Summable
      ({j : ℕ | |X ω| ≤ (j : ℝ) ^ (1 / p)}.indicator
        (fun j => (j : ℝ) ^ (-s) * (X ω) ^ 2)) :=
    ((Real.summable_nat_rpow.mpr (by linarith : -s < -1)).mul_right ((X ω) ^ 2)).indicator _
  have hr_summ : Summable
      (fun i : ℕ => (i : ℝ) ^ (-s) * ({ω | |X ω| ≤ (i : ℝ) ^ (1 / p)}.indicator X ω) ^ 2) :=
    hclean_summ.congr (fun i => (hri i).symm)
  calc ∑' i : ℕ, ENNReal.ofReal
          ((i : ℝ) ^ (-s) * ({ω | |X ω| ≤ (i : ℝ) ^ (1 / p)}.indicator X ω) ^ 2)
      = ENNReal.ofReal (∑' i : ℕ,
          (i : ℝ) ^ (-s) * ({ω | |X ω| ≤ (i : ℝ) ^ (1 / p)}.indicator X ω) ^ 2) :=
        (ENNReal.ofReal_tsum_of_nonneg hr_nonneg hr_summ).symm
    _ ≤ ENNReal.ofReal ((max 1 (|X ω| ^ p)) ^ (1 - s) * s / (s - 1) * (X ω) ^ 2) := by
        apply ENNReal.ofReal_le_ofReal
        calc ∑' i : ℕ,
              (i : ℝ) ^ (-s) * ({ω | |X ω| ≤ (i : ℝ) ^ (1 / p)}.indicator X ω) ^ 2
            = ∑' i : ℕ, {j : ℕ | |X ω| ≤ (j : ℝ) ^ (1 / p)}.indicator
                (fun j => (j : ℝ) ^ (-s) * (X ω) ^ 2) i := tsum_congr hri
          _ ≤ (max 1 (|X ω| ^ p)) ^ (1 - s) * s / (s - 1) * (X ω) ^ 2 :=
              tsum_weight_trunc_sq_le hs hp (X ω)

#check @lintegral_tsum_trunc_sq_weight_le

-- Axiom audit: foundational axioms only (propext / Classical.choice / Quot.sound);
-- no `sorryAx`, no `Lean.ofReduceBool`, no `decide` / `native_decide`.
#print axioms lintegral_tsum_trunc_sq_weight_le

end TonelliInterchange

/-! ## Pointwise domination of the interchange RHS integrand (MZ step-4 finiteness core)

The Tonelli interchange `lintegral_tsum_trunc_sq_weight_le` bounds the variance sum by
`∫⁻ (max 1 |X|ᵖ)^{1-s}·s/(s-1)·X²` with `s = 2/p`.  At *exactly* that exponent the integrand
core `(max 1 |X|ᵖ)^{1-2/p}·X²` is dominated **pointwise** by `|X|ᵖ`, which makes the RHS
integral finite whenever `𝔼|X|ᵖ < ∞`.  The two regions both land under `|x|ᵖ`:

* `|x| ≥ 1`: `max = |x|ᵖ`, and `(|x|ᵖ)^{1-2/p}·|x|² = |x|^{(p-2)+2} = |x|ᵖ` (equality);
* `|x| < 1`: `max = 1`, so the core is `x² = |x|² = |x|ᵖ·|x|^{2-p} ≤ |x|ᵖ` (`|x|^{2-p} ≤ 1`
  since `0 ≤ 2-p` and `|x| ≤ 1`).

0-sorry / 0-`axiom`. -/
section VarianceMajorant

/-- **RHS-integrand domination (MZ step-4 finiteness core).**  For `0 < p < 2` and any real
`x`, the interchange integrand core at `s = 2/p` is dominated by `|x|ᵖ`:

    (max 1 |x|ᵖ)^{1 - 2/p} · x²  ≤  |x|ᵖ.

Multiplying by the nonnegative constant `s/(s-1)` (`s = 2/p`) dominates the full interchange
RHS integrand by `s/(s-1)·|X|ᵖ`, giving `∫⁻ (…) < ∞` from `𝔼|X|ᵖ < ∞` — the next leaf. -/
theorem trunc_rpow_weight_sq_le_rpow {p x : ℝ} (hp : 0 < p) (hp2 : p < 2) :
    (max 1 (|x| ^ p)) ^ (1 - 2 / p) * x ^ 2 ≤ |x| ^ p := by
  have hx2 : x ^ 2 = |x| ^ (2 : ℝ) := by
    rw [← sq_abs x, ← Real.rpow_natCast (|x|) 2]; norm_num
  rcases le_or_gt (|x|) 1 with hle | hgt
  · -- |x| ≤ 1 : max = 1, split |x|² = |x|ᵖ·|x|^{2-p} with |x|^{2-p} ≤ 1
    have hap : |x| ^ p ≤ 1 := Real.rpow_le_one (abs_nonneg x) hle hp.le
    rw [max_eq_left hap, Real.one_rpow, one_mul, hx2]
    have hsplit : |x| ^ (2 : ℝ) = |x| ^ p * |x| ^ (2 - p) := by
      rw [← Real.rpow_add_of_nonneg (abs_nonneg x) hp.le (by linarith),
          show p + (2 - p) = (2 : ℝ) from by ring]
    rw [hsplit]
    have h1 : |x| ^ (2 - p) ≤ 1 := Real.rpow_le_one (abs_nonneg x) hle (by linarith)
    calc |x| ^ p * |x| ^ (2 - p)
        ≤ |x| ^ p * 1 := mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg (abs_nonneg x) p)
      _ = |x| ^ p := mul_one _
  · -- 1 < |x| : max = |x|ᵖ, exact equality
    have hxpos : (0 : ℝ) < |x| := lt_trans one_pos hgt
    have hap : 1 ≤ |x| ^ p := by
      calc (1 : ℝ) = (1 : ℝ) ^ p := (Real.one_rpow p).symm
        _ ≤ |x| ^ p := Real.rpow_le_rpow zero_le_one hgt.le hp.le
    have hexp : p * (1 - 2 / p) + 2 = p := by field_simp; ring
    have hval : (max 1 (|x| ^ p)) ^ (1 - 2 / p) * x ^ 2 = |x| ^ p := by
      rw [max_eq_right hap, hx2, ← Real.rpow_mul (abs_nonneg x), ← Real.rpow_add hxpos, hexp]
    exact le_of_eq hval

#check @trunc_rpow_weight_sq_le_rpow

-- Axiom audit: foundational axioms only (propext / Classical.choice / Quot.sound);
-- no `sorryAx`, no `Lean.ofReduceBool`, no `decide` / `native_decide`.
#print axioms trunc_rpow_weight_sq_le_rpow

end VarianceMajorant

/-! ## Master finiteness bound for the MZ variance sum (interchange ∘ domination)

Chaining the Tonelli interchange `lintegral_tsum_trunc_sq_weight_le` (at `s = 2/p`) with the
pointwise domination `trunc_rpow_weight_sq_le_rpow` and a constant pull-out collapses the whole
`i^{-2/p}`-weighted truncated-second-moment sum to a single multiple of the `p`-th moment:

    ∑'ᵢ ∫⁻ ω, i^{-2/p}·(𝟙{|X|≤i^{1/p}}·X)²  ≤  ofReal((2/p)/(2/p-1)) · ∫⁻ ω, |X|ᵖ.

This is the quantitative `∑ᵢ Var(Yᵢ)/aᵢ² ≤ C·𝔼|X|ᵖ` (in `ℝ≥0∞`, `aᵢ = i^{1/p}`): with
`𝔼|X|ᵖ < ∞` the RHS is finite, so the variance sum is finite — the summability hypothesis of the
Kolmogorov criterion `ae_tendsto_average_zero_of_variance_weighted_bdd` (S5).  0-sorry / 0-`axiom`. -/
section MasterVarianceBound

open MeasureTheory
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- **Master variance-sum bound (MZ step 4).**  For a measurable `X` and `0 < p < 2`, the
`i^{-2/p}`-weighted truncated second moments sum to at most a constant multiple of the `p`-th
absolute moment (all in `ℝ≥0∞`):

    ∑'ᵢ ∫⁻ ω, i^{-2/p}·(𝟙{|X|≤i^{1/p}}·X)²  ≤  ofReal((2/p)/(2/p-1)) · ∫⁻ ω, |X|ᵖ.

Proof: `lintegral_tsum_trunc_sq_weight_le` at `s = 2/p` bounds the LHS by the integral of the
interchange majorant; `lintegral_const_mul'` pulls the constant out of the target; then
`lintegral_mono` + `trunc_rpow_weight_sq_le_rpow` dominate the integrand pointwise by
`(2/p)/(2/p-1)·|X ω|ᵖ`. -/
theorem lintegral_tsum_trunc_sq_weight_le_moment
    (X : Ω → ℝ) (hX : Measurable X) {p : ℝ} (hp : 0 < p) (hp2 : p < 2) :
    ∑' i : ℕ, ∫⁻ ω, ENNReal.ofReal
        ((i : ℝ) ^ (-(2 / p)) * ({ω | |X ω| ≤ (i : ℝ) ^ (1 / p)}.indicator X ω) ^ 2) ∂μ
      ≤ ENNReal.ofReal ((2 / p) / (2 / p - 1)) * ∫⁻ ω, ENNReal.ofReal (|X ω| ^ p) ∂μ := by
  have hs : (1 : ℝ) < 2 / p := by rw [lt_div_iff₀ hp]; linarith
  have hc : (0 : ℝ) ≤ (2 / p) / (2 / p - 1) := div_nonneg (by positivity) (by linarith)
  refine (lintegral_tsum_trunc_sq_weight_le X hX hs hp).trans ?_
  rw [← lintegral_const_mul' (ENNReal.ofReal ((2 / p) / (2 / p - 1)))
        (fun ω => ENNReal.ofReal (|X ω| ^ p)) ENNReal.ofReal_ne_top]
  apply lintegral_mono
  intro ω
  dsimp only
  rw [← ENNReal.ofReal_mul hc]
  apply ENNReal.ofReal_le_ofReal
  calc (max 1 (|X ω| ^ p)) ^ (1 - 2 / p) * (2 / p) / (2 / p - 1) * (X ω) ^ 2
      = (2 / p) / (2 / p - 1) * ((max 1 (|X ω| ^ p)) ^ (1 - 2 / p) * (X ω) ^ 2) := by ring
    _ ≤ (2 / p) / (2 / p - 1) * |X ω| ^ p :=
        mul_le_mul_of_nonneg_left (trunc_rpow_weight_sq_le_rpow hp hp2) hc

#check @lintegral_tsum_trunc_sq_weight_le_moment

/-- **Finiteness of the MZ variance sum (ℝ≥0∞).**  For a measurable `X` with finite `p`-th
absolute moment (`Integrable |X|ᵖ`) and `0 < p < 2`, the `i^{-2/p}`-weighted sum of the truncated
second moments is finite:

    ∑'ᵢ ∫⁻ ω, i^{-2/p}·(𝟙{|X|≤i^{1/p}}·X)²  < ∞.

Proof: bound by the master estimate `lintegral_tsum_trunc_sq_weight_le_moment`
`= ofReal(C)·∫⁻ ω, |X ω|ᵖ`; the constant factor is `< ∞` (`ENNReal.ofReal_lt_top`) and the moment
factor is `< ∞` because `Integrable (fun ω => |X ω|ᵖ)` transfers, via
`hasFiniteIntegral_iff_ofReal` on the nonnegative integrand `|X|ᵖ`, to
`∫⁻ ω, ofReal(|X ω|ᵖ) < ∞`; then `ENNReal.mul_lt_top`.

This is exactly the summability hypothesis of the Kolmogorov weighted criterion
`ae_tendsto_average_zero_of_variance_weighted_bdd` (S5) applied to the centered truncations
`Yᵢ − 𝔼Yᵢ` (`aᵢ = i^{1/p}`), the final analytic input to the Marcinkiewicz–Zygmund SLLN. -/
theorem tsum_lintegral_trunc_sq_weight_lt_top
    (X : Ω → ℝ) (hX : Measurable X) {p : ℝ} (hp : 0 < p) (hp2 : p < 2)
    (hint : Integrable (fun ω => |X ω| ^ p) μ) :
    ∑' i : ℕ, ∫⁻ ω, ENNReal.ofReal
        ((i : ℝ) ^ (-(2 / p)) * ({ω | |X ω| ≤ (i : ℝ) ^ (1 / p)}.indicator X ω) ^ 2) ∂μ
      < ∞ := by
  refine (lintegral_tsum_trunc_sq_weight_le_moment X hX hp hp2).trans_lt ?_
  apply ENNReal.mul_lt_top ENNReal.ofReal_lt_top
  -- `∫⁻ ω, ofReal(|X ω|ᵖ) < ∞` from `Integrable (fun ω => |X ω|ᵖ)` via the nonneg iff.
  have hnn : (0 : Ω → ℝ) ≤ᵐ[μ] fun ω => |X ω| ^ p :=
    ae_of_all _ (fun ω => Real.rpow_nonneg (abs_nonneg _) _)
  exact (hasFiniteIntegral_iff_ofReal hnn).mp hint.hasFiniteIntegral

#check @tsum_lintegral_trunc_sq_weight_lt_top

-- Axiom audit: foundational axioms only (propext / Classical.choice / Quot.sound);
-- no `sorryAx`, no `Lean.ofReduceBool`, no `decide` / `native_decide`.
#print axioms lintegral_tsum_trunc_sq_weight_le_moment
#print axioms tsum_lintegral_trunc_sq_weight_lt_top

end MasterVarianceBound

end LawsOfLargeNumbers.MZ
