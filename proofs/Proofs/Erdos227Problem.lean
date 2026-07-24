/-
  Erdős Problem #227: Maximum Term vs Maximum Modulus

  Source: https://erdosproblems.com/227
  Status: SOLVED (DISPROVED)

  Statement:
  Let f = Σ aₙzⁿ be an entire function which is not a polynomial. Is it true that if
    lim(r→∞) max_n|aₙrⁿ| / max_{|z|=r}|f(z)|
  exists, then it must be 0?

  Answer: NO. Clunie-Hayman (1964) showed the limit can take any value in [0, 1/2].

  Known Results:
  - Clunie (unpublished): True for functions with all aₙ ≥ 0
  - Clunie-Hayman (1964): Disproved in general — limit can be any λ ∈ [0, 1/2]

  Related: Erdős #513

  Tags: complex-analysis, entire-functions, power-series
-/

import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Order.Filter.Basic

namespace Erdos227

open Complex Filter Topology FormalMultilinearSeries

/-
## Part 1: Basic Definitions

Maximum term and maximum modulus for power series.
-/

/-- An entire function represented by its power series coefficients -/
structure EntireFunction where
  coeff : ℕ → ℂ
  not_polynomial : ∀ N : ℕ, ∃ n > N, coeff n ≠ 0

/-- The maximum term μ(r) = max_n |aₙ|rⁿ -/
noncomputable def maxTerm (f : EntireFunction) (r : ℝ) : ℝ :=
  ⨆ n : ℕ, ‖f.coeff n‖ * r ^ n

/-- The maximum modulus M(r) = max_{|z|=r} |f(z)| -/
noncomputable def maxModulus (f : EntireFunction) (r : ℝ) : ℝ :=
  ⨆ θ : ℝ, ‖∑' n, f.coeff n * (r * exp (I * θ)) ^ n‖

/-- The ratio μ(r)/M(r) -/
noncomputable def termModulusRatio (f : EntireFunction) (r : ℝ) : ℝ :=
  maxTerm f r / maxModulus f r

/-
## Part 2: The Original Conjecture

Erdős asked: if lim μ(r)/M(r) exists, must it be 0?
-/

/-- The original conjecture: if the limit exists, it equals 0 -/
def OriginalConjecture : Prop :=
  ∀ f : EntireFunction, ∀ L : ℝ,
    Tendsto (termModulusRatio f) atTop (nhds L) → L = 0

/-- Clunie's result for non-negative coefficients -/
axiom clunie_positive_coeffs (f : EntireFunction) (hpos : ∀ n, (f.coeff n).re ≥ 0 ∧ (f.coeff n).im = 0)
    (L : ℝ) (hL : Tendsto (termModulusRatio f) atTop (nhds L)) :
    L = 0

/-
## Part 3: Clunie-Hayman Counterexample

The conjecture is FALSE: the limit can be any λ ∈ [0, 1/2].
-/

/-- There exist entire functions achieving any limit in [0, 1/2] -/
axiom clunie_hayman_1964 :
  ∀ lam : ℝ, 0 ≤ lam → lam ≤ 1/2 →
    ∃ f : EntireFunction, Tendsto (termModulusRatio f) atTop (nhds lam)

/-- The upper bound is 1/2 -/
axiom ratio_upper_bound (f : EntireFunction) (L : ℝ)
    (hL : Tendsto (termModulusRatio f) atTop (nhds L)) :
    L ≤ 1/2

/-- The conjecture is disproved -/
theorem original_conjecture_false : ¬OriginalConjecture := by
  intro hConj
  -- Take λ = 1/4 ∈ (0, 1/2]
  have h := clunie_hayman_1964 (1/4) (by norm_num) (by norm_num)
  obtain ⟨f, hf⟩ := h
  -- By the conjecture, the limit should be 0
  have hzero := hConj f (1/4) hf
  -- But 1/4 ≠ 0, contradiction
  norm_num at hzero

/-
## Part 4: The Complete Characterization

The set of achievable limits is exactly [0, 1/2].
-/

/-- The set of achievable limit values -/
def AchievableLimits : Set ℝ :=
  { L | ∃ f : EntireFunction, Tendsto (termModulusRatio f) atTop (nhds L) }

/-- The term-to-modulus ratio is non-negative for every `r ≥ 0`: both `maxTerm`
    (a supremum of `‖aₙ‖·rⁿ ≥ 0`) and `maxModulus` (a supremum of norms `≥ 0`) are
    non-negative, so their quotient is. -/
theorem termModulusRatio_nonneg (f : EntireFunction) {r : ℝ} (hr : 0 ≤ r) :
    0 ≤ termModulusRatio f r := by
  unfold termModulusRatio maxTerm maxModulus
  apply div_nonneg
  · exact Real.iSup_nonneg fun n => mul_nonneg (norm_nonneg _) (pow_nonneg hr n)
  · exact Real.iSup_nonneg fun _ => norm_nonneg _

/-- Complete characterization of achievable limits -/
theorem achievable_limits_characterization :
    AchievableLimits = Set.Icc 0 (1/2) := by
  ext L
  constructor
  · -- If L is achievable, then L ∈ [0, 1/2]
    intro ⟨f, hf⟩
    constructor
    · -- L ≥ 0: the ratio is eventually non-negative (for r ≥ 0), so its limit is ≥ 0
      refine ge_of_tendsto hf ?_
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with r hr
      exact termModulusRatio_nonneg f hr
    · -- L ≤ 1/2 (Clunie-Hayman upper bound)
      exact ratio_upper_bound f L hf
  · -- If L ∈ [0, 1/2], then L is achievable
    intro ⟨hL0, hL12⟩
    exact clunie_hayman_1964 L hL0 hL12

/-
## Part 5: Central Index

The maximum term is achieved at specific indices.
-/

/-- A choice of index whose term `‖aₙ‖rⁿ` dominates the constant term `‖a₀‖`.

    The genuine central index `ν(r)` is the largest `n` with `‖aₙ‖rⁿ = μ(r)`, but
    that is only well-defined when the maximum term is actually attained (the `iSup`
    defining `maxTerm` can be a junk value when the terms are unbounded). This
    well-typed stand-in picks, via choice, some `n` with `‖a₀‖ ≤ ‖aₙ‖rⁿ` (witnessed
    by `n = 0`), which always exists. -/
noncomputable def centralIndex (f : EntireFunction) (r : ℝ) : ℕ :=
  Classical.choose (⟨0, le_refl _⟩ : ∃ n : ℕ, ‖f.coeff 0‖ * r ^ (0 : ℕ) ≤ ‖f.coeff n‖ * r ^ n)

/- Central index grows to infinity as r → ∞ -/
/-
## Part 6: Asymptotic Relations

Relation between μ(r), M(r), and the growth of f.
-/

/- For any entire function, μ(r) ≤ M(r) -/
/-- Asymptotic: M(r) ~ μ(r) for "normal" functions -/
def IsNormal (f : EntireFunction) : Prop :=
  Tendsto (termModulusRatio f) atTop (nhds 0)

/-- Positive coefficient functions are normal.

    NOTE: this asserts more than `clunie_positive_coeffs`, which only says that
    *if* the ratio converges to some `L` then `L = 0`. `IsNormal` additionally
    requires that the limit *exists* (and equals `0`). Establishing existence is
    the analytic heart of Clunie's (unpublished) result and is not implied by the
    conditional axiom, so this remains a `sorry`. -/
theorem positive_coeffs_normal (f : EntireFunction)
    (hpos : ∀ n, (f.coeff n).re ≥ 0 ∧ (f.coeff n).im = 0) :
    IsNormal f := by
  unfold IsNormal
  -- Requires the existence of the limit (Clunie's full result), not just its value.
  sorry

/-
## Part 7: Order and Type

Connection to order of growth.
-/

/-- Order of an entire function: inf{ρ : M(r) ≤ exp(r^ρ)} -/
noncomputable def order (f : EntireFunction) : ℝ :=
  sInf { ρ : ℝ | ∃ C : ℝ, ∀ r > 0, maxModulus f r ≤ C * Real.exp (r ^ ρ) }

/-- Type of an entire function of given order -/
noncomputable def typeOfOrder (f : EntireFunction) (ρ : ℝ) : ℝ :=
  sInf { σ : ℝ | ∃ C : ℝ, ∀ r > 0, maxModulus f r ≤ C * Real.exp (σ * r ^ ρ) }

/- Functions of order 0 have ratio tending to 0 -/
/-
## Part 8: Examples

Specific examples illustrating the theorem.
-/

/- The exponential function has ratio → 0 -/
/- Existence of pathological examples -/
/-
## Part 9: Main Problem Statement
-/

/-- Erdős Problem #227: Complete statement -/
theorem erdos_227_statement :
    -- Original conjecture was: limit exists ⟹ limit = 0
    -- This is FALSE
    (¬OriginalConjecture) ∧
    -- Clunie's partial result: true for positive coefficients
    (∀ f : EntireFunction, (∀ n, (f.coeff n).re ≥ 0 ∧ (f.coeff n).im = 0) →
      ∀ L, Tendsto (termModulusRatio f) atTop (nhds L) → L = 0) ∧
    -- Clunie-Hayman complete answer: achievable limits = [0, 1/2]
    AchievableLimits = Set.Icc 0 (1/2) := by
  refine ⟨original_conjecture_false, ?_, achievable_limits_characterization⟩
  exact clunie_positive_coeffs

/-
## Part 10: Summary
-/

/-- Summary of Erdős Problem #227 -/
theorem erdos_227_summary :
    -- The conjecture is disproved
    (¬OriginalConjecture) ∧
    -- Complete characterization exists
    (AchievableLimits = Set.Icc 0 (1/2)) ∧
    -- Special case for positive coefficients
    (∀ f : EntireFunction, (∀ n, (f.coeff n).re ≥ 0 ∧ (f.coeff n).im = 0) →
      ∀ L, Tendsto (termModulusRatio f) atTop (nhds L) → L = 0) := by
  refine ⟨original_conjecture_false, achievable_limits_characterization, ?_⟩
  exact clunie_positive_coeffs

/- Erdős Problem #227: SOLVED (DISPROVED). -/

/-
## Part 11: Elementary Bounds — Maximum Term vs Maximum Modulus

Axiom-free supporting layer. The `EntireFunction` structure records only the
coefficients; it does not force the power series to converge anywhere.
`IsEntire` captures genuine entireness (absolute convergence of the coefficient
series at every radius). In Clunie's setting — non-negative real coefficients —
we prove the elementary inequality `μ(r) ≤ M(r)` (the maximum term is one term
of the series that sums to `f(r) ≤ M(r)`), hence the term/modulus ratio is at
most `1` and any limit `L` of the ratio lies in `[0, 1]`. The deep
Clunie–Hayman refinement `L ≤ 1/2` remains axiomatized (`ratio_upper_bound`),
as does Clunie's exact value `L = 0` (`clunie_positive_coeffs`).
-/

/-- Genuine entireness: absolute convergence of the coefficient series at every
    non-negative radius. The bare `EntireFunction` structure does not require
    this; theorems that need convergence take it as an explicit hypothesis. -/
def IsEntire (f : EntireFunction) : Prop :=
  ∀ r : ℝ, 0 ≤ r → Summable fun n => ‖f.coeff n‖ * r ^ n

/-- The maximum term is non-negative for `r ≥ 0`. -/
theorem maxTerm_nonneg (f : EntireFunction) {r : ℝ} (hr : 0 ≤ r) :
    0 ≤ maxTerm f r :=
  Real.iSup_nonneg fun n => mul_nonneg (norm_nonneg _) (pow_nonneg hr n)

/-- The maximum modulus is non-negative. -/
theorem maxModulus_nonneg (f : EntireFunction) (r : ℝ) :
    0 ≤ maxModulus f r :=
  Real.iSup_nonneg fun _ => norm_nonneg _

/-- Norm of the `n`-th series term at the point `r·e^{iθ}`: it equals
    `‖aₙ‖·rⁿ`, independently of the angle `θ`. -/
theorem norm_series_term (f : EntireFunction) {r : ℝ} (hr : 0 ≤ r) (θ : ℝ) (n : ℕ) :
    ‖f.coeff n * (↑r * exp (I * ↑θ)) ^ n‖ = ‖f.coeff n‖ * r ^ n := by
  have hexp : ‖exp (I * (θ : ℂ))‖ = 1 := by
    rw [Complex.norm_exp]
    simp [Complex.mul_re]
  rw [norm_mul, norm_pow, norm_mul, hexp, mul_one, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg hr]

/-- Absolute convergence at radius `r` gives convergence at every point of the
    circle `|z| = r`. -/
theorem summable_series_term (f : EntireFunction) {r : ℝ} (hr : 0 ≤ r)
    (hs : Summable fun n => ‖f.coeff n‖ * r ^ n) (θ : ℝ) :
    Summable fun n => f.coeff n * (↑r * exp (I * ↑θ)) ^ n :=
  Summable.of_norm (hs.congr fun n => (norm_series_term f hr θ n).symm)

/-- Triangle inequality on the circle of radius `r`: `‖f(re^{iθ})‖` is bounded
    by the absolute sum `Σ ‖aₙ‖ rⁿ`, uniformly in `θ`. -/
theorem norm_tsum_le_sum_norm (f : EntireFunction) {r : ℝ} (hr : 0 ≤ r)
    (hs : Summable fun n => ‖f.coeff n‖ * r ^ n) (θ : ℝ) :
    ‖∑' n, f.coeff n * (↑r * exp (I * ↑θ)) ^ n‖ ≤ ∑' n, ‖f.coeff n‖ * r ^ n :=
  calc ‖∑' n, f.coeff n * (↑r * exp (I * ↑θ)) ^ n‖
      ≤ ∑' n, ‖f.coeff n * (↑r * exp (I * ↑θ)) ^ n‖ :=
        norm_tsum_le_tsum_norm (hs.congr fun n => (norm_series_term f hr θ n).symm)
    _ = ∑' n, ‖f.coeff n‖ * r ^ n := tsum_congr fun n => norm_series_term f hr θ n

/-- The family `θ ↦ ‖f(re^{iθ})‖` is bounded above (by the absolute sum). -/
theorem bddAbove_range_norm (f : EntireFunction) {r : ℝ} (hr : 0 ≤ r)
    (hs : Summable fun n => ‖f.coeff n‖ * r ^ n) :
    BddAbove (Set.range fun θ : ℝ => ‖∑' n, f.coeff n * (↑r * exp (I * ↑θ)) ^ n‖) := by
  refine ⟨∑' n, ‖f.coeff n‖ * r ^ n, ?_⟩
  rintro x ⟨θ, rfl⟩
  exact norm_tsum_le_sum_norm f hr hs θ

/-- `M(r) ≤ Σ ‖aₙ‖ rⁿ`: the maximum modulus is at most the absolute sum. -/
theorem maxModulus_le_tsum (f : EntireFunction) {r : ℝ} (hr : 0 ≤ r)
    (hs : Summable fun n => ‖f.coeff n‖ * r ^ n) :
    maxModulus f r ≤ ∑' n, ‖f.coeff n‖ * r ^ n :=
  ciSup_le fun θ => norm_tsum_le_sum_norm f hr hs θ

/-- For non-negative real coefficients the value at `θ = 0` is exactly the
    absolute sum: `‖f(r)‖ = Σ aₙ rⁿ = Σ ‖aₙ‖ rⁿ`. -/
theorem norm_tsum_at_zero_of_nonneg (f : EntireFunction) {r : ℝ} (hr : 0 ≤ r)
    (hpos : ∀ n, (f.coeff n).re ≥ 0 ∧ (f.coeff n).im = 0) :
    ‖∑' n, f.coeff n * (↑r * exp (I * ((0 : ℝ) : ℂ))) ^ n‖
      = ∑' n, ‖f.coeff n‖ * r ^ n := by
  have hcoeff : ∀ n, f.coeff n = ((‖f.coeff n‖ : ℝ) : ℂ) := by
    intro n
    have h1 : f.coeff n = (((f.coeff n).re : ℝ) : ℂ) :=
      Complex.ext (by simp) (by simpa using (hpos n).2)
    have h2 : ‖f.coeff n‖ = (f.coeff n).re := by
      rw [h1, Complex.norm_real, Complex.ofReal_re, Real.norm_eq_abs]
      exact abs_of_nonneg (hpos n).1
    rw [h2]
    exact h1
  have h0 : ∀ n : ℕ, f.coeff n * (↑r * exp (I * ((0 : ℝ) : ℂ))) ^ n
      = ((‖f.coeff n‖ * r ^ n : ℝ) : ℂ) := by
    intro n
    have hexp0 : exp (I * ((0 : ℝ) : ℂ)) = 1 := by simp
    rw [hexp0, mul_one]
    conv_lhs => rw [hcoeff n]
    push_cast
    ring
  calc ‖∑' n, f.coeff n * (↑r * exp (I * ((0 : ℝ) : ℂ))) ^ n‖
      = ‖((∑' n, ‖f.coeff n‖ * r ^ n : ℝ) : ℂ)‖ := by
        rw [tsum_congr h0, ← Complex.ofReal_tsum]
    _ = ∑' n, ‖f.coeff n‖ * r ^ n := by
        rw [Complex.norm_real, Real.norm_eq_abs]
        exact abs_of_nonneg
          (tsum_nonneg fun n => mul_nonneg (norm_nonneg _) (pow_nonneg hr n))

/-- **Clunie's setting, elementary part**: for non-negative real coefficients
    the maximum term is at most the maximum modulus, `μ(r) ≤ M(r)` — each term
    `aₙrⁿ` is one summand of the non-negative series summing to `f(r) ≤ M(r)`. -/
theorem maxTerm_le_maxModulus_of_nonneg (f : EntireFunction) {r : ℝ} (hr : 0 ≤ r)
    (hpos : ∀ n, (f.coeff n).re ≥ 0 ∧ (f.coeff n).im = 0)
    (hs : Summable fun n => ‖f.coeff n‖ * r ^ n) :
    maxTerm f r ≤ maxModulus f r := by
  have hM : (∑' n, ‖f.coeff n‖ * r ^ n) ≤ maxModulus f r := by
    rw [← norm_tsum_at_zero_of_nonneg f hr hpos]
    exact le_ciSup (bddAbove_range_norm f hr hs) (0 : ℝ)
  have key : (⨆ n : ℕ, ‖f.coeff n‖ * r ^ n) ≤ maxModulus f r :=
    ciSup_le fun n =>
      le_trans (hs.le_tsum n fun j _ => mul_nonneg (norm_nonneg _) (pow_nonneg hr j)) hM
  exact key

/-- For non-negative real coefficients the term/modulus ratio is at most `1`. -/
theorem termModulusRatio_le_one_of_nonneg (f : EntireFunction) {r : ℝ} (hr : 0 ≤ r)
    (hpos : ∀ n, (f.coeff n).re ≥ 0 ∧ (f.coeff n).im = 0)
    (hs : Summable fun n => ‖f.coeff n‖ * r ^ n) :
    termModulusRatio f r ≤ 1 := by
  rcases (maxModulus_nonneg f r).eq_or_lt with hM | hM
  · unfold termModulusRatio
    rw [← hM, div_zero]
    exact zero_le_one
  · unfold termModulusRatio
    rw [div_le_one hM]
    exact maxTerm_le_maxModulus_of_nonneg f hr hpos hs

/-- Any limit of the term/modulus ratio of a genuinely entire function with
    non-negative real coefficients lies in `[0, 1]`. This is the elementary
    companion of the deep axiomatized results: Clunie–Hayman give `L ≤ 1/2`
    (`ratio_upper_bound`) and Clunie gives the exact value `L = 0`
    (`clunie_positive_coeffs`); the bound here uses only Mathlib. -/
theorem limit_mem_Icc_of_nonneg (f : EntireFunction)
    (hpos : ∀ n, (f.coeff n).re ≥ 0 ∧ (f.coeff n).im = 0)
    (hent : IsEntire f) {L : ℝ}
    (hL : Tendsto (termModulusRatio f) atTop (nhds L)) :
    L ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · refine ge_of_tendsto hL ?_
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with r hr
    exact termModulusRatio_nonneg f hr
  · refine le_of_tendsto hL ?_
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with r hr
    exact termModulusRatio_le_one_of_nonneg f hr hpos (hent r hr)

/-
### The exponential function

A concrete witness that `IsEntire` is non-vacuous and the hypotheses above are
satisfiable: `exp` with coefficients `1/n!`.
-/

/-- The exponential function `Σ zⁿ/n!` as an `EntireFunction`. -/
noncomputable def expFunction : EntireFunction where
  coeff n := 1 / (n.factorial : ℂ)
  not_polynomial N := ⟨N + 1, Nat.lt_succ_self N, by
    have h : (((N + 1).factorial : ℕ) : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    exact one_div_ne_zero h⟩

/-- The coefficients of `exp` are non-negative reals. -/
theorem expFunction_coeff_nonneg (n : ℕ) :
    (expFunction.coeff n).re ≥ 0 ∧ (expFunction.coeff n).im = 0 := by
  have h : expFunction.coeff n = ((1 / (n.factorial : ℝ) : ℝ) : ℂ) := by
    show (1 : ℂ) / (n.factorial : ℂ) = _
    push_cast
    ring
  constructor
  · rw [h, Complex.ofReal_re]
    positivity
  · rw [h, Complex.ofReal_im]

/-- `exp` is genuinely entire: `Σ ‖1/n!‖ rⁿ` converges for every `r ≥ 0`. -/
theorem expFunction_isEntire : IsEntire expFunction := by
  intro r hr
  refine (Real.summable_pow_div_factorial r).congr fun n => ?_
  have h : ‖expFunction.coeff n‖ = 1 / (n.factorial : ℝ) := by
    show ‖(1 : ℂ) / (n.factorial : ℂ)‖ = _
    rw [norm_div, norm_one, Complex.norm_natCast]
  rw [h]
  ring

/-- The term/modulus ratio of `exp` is at most `1` for every `r ≥ 0`. -/
theorem expFunction_ratio_le_one {r : ℝ} (hr : 0 ≤ r) :
    termModulusRatio expFunction r ≤ 1 :=
  termModulusRatio_le_one_of_nonneg expFunction hr expFunction_coeff_nonneg
    (expFunction_isEntire r hr)

/-
## Part 12: The Unconditional Cauchy Estimate — μ(r) ≤ M(r) for ALL coefficients

Part 11 proved `μ(r) ≤ M(r)` only for non-negative real coefficients (where it
is elementary: the maximum term is one summand of the positive series summing
to `f(r)`). This part removes the coefficient hypothesis entirely via genuine
complex analysis: the coefficients of a power series with infinite radius of
convergence are Cauchy integrals over circles, so Cauchy's estimate

    ‖aₙ‖ · rⁿ ≤ max_{|z| = r} ‖f(z)‖ = M(r)

holds for every `n` and every `r > 0`.

The Mathlib bridge: `FormalMultilinearSeries.ofScalars ℂ f.coeff` packages the
coefficients as a formal power series `p`; `IsEntire` forces `p.radius = ⊤`,
so `p.sum` is an entire function represented by `p`
(`FormalMultilinearSeries.hasFPowerSeriesOnBall`), hence differentiable.
`Differentiable.hasFPowerSeriesOnBall` represents the same function by the
Cauchy power series `cauchyPowerSeries p.sum 0 r` on every ball, and
one-dimensional uniqueness (`HasFPowerSeriesAt.eq_formalMultilinearSeries`)
identifies the two series. Mathlib's `norm_cauchyPowerSeries_le` then bounds
`‖aₙ‖` by the circle average of `‖f‖` times `r⁻ⁿ`, and the circle average is
at most the sup `M(r)`.

Consequences: the ratio bound `μ/M ≤ 1` and the limit membership `L ∈ [0, 1]`
now hold for EVERY genuinely entire function — the Part-11 `_of_nonneg`
versions become special cases. The deep Clunie–Hayman refinement (`L ≤ 1/2`)
remains axiomatized; this part is axiom-free.
-/

/-- The sum function `z ↦ Σ aₙ zⁿ` of the power series, packaged as
`FormalMultilinearSeries.sum` of the scalar series. -/
noncomputable def seriesSum (f : EntireFunction) : ℂ → ℂ :=
  (ofScalars ℂ f.coeff).sum

/-- `seriesSum` is pointwise the naive `tsum` of the power series. -/
theorem seriesSum_apply (f : EntireFunction) (z : ℂ) :
    seriesSum f z = ∑' n, f.coeff n * z ^ n := by
  have h := ofScalars_sum_eq (E := ℂ) f.coeff z
  simpa [seriesSum, ofScalarsSum, smul_eq_mul] using h

/-- Genuine entireness forces infinite radius of convergence for the
formal scalar series. -/
theorem ofScalars_radius_eq_top (f : EntireFunction) (hent : IsEntire f) :
    (ofScalars ℂ f.coeff).radius = ⊤ := by
  refine ENNReal.eq_top_of_forall_nnreal_le fun r => ?_
  refine le_radius_of_summable _ ?_
  refine ((hent r r.coe_nonneg).congr fun n => ?_)
  rw [ofScalars_norm]

/-- The sum function is represented by the scalar series on all of `ℂ`. -/
theorem hasFPowerSeriesOnBall_seriesSum (f : EntireFunction) (hent : IsEntire f) :
    HasFPowerSeriesOnBall (seriesSum f) (ofScalars ℂ f.coeff) 0 ⊤ := by
  have h := (ofScalars ℂ f.coeff).hasFPowerSeriesOnBall
    (by rw [ofScalars_radius_eq_top f hent]; simp)
  rwa [ofScalars_radius_eq_top f hent] at h

/-- A genuinely entire `f` has a complex-differentiable sum function. -/
theorem differentiable_seriesSum (f : EntireFunction) (hent : IsEntire f) :
    Differentiable ℂ (seriesSum f) := by
  intro z
  have h := hasFPowerSeriesOnBall_seriesSum f hent
  exact (h.analyticAt_of_mem (by simp)).differentiableAt

/-- Pointwise bound on the circle: `‖(seriesSum f)(circleMap 0 r θ)‖ ≤ M(r)`.
The parametrisations `circleMap 0 r θ = r·e^{θi}` and `r·e^{iθ}` agree. -/
theorem norm_seriesSum_circleMap_le (f : EntireFunction) {r : ℝ} (hr : 0 ≤ r)
    (hent : IsEntire f) (θ : ℝ) :
    ‖seriesSum f (circleMap 0 r θ)‖ ≤ maxModulus f r := by
  have hmap : circleMap 0 r θ = (r : ℂ) * exp (I * θ) := by
    rw [circleMap_zero, mul_comm I (θ : ℂ)]
  rw [hmap, seriesSum_apply]
  exact le_ciSup (bddAbove_range_norm f hr (hent r hr)) θ

/-- **Cauchy's estimate, unconditional**: for a genuinely entire function and
every `r > 0`, each term of the power series is bounded by the maximum
modulus: `‖aₙ‖ · rⁿ ≤ M(r)`. No hypothesis on the coefficients. -/
theorem norm_coeff_mul_pow_le_maxModulus (f : EntireFunction) {r : ℝ} (hr : 0 < r)
    (hent : IsEntire f) (n : ℕ) :
    ‖f.coeff n‖ * r ^ n ≤ maxModulus f r := by
  set R : NNReal := ⟨r, hr.le⟩ with hR
  have hRpos : 0 < R := by
    rw [← NNReal.coe_lt_coe]
    exact hr
  have hRr : (R : ℝ) = r := rfl
  -- the Cauchy series at radius r equals the scalar series, by uniqueness
  have h1 : HasFPowerSeriesAt (seriesSum f) (ofScalars ℂ f.coeff) 0 :=
    (hasFPowerSeriesOnBall_seriesSum f hent).hasFPowerSeriesAt
  have h2 : HasFPowerSeriesAt (seriesSum f)
      (cauchyPowerSeries (seriesSum f) 0 R) 0 :=
    ((differentiable_seriesSum f hent).hasFPowerSeriesOnBall 0 hRpos).hasFPowerSeriesAt
  have heq : ofScalars ℂ f.coeff = cauchyPowerSeries (seriesSum f) 0 R :=
    h1.eq_formalMultilinearSeries h2
  -- Cauchy's coefficient bound
  have hbound := norm_cauchyPowerSeries_le (seriesSum f) 0 R n
  rw [← heq, ofScalars_norm] at hbound
  -- bound the circle average by the sup M(r)
  have hFcont : Continuous fun θ : ℝ => ‖seriesSum f (circleMap 0 (R : ℝ) θ)‖ :=
    ((differentiable_seriesSum f hent).continuous.comp
      (continuous_circleMap 0 (R : ℝ))).norm
  have hint : (∫ θ : ℝ in (0)..(2 * Real.pi), ‖seriesSum f (circleMap 0 (R : ℝ) θ)‖)
      ≤ 2 * Real.pi * maxModulus f r := by
    have hmono : ∀ θ ∈ Set.Icc (0 : ℝ) (2 * Real.pi),
        ‖seriesSum f (circleMap 0 (R : ℝ) θ)‖ ≤ maxModulus f r := fun θ _ => by
      rw [hRr]
      exact norm_seriesSum_circleMap_le f hr.le hent θ
    calc (∫ θ : ℝ in (0)..(2 * Real.pi), ‖seriesSum f (circleMap 0 (R : ℝ) θ)‖)
        ≤ ∫ _ : ℝ in (0)..(2 * Real.pi), maxModulus f r :=
          intervalIntegral.integral_mono_on (by positivity)
            (hFcont.intervalIntegrable _ _) intervalIntegrable_const hmono
      _ = 2 * Real.pi * maxModulus f r := by
          rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero]
  -- assemble: ‖aₙ‖ ≤ M(r) · r⁻ⁿ, then multiply through by rⁿ
  have hC : ((2 * Real.pi)⁻¹ *
      ∫ θ : ℝ in (0)..(2 * Real.pi), ‖seriesSum f (circleMap 0 (R : ℝ) θ)‖)
      ≤ maxModulus f r := by
    have hstep := mul_le_mul_of_nonneg_left hint
      (by positivity : (0 : ℝ) ≤ (2 * Real.pi)⁻¹)
    calc (2 * Real.pi)⁻¹ *
        ∫ θ : ℝ in (0)..(2 * Real.pi), ‖seriesSum f (circleMap 0 (R : ℝ) θ)‖
        ≤ (2 * Real.pi)⁻¹ * (2 * Real.pi * maxModulus f r) := hstep
      _ = maxModulus f r := by
          field_simp
  have hcoeff : ‖f.coeff n‖ ≤ maxModulus f r * (r⁻¹) ^ n := by
    have habs : |(R : ℝ)| = r := by rw [hRr, abs_of_pos hr]
    have hstep := hbound.trans
      (mul_le_mul_of_nonneg_right hC (by positivity : (0 : ℝ) ≤ |(R : ℝ)|⁻¹ ^ n))
    rwa [habs] at hstep
  calc ‖f.coeff n‖ * r ^ n
      ≤ (maxModulus f r * (r⁻¹) ^ n) * r ^ n := by
        gcongr
    _ = maxModulus f r := by
        rw [mul_assoc, ← mul_pow, inv_mul_cancel₀ (ne_of_gt hr), one_pow, mul_one]

/-- **Unconditional `μ(r) ≤ M(r)`** for every genuinely entire function and
every `r ≥ 0` — the Part-11 `maxTerm_le_maxModulus_of_nonneg` without the
non-negativity hypothesis. `r > 0` is Cauchy's estimate; at `r = 0` both
sides collapse to `‖a₀‖`. -/
theorem maxTerm_le_maxModulus (f : EntireFunction) {r : ℝ} (hr : 0 ≤ r)
    (hent : IsEntire f) :
    maxTerm f r ≤ maxModulus f r := by
  rcases hr.eq_or_lt with rfl | hrpos
  · -- r = 0: every term with n > 0 vanishes and the n = 0 term is ‖a₀‖ = ‖f(0)‖
    apply ciSup_le
    intro n
    have h0 : ‖∑' m, f.coeff m * ((0 : ℝ) * exp (I * (0 : ℝ))) ^ m‖ = ‖f.coeff 0‖ := by
      have hz : ((0 : ℝ) : ℂ) * exp (I * (0 : ℝ)) = 0 := by simp
      rw [hz]
      have : (∑' m, f.coeff m * (0 : ℂ) ^ m) = f.coeff 0 := by
        rw [tsum_eq_single 0 (fun m hm => by
          rw [zero_pow hm, mul_zero])]
        simp
      rw [this]
    have hM : ‖f.coeff 0‖ ≤ maxModulus f 0 := by
      rw [← h0]
      exact le_ciSup (bddAbove_range_norm f le_rfl (hent 0 le_rfl)) (0 : ℝ)
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simpa using hM
    · have hzero : ‖f.coeff n‖ * (0 : ℝ) ^ n = 0 := by
        rw [zero_pow hn.ne', mul_zero]
      rw [hzero]
      exact Real.iSup_nonneg fun _ => norm_nonneg _
  · exact ciSup_le fun n => norm_coeff_mul_pow_le_maxModulus f hrpos hent n

/-- The term/modulus ratio is at most `1` for every genuinely entire function
— unconditional version of `termModulusRatio_le_one_of_nonneg`. -/
theorem termModulusRatio_le_one (f : EntireFunction) {r : ℝ} (hr : 0 ≤ r)
    (hent : IsEntire f) :
    termModulusRatio f r ≤ 1 := by
  rcases (maxModulus_nonneg f r).eq_or_lt with hM | hM
  · unfold termModulusRatio
    rw [← hM, div_zero]
    exact zero_le_one
  · unfold termModulusRatio
    rw [div_le_one hM]
    exact maxTerm_le_maxModulus f hr hent

/-- Any limit of the term/modulus ratio of a genuinely entire function lies in
`[0, 1]` — unconditional version of `limit_mem_Icc_of_nonneg`. Together with
the axiomatized Clunie–Hayman results (`ratio_upper_bound`: `L ≤ 1/2`;
`clunie_hayman_1964`: every `L ∈ [0, 1/2]` is achieved), this brackets the
achievable-limit analysis with an axiom-free outer bound. -/
theorem limit_mem_Icc (f : EntireFunction) (hent : IsEntire f) {L : ℝ}
    (hL : Tendsto (termModulusRatio f) atTop (nhds L)) :
    L ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · refine ge_of_tendsto hL ?_
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with r hr
    exact termModulusRatio_nonneg f hr
  · refine le_of_tendsto hL ?_
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with r hr
    exact termModulusRatio_le_one f hr hent

end Erdos227
