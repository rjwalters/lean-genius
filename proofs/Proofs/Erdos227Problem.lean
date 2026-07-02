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
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Archimedean
import Mathlib.Order.Filter.Basic

namespace Erdos227

open Complex Filter Topology

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

end Erdos227
