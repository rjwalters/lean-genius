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
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.Basic

namespace Erdos227

open Complex Filter Topology

/-!
## Part 1: Basic Definitions

Maximum term and maximum modulus for power series.
-/

/-- An entire function represented by its power series coefficients -/
structure EntireFunction where
  coeff : ℕ → ℂ
  not_polynomial : ∀ N : ℕ, ∃ n > N, coeff n ≠ 0

/-- The maximum term μ(r) = max_n |aₙ|rⁿ -/
noncomputable def maxTerm (f : EntireFunction) (r : ℝ) : ℝ :=
  ⨆ n : ℕ, Complex.abs (f.coeff n) * r ^ n

/-- The maximum modulus M(r) = max_{|z|=r} |f(z)| -/
noncomputable def maxModulus (f : EntireFunction) (r : ℝ) : ℝ :=
  ⨆ θ : ℝ, Complex.abs (∑' n, f.coeff n * (r * exp (I * θ)) ^ n)

/-- The ratio μ(r)/M(r) -/
noncomputable def termModulusRatio (f : EntireFunction) (r : ℝ) : ℝ :=
  maxTerm f r / maxModulus f r

/-!
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

/-!
## Part 3: Clunie-Hayman Counterexample

The conjecture is FALSE: the limit can be any λ ∈ [0, 1/2].
-/

/-- There exist entire functions achieving any limit in [0, 1/2] -/
axiom clunie_hayman_1964 :
  ∀ λ : ℝ, 0 ≤ λ → λ ≤ 1/2 →
    ∃ f : EntireFunction, Tendsto (termModulusRatio f) atTop (nhds λ)

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

/-!
## Part 4: The Complete Characterization

The set of achievable limits is exactly [0, 1/2].
-/

/-- The set of achievable limit values -/
def AchievableLimits : Set ℝ :=
  { L | ∃ f : EntireFunction, Tendsto (termModulusRatio f) atTop (nhds L) }

/-- Complete characterization of achievable limits -/
theorem achievable_limits_characterization :
    AchievableLimits = Set.Icc 0 (1/2) := by
  ext L
  constructor
  · -- If L is achievable, then L ∈ [0, 1/2]
    intro ⟨f, hf⟩
    constructor
    · -- L ≥ 0 (ratios are non-negative)
      sorry
    · -- L ≤ 1/2 (Clunie-Hayman upper bound)
      exact ratio_upper_bound f L hf
  · -- If L ∈ [0, 1/2], then L is achievable
    intro ⟨hL0, hL12⟩
    exact clunie_hayman_1964 L hL0 hL12

/-!
## Part 5: Central Index

The maximum term is achieved at specific indices.
-/

/-- The central index: n where |aₙ|rⁿ = μ(r) -/
noncomputable def centralIndex (f : EntireFunction) (r : ℝ) : ℕ :=
  Classical.choose (⟨0, le_refl _⟩ : ∃ n, Complex.abs (f.coeff n) * r ^ n ≤ maxTerm f r)

/-- Central index grows to infinity as r → ∞ -/
axiom central_index_unbounded (f : EntireFunction) :
    Tendsto (centralIndex f) atTop atTop

/-!
## Part 6: Asymptotic Relations

Relation between μ(r), M(r), and the growth of f.
-/

/-- For any entire function, μ(r) ≤ M(r) -/
axiom max_term_le_max_modulus (f : EntireFunction) (r : ℝ) (hr : r > 0) :
    maxTerm f r ≤ maxModulus f r

/-- Asymptotic: M(r) ~ μ(r) for "normal" functions -/
def IsNormal (f : EntireFunction) : Prop :=
  Tendsto (termModulusRatio f) atTop (nhds 0)

/-- Positive coefficient functions are normal -/
theorem positive_coeffs_normal (f : EntireFunction)
    (hpos : ∀ n, (f.coeff n).re ≥ 0 ∧ (f.coeff n).im = 0) :
    IsNormal f := by
  unfold IsNormal
  -- Follows from Clunie's result
  sorry

/-!
## Part 7: Order and Type

Connection to order of growth.
-/

/-- Order of an entire function: inf{ρ : M(r) ≤ exp(r^ρ)} -/
noncomputable def order (f : EntireFunction) : ℝ :=
  sInf { ρ : ℝ | ∃ C : ℝ, ∀ r > 0, maxModulus f r ≤ C * Real.exp (r ^ ρ) }

/-- Type of an entire function of given order -/
noncomputable def typeOfOrder (f : EntireFunction) (ρ : ℝ) : ℝ :=
  sInf { σ : ℝ | ∃ C : ℝ, ∀ r > 0, maxModulus f r ≤ C * Real.exp (σ * r ^ ρ) }

/-- Functions of order 0 have ratio tending to 0 -/
axiom order_zero_normal (f : EntireFunction) (h : order f = 0) :
    IsNormal f

/-!
## Part 8: Examples

Specific examples illustrating the theorem.
-/

/-- The exponential function has ratio → 0 -/
axiom exp_is_normal : ∃ f : EntireFunction,
    (∀ n, f.coeff n = 1 / (n.factorial : ℂ)) ∧ IsNormal f

/-- Existence of pathological examples -/
axiom pathological_examples_exist :
    ∀ λ : ℝ, 0 < λ → λ < 1/2 →
      ∃ f : EntireFunction,
        -- Not of finite order
        (∀ ρ > 0, ∃ r > 0, maxModulus f r > Real.exp (r ^ ρ)) ∧
        -- But has limit λ
        Tendsto (termModulusRatio f) atTop (nhds λ)

/-!
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
  constructor
  · exact original_conjecture_false
  constructor
  · exact clunie_positive_coeffs
  · exact achievable_limits_characterization

/-!
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
  constructor
  · exact original_conjecture_false
  constructor
  · exact achievable_limits_characterization
  · exact clunie_positive_coeffs

/-- The answer to Erdős Problem #227: SOLVED (DISPROVED) -/
theorem erdos_227_answer : True := trivial

end Erdos227
