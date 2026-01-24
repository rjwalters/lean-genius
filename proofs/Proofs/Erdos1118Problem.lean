/-
  Erdős Problem #1118: Entire Functions with Finite Measure Superlevel Sets

  Source: https://erdosproblems.com/1118
  Status: SOLVED (Camera 1977, Gol'dberg 1979)

  Statement:
  Let f(z) be a non-constant entire function such that, for some c > 0,
  the set E(c) = {z : |f(z)| > c} has finite planar measure.

  Questions:
  1. What is the minimum growth rate of f(z)?
  2. If E(c) has finite measure, must there exist c' < c with E(c') finite measure?

  Answers:
  1. Hayman conjectured ∫₀^∞ r/(log log M(r)) dr < ∞ is necessary and sufficient.
     This was proved by Camera (1977) and Gol'dberg (1979).
  2. NO - Gol'dberg showed the threshold set T = {c > 0 : |E(c)| < ∞}
     can be [m, ∞), (m, ∞), ∅, or (0, ∞) for different entire functions.

  References:
  - [Ha74] Hayman, "Research problems in function theory" (1974), Problem 2.40
  - [Ca77] Camera, PhD Thesis, Imperial College (1977)
  - [Go79b] Gol'dberg, Sibirsk. Mat. Zh. (1979), 512-518
-/

import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Complex Real MeasureTheory Set

namespace Erdos1118

/-
## Part I: Basic Definitions
-/

/-- An entire function (holomorphic on all of ℂ). -/
def IsEntire (f : ℂ → ℂ) : Prop :=
  Differentiable ℂ f

/-- A non-constant entire function. -/
def IsNonConstantEntire (f : ℂ → ℂ) : Prop :=
  IsEntire f ∧ ¬∃ w : ℂ, ∀ z, f z = w

/-- The superlevel set E(c) = {z : |f(z)| > c}. -/
def superlevelSet (f : ℂ → ℂ) (c : ℝ) : Set ℂ :=
  {z : ℂ | abs (f z) > c}

/-- The superlevel set has finite planar (Lebesgue) measure. -/
def HasFiniteMeasure (f : ℂ → ℂ) (c : ℝ) : Prop :=
  volume (superlevelSet f c) < ⊤

/-- The maximum modulus function M(r) = max_{|z|=r} |f(z)|. -/
noncomputable def maxModulus (f : ℂ → ℂ) (r : ℝ) : ℝ :=
  ⨆ (z : ℂ) (_ : abs z = r), abs (f z)

/-
## Part II: The Erdős Questions
-/

/-- The threshold set T(f) = {c > 0 : E(c) has finite measure}. -/
def thresholdSet (f : ℂ → ℂ) : Set ℝ :=
  {c : ℝ | c > 0 ∧ HasFiniteMeasure f c}

/-- Question 1: What is the minimum growth rate for finite measure superlevel sets? -/
def GrowthRateQuestion : Prop :=
  -- Characterize the class of entire functions with some c having |E(c)| < ∞
  True

/-- Question 2: Is the threshold set always a "tail" starting from 0? -/
def ThresholdMonotonicityQuestion : Prop :=
  -- If c ∈ T(f), must c' ∈ T(f) for all c' < c?
  True

/-
## Part III: Hayman's Conjecture and Growth Rate
-/

/-- The growth rate integral ∫₀^∞ r/(log log M(r)) dr. -/
noncomputable def growthIntegral (f : ℂ → ℂ) : ℝ :=
  ∫ r in Ioi (0 : ℝ), r / Real.log (Real.log (maxModulus f r))

/-- Hayman's conjecture: finite growth integral characterizes the property. -/
def HaymanConjecture : Prop :=
  ∀ f : ℂ → ℂ, IsNonConstantEntire f →
    (∃ c > 0, HasFiniteMeasure f c) ↔ growthIntegral f < ⊤

/-- **Camera-Gol'dberg Theorem (1977-1979):**
    Hayman's conjecture is true. -/
axiom camera_goldberg_theorem : HaymanConjecture

/-- The growth integral condition is necessary. -/
axiom growth_necessary (f : ℂ → ℂ) (hf : IsNonConstantEntire f)
    (c : ℝ) (hc : c > 0) (hFinite : HasFiniteMeasure f c) :
    growthIntegral f < ⊤

/-- The growth integral condition is sufficient. -/
axiom growth_sufficient (f : ℂ → ℂ) (hf : IsNonConstantEntire f)
    (hGrowth : growthIntegral f < ⊤) :
    ∃ c > 0, HasFiniteMeasure f c

/-
## Part IV: Gol'dberg's Counterexample
-/

/-- Answer to Question 2: NO, the threshold set need not extend to 0. -/
axiom goldberg_counterexample :
  ∃ f : ℂ → ℂ, IsNonConstantEntire f ∧
    ∃ m > 0, thresholdSet f = Ici m  -- T(f) = [m, ∞)

/-- Gol'dberg showed all these threshold shapes are possible. -/
axiom goldberg_threshold_classification :
  -- T(f) = ∅ is possible (no c gives finite measure)
  (∃ f : ℂ → ℂ, IsNonConstantEntire f ∧ thresholdSet f = ∅) ∧
  -- T(f) = (0, ∞) is possible (all positive c give finite measure)
  (∃ f : ℂ → ℂ, IsNonConstantEntire f ∧ thresholdSet f = Ioi 0) ∧
  -- T(f) = [m, ∞) is possible for any m > 0
  (∀ m > 0, ∃ f : ℂ → ℂ, IsNonConstantEntire f ∧ thresholdSet f = Ici m) ∧
  -- T(f) = (m, ∞) is possible for any m > 0
  (∀ m > 0, ∃ f : ℂ → ℂ, IsNonConstantEntire f ∧ thresholdSet f = Ioi m)

/-
## Part V: Properties of the Maximum Modulus
-/

/-- M(r) → ∞ as r → ∞ for non-constant entire functions (Liouville). -/
axiom max_modulus_unbounded (f : ℂ → ℂ) (hf : IsNonConstantEntire f) :
    Filter.Tendsto (maxModulus f) Filter.atTop Filter.atTop

/-- M(r) is increasing (roughly, by maximum principle). -/
axiom max_modulus_increasing (f : ℂ → ℂ) (hf : IsNonConstantEntire f)
    (r₁ r₂ : ℝ) (h : r₁ < r₂) (hr : r₁ ≥ 0) :
    maxModulus f r₁ ≤ maxModulus f r₂

/-- For polynomial f of degree d, M(r) ~ C·r^d. -/
axiom polynomial_max_modulus (p : Polynomial ℂ) (hp : p.degree > 0) :
    ∃ C > 0, ∀ᶠ r in Filter.atTop,
      maxModulus (fun z => p.eval z) r ≤ C * r ^ p.natDegree

/-
## Part VI: Examples
-/

/-- Polynomials have T(f) = (0, ∞). -/
axiom polynomial_threshold (p : Polynomial ℂ) (hp : p.degree > 0) :
    let f := fun z => p.eval z
    thresholdSet f = Ioi 0

/-- exp(z) has T(f) = ∅ (superlevel sets are half-planes). -/
axiom exp_threshold :
    thresholdSet Complex.exp = ∅

/-- For fast-growing entire functions, T(f) can be bounded below. -/
axiom fast_growth_bounded_threshold :
    ∃ f : ℂ → ℂ, IsNonConstantEntire f ∧
      ∃ m > 0, ∀ c < m, c > 0 → ¬HasFiniteMeasure f c

/-
## Part VII: Measure Theory Aspects
-/

/-- Superlevel sets are measurable (f is continuous). -/
axiom superlevel_measurable (f : ℂ → ℂ) (hf : IsEntire f) (c : ℝ) :
    MeasurableSet (superlevelSet f c)

/-- Nested property: c₁ < c₂ → E(c₂) ⊆ E(c₁). -/
theorem superlevel_nested (f : ℂ → ℂ) (c₁ c₂ : ℝ) (h : c₁ < c₂) :
    superlevelSet f c₂ ⊆ superlevelSet f c₁ := by
  intro z hz
  simp only [superlevelSet, mem_setOf_eq] at hz ⊢
  linarith

/-- If E(c₂) has finite measure and c₁ > c₂, then E(c₁) has finite measure. -/
theorem finite_measure_monotone (f : ℂ → ℂ) (c₁ c₂ : ℝ) (h : c₁ > c₂)
    (hFinite : HasFiniteMeasure f c₂) :
    HasFiniteMeasure f c₁ := by
  unfold HasFiniteMeasure at *
  have hSub : superlevelSet f c₁ ⊆ superlevelSet f c₂ := superlevel_nested f c₂ c₁ h
  exact lt_of_le_of_lt (measure_mono hSub) hFinite

/-- The threshold set is always an upper set (if non-empty). -/
theorem threshold_is_upper_set (f : ℂ → ℂ) :
    ∀ c₁ c₂, c₁ ∈ thresholdSet f → c₂ > c₁ → c₂ ∈ thresholdSet f := by
  intro c₁ c₂ ⟨hc₁_pos, hc₁_finite⟩ hc₂_gt
  constructor
  · linarith
  · exact finite_measure_monotone f c₂ c₁ hc₂_gt hc₁_finite

/-
## Part VIII: Connections
-/

/-- Connection to Nevanlinna theory. -/
def NevanlinnaConnection : Prop :=
  -- The growth rate relates to the order and type of f
  True

/-- Connection to value distribution theory. -/
def ValueDistributionConnection : Prop :=
  -- How often f takes values near infinity
  True

/-- Related to Problem 2.40 in Hayman's book. -/
def HaymanProblem240 : Prop :=
  HaymanConjecture

/-
## Part IX: Summary
-/

/-- **Erdős Problem #1118: SOLVED (Camera 1977, Gol'dberg 1979)**

Question 1: What is the minimum growth rate for an entire function
to have a superlevel set of finite measure?

Answer: ∫₀^∞ r/(log log M(r)) dr < ∞ is necessary and sufficient.
(Camera and Gol'dberg independently)

Question 2: If E(c) has finite measure, must E(c') for some c' < c?

Answer: NO - Gol'dberg showed T = {c : |E(c)| < ∞} can be [m,∞), (m,∞), ∅, or (0,∞).
-/
theorem erdos_1118_question1 : HaymanConjecture := camera_goldberg_theorem

/-- Answer to Question 2: The threshold set is NOT necessarily a tail from 0. -/
theorem erdos_1118_question2_negative :
    ∃ f : ℂ → ℂ, IsNonConstantEntire f ∧
      ∃ c > 0, HasFiniteMeasure f c ∧
        ∃ c' > 0, c' < c ∧ ¬HasFiniteMeasure f c' := by
  obtain ⟨f, hf, m, hm, hT⟩ := goldberg_counterexample
  use f, hf
  use m + 1
  constructor
  · linarith
  constructor
  · -- m + 1 ∈ [m, ∞) = thresholdSet f
    have h : m + 1 ∈ thresholdSet f := by
      rw [hT]
      simp only [mem_Ici]
      linarith
    exact h.2
  · use m / 2
    constructor
    · linarith
    constructor
    · linarith
    · -- m/2 ∉ [m, ∞), so not in threshold set
      intro hContra
      have h : m / 2 ∈ thresholdSet f := ⟨by linarith, hContra⟩
      rw [hT] at h
      simp only [mem_Ici] at h
      linarith

/-- Main theorem: Both questions answered. -/
theorem erdos_1118 :
    HaymanConjecture ∧
    ∃ f : ℂ → ℂ, IsNonConstantEntire f ∧
      ∃ m > 0, thresholdSet f = Ici m :=
  ⟨camera_goldberg_theorem, goldberg_counterexample⟩

/-- Summary: The problem is completely resolved. -/
theorem erdos_1118_summary :
    -- Q1: Growth rate characterized by integral condition
    HaymanConjecture ∧
    -- Q2: Threshold sets can have gaps
    (∃ f : ℂ → ℂ, IsNonConstantEntire f ∧ ∃ m > 0, thresholdSet f = Ici m) ∧
    -- All threshold shapes classified
    (∃ f : ℂ → ℂ, IsNonConstantEntire f ∧ thresholdSet f = ∅) :=
  ⟨camera_goldberg_theorem, goldberg_counterexample,
   goldberg_threshold_classification.1⟩

end Erdos1118
