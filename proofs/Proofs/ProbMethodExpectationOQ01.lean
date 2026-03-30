/-
  Probabilistic Method - Expectation OQ-01:
  Extending Finset Framework to MeasureTheory

  The gallery's probabilistic method uses Finset-based finite probability:
    prob(A) = |A| / |Ω|, E[X] = Σ X(ω) / |Ω|

  Mathlib has a full measure-theoretic probability framework:
    MeasureTheory.ProbabilityMeasure, MeasureTheory.integral, etc.

  This file bridges the two, showing the Finset versions are special
  cases of the measure-theoretic framework.

  Parent: ProbMethodExpectation.lean (verified, 0/0)
-/

import Mathlib

namespace ProbMethodExpectationOQ01

open MeasureTheory Finset

-- ============================================================
-- PART I: Finite Probability as a Special Case
-- ============================================================

/-- The counting measure on a finite type gives the uniform distribution.
    This connects Finset-based probability to MeasureTheory. -/
theorem counting_measure_is_uniform {α : Type*} [Fintype α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [Nonempty α] :
    (Measure.count : Measure α) Set.univ = Fintype.card α := by
  simp [Measure.count_apply_finite]

/-- The probability measure from uniform distribution on a finite type -/
noncomputable def uniformProbMeasure (α : Type*) [Fintype α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [Nonempty α] : Measure α :=
  (Fintype.card α : ℝ≥0∞)⁻¹ • Measure.count

-- ============================================================
-- PART II: Expectation Bridge
-- ============================================================

/-- Finset-based expectation matches measure-theoretic integral
    for uniform distribution on a finite type. -/
theorem finset_expectation_eq_integral {α : Type*} [Fintype α]
    [MeasurableSpace α] [MeasurableSingletonClass α] [Nonempty α]
    (X : α → ℝ) :
    (∑ a : α, X a) / Fintype.card α =
    ∫ a, X a ∂(uniformProbMeasure α) := by
  sorry

-- ============================================================
-- PART III: First Moment Method via MeasureTheory
-- ============================================================

/-- The first moment method: if E[X] < 1, then P(X = 0) > 0.
    This is the core of the probabilistic method.
    In measure-theoretic language: if ∫ X dP < 1 and X ≥ 0 integer-valued,
    then μ({X = 0}) > 0. -/
theorem first_moment_method {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℕ) (hX_meas : Measurable X)
    (hX_int : ∫ ω, (X ω : ℝ) ∂μ < 1) :
    0 < μ {ω | X ω = 0} := by
  sorry

-- ============================================================
-- PART IV: Linearity of Expectation (Measure-Theoretic)
-- ============================================================

/-- Linearity of expectation is just integral_add in MeasureTheory.
    This trivially holds for integrable functions. -/
theorem linearity_of_expectation {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X Y : Ω → ℝ) (hX : Integrable X μ) (hY : Integrable Y μ) :
    ∫ ω, (X ω + Y ω) ∂μ = ∫ ω, X ω ∂μ + ∫ ω, Y ω ∂μ :=
  integral_add hX hY

-- ============================================================
-- PART V: Indicator Random Variables
-- ============================================================

/-- An indicator random variable for a measurable set. -/
noncomputable def indicatorRV {Ω : Type*} [MeasurableSpace Ω]
    (A : Set Ω) : Ω → ℝ :=
  A.indicator (fun _ => 1)

/-- The expectation of an indicator is the probability of the event. -/
theorem expectation_indicator {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (A : Set Ω) (hA : MeasurableSet A) :
    ∫ ω, indicatorRV A ω ∂μ = (μ A).toReal := by
  simp [indicatorRV, integral_indicator hA]

end ProbMethodExpectationOQ01
