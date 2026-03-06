import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic

/-
# Dirichlet Function Integral via Almost Everywhere Zero

## What This Proves

The Dirichlet function 𝟙_ℚ (indicator of the rationals) has Lebesgue integral 0
over [0,1]. This is the canonical example showing Lebesgue integration handles
functions that are not Riemann integrable.

## Proof Strategy

1. ℚ is countable, hence its image in ℝ has Lebesgue measure zero
2. The indicator function 𝟙_ℚ equals zero almost everywhere (on irrationals)
3. An a.e. zero function has integral zero (via integral_eq_zero_of_ae)

## Context

This resolves the axiom `dirichlet_integral_zero` in LebesgueMeasure.lean,
replacing it with a complete proof from Mathlib primitives.

## Open Question Origin

From the Lebesgue Measure gallery proof (lebesgue-measure):
"Can the Dirichlet function integral axiom be replaced by a full proof
using Mathlib's integral_eq_zero_of_ae and the countability of ℚ?"

Answer: YES. This file provides the complete proof.
-/

open MeasureTheory Measure Set Filter

namespace LebesgueMeasureOQ01

/-
## Part I: Measure Zero Properties
-/

/-- The image of ℚ in ℝ (via Rat.cast) is countable. -/
theorem rationals_countable : (Set.range (Rat.cast : ℚ → ℝ)).Countable :=
  Set.countable_range _

/-- ℚ embedded in ℝ has Lebesgue measure zero. -/
theorem rationals_measure_zero :
    volume (Set.range (Rat.cast : ℚ → ℝ)) = 0 :=
  rationals_countable.measure_zero volume

/-- Any subset of a measure-zero set has measure zero (for complete measures). -/
theorem subset_of_null_has_measure_zero {s t : Set ℝ}
    (hst : s ⊆ t) (ht : volume t = 0) :
    volume s = 0 :=
  le_antisymm (le_trans (measure_mono hst) (le_of_eq ht)) (zero_le _)

/-
## Part II: The Dirichlet Function
-/

/-- The Dirichlet function: 1 on rationals, 0 on irrationals.
    Defined as the indicator function of the rationals in ℝ. -/
noncomputable def dirichletFunction : ℝ → ℝ :=
  Set.indicator (Set.range (Rat.cast : ℚ → ℝ)) (fun _ => (1 : ℝ))

/-- The Dirichlet function is zero outside ℚ. -/
theorem dirichletFunction_eq_zero_of_irrational {x : ℝ}
    (hx : x ∉ Set.range (Rat.cast : ℚ → ℝ)) :
    dirichletFunction x = 0 :=
  Set.indicator_of_notMem hx _

/-- The Dirichlet function is one on ℚ. -/
theorem dirichletFunction_eq_one_of_rational {x : ℝ}
    (hx : x ∈ Set.range (Rat.cast : ℚ → ℝ)) :
    dirichletFunction x = 1 :=
  Set.indicator_of_mem hx _

/-
## Part III: Almost Everywhere Zero
-/

/-- The Dirichlet function is zero almost everywhere with respect to
    Lebesgue measure. This is because ℚ has measure zero, so the set
    where the function is nonzero (namely ℚ) is negligible. -/
theorem dirichletFunction_ae_zero :
    ∀ᵐ x ∂(volume : Measure ℝ), dirichletFunction x = 0 := by
  have hmz : volume (Set.range (Rat.cast : ℚ → ℝ)) = 0 := rationals_measure_zero
  filter_upwards [compl_mem_ae_iff.mpr hmz] with x hx
  exact Set.indicator_of_notMem hx _

/-- The Dirichlet function is zero a.e. restricted to [0,1]. -/
theorem dirichletFunction_ae_zero_restrict :
    ∀ᵐ x ∂(volume.restrict (Icc (0:ℝ) 1)), dirichletFunction x = 0 := by
  apply ae_restrict_of_ae
  exact dirichletFunction_ae_zero

/-
## Part IV: The Main Theorem
-/

/-- **Main Theorem**: The Lebesgue integral of the Dirichlet function over [0,1] is zero.

    ∫ x in [0,1], 𝟙_ℚ(x) dλ = 0

    This is the canonical example demonstrating that Lebesgue integration
    handles functions not integrable in the Riemann sense.

    The Dirichlet function oscillates between 0 and 1 at every point,
    making Riemann upper sums = 1 and lower sums = 0 always.
    But since ℚ has Lebesgue measure zero, the function is almost
    everywhere zero, and the Lebesgue integral captures this. -/
theorem dirichlet_integral_zero :
    ∫ x in Icc (0:ℝ) 1,
      Set.indicator (Set.range (Rat.cast : ℚ → ℝ)) (fun _ => (1:ℝ)) x ∂volume = 0 := by
  apply integral_eq_zero_of_ae
  exact dirichletFunction_ae_zero_restrict

/-- Alternative formulation using our named function. -/
theorem dirichlet_integral_zero' :
    ∫ x in Icc (0:ℝ) 1, dirichletFunction x ∂volume = 0 := by
  exact dirichlet_integral_zero

/-
## Part V: Extensions
-/

/-- The integral of the Dirichlet function over ANY measurable set is zero. -/
theorem dirichlet_integral_zero_on_any_set (s : Set ℝ) :
    ∫ x in s, dirichletFunction x ∂volume = 0 := by
  apply integral_eq_zero_of_ae
  apply ae_restrict_of_ae
  exact dirichletFunction_ae_zero

/-- The integral of the Dirichlet function over all of ℝ is zero. -/
theorem dirichlet_integral_zero_univ :
    ∫ x, dirichletFunction x ∂volume = 0 := by
  apply integral_eq_zero_of_ae
  exact dirichletFunction_ae_zero

/-- The Dirichlet function is NOT Riemann integrable (informally stated).
    We state this as: the function takes value 1 on a dense set and
    0 on a dense set, so upper and lower Riemann sums never agree.

    Formally, we prove the function is not continuous at any point,
    which implies it's not Riemann integrable (its set of discontinuities
    is all of ℝ, which has positive measure). -/
theorem dirichletFunction_not_continuous_at (x : ℝ) :
    ¬ ContinuousAt dirichletFunction x := by
  intro h
  by_cases hx : x ∈ Set.range (Rat.cast : ℚ → ℝ)
  · -- x is rational, so dirichletFunction x = 1
    -- But near x there are irrationals where the function is 0
    have hval : dirichletFunction x = 1 := Set.indicator_of_mem hx _
    rw [Metric.continuousAt_iff] at h
    obtain ⟨δ, hδ_pos, hδ⟩ := h 1 one_pos
    -- There exists an irrational in (x - δ, x + δ)
    have : ∃ y, y ∈ Metric.ball x δ ∧ y ∉ Set.range (Rat.cast : ℚ → ℝ) := by
      -- The ball has positive measure, but ℚ has measure zero, so there must be irrationals
      by_contra h_all_rat
      push_neg at h_all_rat
      -- Every point in the ball is rational
      have hball_sub : Metric.ball x δ ⊆ Set.range (Rat.cast : ℚ → ℝ) := h_all_rat
      -- But the ball has positive measure
      have hball_pos : 0 < volume (Metric.ball x δ) := by
        rw [Real.volume_ball]
        exact ENNReal.ofReal_pos.mpr (by linarith)
      -- And ℚ has measure zero - contradiction
      have : volume (Metric.ball x δ) ≤ volume (Set.range (Rat.cast : ℚ → ℝ)) :=
        measure_mono hball_sub
      rw [rationals_measure_zero] at this
      exact absurd hball_pos (not_lt.mpr this)
    obtain ⟨y, hy_ball, hy_irr⟩ := this
    have hy_val : dirichletFunction y = 0 := Set.indicator_of_notMem hy_irr _
    have hy_dist := hδ hy_ball
    rw [hval, hy_val] at hy_dist
    simp at hy_dist
  · -- x is irrational, so dirichletFunction x = 0
    -- But near x there are rationals where the function is 1
    have hval : dirichletFunction x = 0 := Set.indicator_of_notMem hx _
    rw [Metric.continuousAt_iff] at h
    obtain ⟨δ, hδ_pos, hδ⟩ := h 1 one_pos
    -- There exists a rational in (x - δ, x + δ)
    have : ∃ y, y ∈ Metric.ball x δ ∧ y ∈ Set.range (Rat.cast : ℚ → ℝ) := by
      obtain ⟨q, hq⟩ := exists_rat_near x (by linarith : (0 : ℝ) < δ / 2)
      refine ⟨↑q, ?_, Set.mem_range.mpr ⟨q, rfl⟩⟩
      rw [Metric.mem_ball, Real.dist_eq]
      rw [abs_sub_comm] at hq
      calc |↑q - x| < δ / 2 := hq
        _ < δ := by linarith
    obtain ⟨y, hy_ball, hy_rat⟩ := this
    have hy_val : dirichletFunction y = 1 := Set.indicator_of_mem hy_rat _
    have hy_dist := hδ hy_ball
    rw [hval, hy_val] at hy_dist
    simp at hy_dist

end LebesgueMeasureOQ01
