/-
  AWGN second-moment identity:  E[Y²] = P + N  for  Y = X + Z

  Open question (shannon-channel-coding-awgn-oq-02):
  "Derive E[Y²] = P + N for Y = X + Z with independent zero-mean X (power P) and
   noise Z (power N) from Mathlib's variance/independence API, removing it as a
   converse hypothesis in the parent AWGN capacity proof."

  Context.  The parent file `ShannonChannelCodingAWGN` proves the AWGN capacity
  C(P,N) = ½ log(1 + P/N).  Its converse bound `awgn_capacity_upper_bound` takes
  the average-power relation E[Y²] = P + N as the bare hypothesis `hvar`
  (`∫ x, x² · f x ≤ P + N`).  That relation is the standard *variance of a sum of
  independent variables* fact:

        Y = X + Z,  X ⟂ Z,  E[X] = E[Z] = 0
        ⟹  E[Y²] = E[X²] + 2·E[X·Z] + E[Z²] = E[X²] + E[Z²] = P + N,

  because independence forces the cross term E[X·Z] = E[X]·E[Z] = 0.

  This file discharges that fact axiom-free from Mathlib's probability API.  The
  random variables X, Z live on an arbitrary probability space and are only
  assumed square-integrable (`MemLp · 2`), independent, and centered.  The three
  ingredients are:

    * `ProbabilityTheory.variance_eq_sub`     :  Var[X] = E[X²] − E[X]²
    * `ProbabilityTheory.IndepFun.variance_add`:  Var[X+Z] = Var[X] + Var[Z]
    * `ProbabilityTheory.IndepFun.integral_mul`:  E[X·Z] = E[X]·E[Z]

  The headline `awgn_output_power` states E[Y²] = P + N with P = E[X²], N = E[Z²],
  exactly the quantity assumed in the parent converse.
-/

import Mathlib

namespace ShannonAWGNPower

open MeasureTheory ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- For a centered square-integrable variable the second moment *is* the variance:
    `E[X²] = Var[X]` when `E[X] = 0`.  This is the bridge between the "power"
    `E[X²]` used in the AWGN converse and Mathlib's `variance`. -/
theorem secondMoment_eq_variance_of_mean_zero {X : Ω → ℝ}
    (hX : MemLp X 2 μ) (hEX : μ[X] = 0) :
    μ[X ^ 2] = variance X μ := by
  rw [variance_eq_sub hX, hEX]
  ring

omit [IsProbabilityMeasure μ] in
/-- **Independence kills the cross moment.**  For independent, centered,
    square-integrable `X` and `Z` one has `E[X·Z] = E[X]·E[Z] = 0`.  This is the
    only place independence enters the second-moment identity. -/
theorem indep_cross_moment_zero {X Z : Ω → ℝ}
    (hX : MemLp X 2 μ) (hZ : MemLp Z 2 μ) (hindep : IndepFun X Z μ)
    (hEX : μ[X] = 0) (hEZ : μ[Z] = 0) :
    μ[X * Z] = 0 := by
  rw [hindep.integral_mul_eq_mul_integral hX.aestronglyMeasurable
      hZ.aestronglyMeasurable, hEX, hEZ, mul_zero]

/-- **Second-moment additivity.**  For independent, centered, square-integrable
    inputs the second moment of the sum splits:
    `E[(X+Z)²] = E[X²] + E[Z²]`.  This is the variance-of-a-sum law specialised to
    the additive-noise channel `Y = X + Z`. -/
theorem awgn_second_moment_sum {X Z : Ω → ℝ}
    (hX : MemLp X 2 μ) (hZ : MemLp Z 2 μ) (hindep : IndepFun X Z μ)
    (hEX : μ[X] = 0) (hEZ : μ[Z] = 0) :
    μ[(X + Z) ^ 2] = μ[X ^ 2] + μ[Z ^ 2] := by
  have hXint : Integrable X μ := hX.integrable (by norm_num)
  have hZint : Integrable Z μ := hZ.integrable (by norm_num)
  -- The mean of the sum vanishes.
  have hmean : μ[X + Z] = 0 := by
    simp only [Pi.add_apply]
    rw [integral_add hXint hZint, hEX, hEZ, add_zero]
  -- Variance of a sum of independent variables is additive.
  have hv := hindep.variance_add hX hZ
  rw [variance_eq_sub (hX.add hZ), variance_eq_sub hX, variance_eq_sub hZ] at hv
  -- All three mean-square terms collapse since every mean is zero.
  rw [hmean, hEX, hEZ] at hv
  simpa using hv

/-- **AWGN output power.**  The headline identity `E[Y²] = P + N` for the additive
    channel `Y = X + Z`, where `P = E[X²]` is the signal power and `N = E[Z²]` the
    noise power.  Discharges the bare hypothesis `hvar` of the parent converse
    `ShannonAWGN.awgn_capacity_upper_bound` from independence and zero mean. -/
theorem awgn_output_power {X Z : Ω → ℝ} {P N : ℝ}
    (hX : MemLp X 2 μ) (hZ : MemLp Z 2 μ) (hindep : IndepFun X Z μ)
    (hEX : μ[X] = 0) (hEZ : μ[Z] = 0)
    (hP : μ[X ^ 2] = P) (hN : μ[Z ^ 2] = N) :
    μ[(X + Z) ^ 2] = P + N := by
  rw [awgn_second_moment_sum hX hZ hindep hEX hEZ, hP, hN]

/-- The same output power expressed through `variance`: `Var[Y] = P + N`.  Under
    the zero-mean assumption the variance and the second moment of `Y` agree, so
    this is just `awgn_output_power` read in variance form. -/
theorem awgn_output_variance {X Z : Ω → ℝ} {P N : ℝ}
    (hX : MemLp X 2 μ) (hZ : MemLp Z 2 μ) (hindep : IndepFun X Z μ)
    (hEX : μ[X] = 0) (hEZ : μ[Z] = 0)
    (hP : μ[X ^ 2] = P) (hN : μ[Z ^ 2] = N) :
    variance (X + Z) μ = P + N := by
  have hmean : μ[X + Z] = 0 := by
    have hXint : Integrable X μ := hX.integrable (by norm_num)
    have hZint : Integrable Z μ := hZ.integrable (by norm_num)
    simp only [Pi.add_apply]
    rw [integral_add hXint hZint, hEX, hEZ, add_zero]
  rw [← secondMoment_eq_variance_of_mean_zero (hX.add hZ) hmean]
  exact awgn_output_power hX hZ hindep hEX hEZ hP hN

end ShannonAWGNPower
