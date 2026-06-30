/-
  AWGN second-moment identity:  E[Y²] = P + N

  Open question (shannon-channel-coding-awgn-oq-02):
  "Derive E[Y²] = P + N for Y = X + Z with independent zero-mean input X (power P)
   and noise Z (power N) from Mathlib's variance/independence API, removing it as a
   converse hypothesis in the parent AWGN capacity proof."

  In the parent file `ShannonChannelCodingAWGN.lean` the input/output power relation
  `E[Y²] = P + N` for an additive independent-noise channel is taken as the hypothesis
  `hvar` of the converse bound (it encodes the average-power constraint at the output).
  Here we discharge exactly that relation from Mathlib's probability layer.

  The mathematical content is the *variance-of-a-sum* fact specialised to zero-mean
  variables: for independent square-integrable `X, Z`,

        Var[X + Z] = Var[X] + Var[Z]            (independence kills the covariance)

  and when the means vanish the second moment coincides with the variance,

        E[X²] = Var[X],   E[Z²] = Var[Z],   E[(X+Z)²] = Var[X+Z],

  so the output power adds:  E[(X+Z)²] = E[X²] + E[Z²] = P + N.

  Everything is assembled from `ProbabilityTheory.IndepFun.variance_add` and
  `ProbabilityTheory.variance_eq_sub`; the file is axiom-free.
-/

import Mathlib

open MeasureTheory ProbabilityTheory
open scoped MeasureTheory ProbabilityTheory ENNReal

namespace ShannonAWGNSecondMoment

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- For a zero-mean square-integrable random variable the **second moment equals the
variance**: `E[X²] = Var[X]`.  This is the bridge that turns the "power" of a
zero-mean signal into its variance. -/
theorem second_moment_eq_variance [IsProbabilityMeasure μ] {X : Ω → ℝ}
    (hX : MemLp X 2 μ) (hX0 : μ[X] = 0) :
    μ[X ^ 2] = Var[X; μ] := by
  rw [variance_eq_sub hX, hX0]
  ring

/-- The output variance of an additive independent-noise channel is the sum of the
input and noise variances.  This is `IndepFun.variance_add`, recorded here in the
channel notation `Y = X + Z`. -/
theorem awgn_output_variance [IsProbabilityMeasure μ] {X Z : Ω → ℝ}
    (hX : MemLp X 2 μ) (hZ : MemLp Z 2 μ) (hindep : IndepFun X Z μ) :
    Var[X + Z; μ] = Var[X; μ] + Var[Z; μ] :=
  hindep.variance_add hX hZ

/-- **AWGN second-moment identity.**  If the channel output is `Y = X + Z` with the
input `X` and the noise `Z` independent, both zero-mean and square-integrable, then the
output second moment is the sum of the input and noise second moments:

        E[(X + Z)²] = E[X²] + E[Z²].

This is the variance-of-a-sum fact reduced to second moments via the zero-mean
hypotheses, and is exactly the relation the parent AWGN converse takes as `hvar`. -/
theorem awgn_second_moment [IsProbabilityMeasure μ] {X Z : Ω → ℝ}
    (hX : MemLp X 2 μ) (hZ : MemLp Z 2 μ) (hindep : IndepFun X Z μ)
    (hX0 : μ[X] = 0) (hZ0 : μ[Z] = 0) :
    μ[(X + Z) ^ 2] = μ[X ^ 2] + μ[Z ^ 2] := by
  have hXint : Integrable X μ := hX.integrable one_le_two
  have hZint : Integrable Z μ := hZ.integrable one_le_two
  -- the sum is again zero-mean
  have hmean : μ[X + Z] = 0 := by
    simp only [Pi.add_apply]
    rw [integral_add hXint hZint, hX0, hZ0, add_zero]
  -- variance additivity for the independent sum
  have hvar : Var[X + Z; μ] = Var[X; μ] + Var[Z; μ] := hindep.variance_add hX hZ
  -- expand each variance as second-moment minus squared-mean
  have e1 := variance_eq_sub (hX.add hZ)
  have e2 := variance_eq_sub hX
  have e3 := variance_eq_sub hZ
  have key : μ[(X + Z) ^ 2] - μ[X + Z] ^ 2
      = (μ[X ^ 2] - μ[X] ^ 2) + (μ[Z ^ 2] - μ[Z] ^ 2) := by
    rw [← e1, ← e2, ← e3]; exact hvar
  rw [hmean, hX0, hZ0] at key
  -- with all means zero the squared-mean terms drop out
  simpa using key

/-- **AWGN output power.**  Restated with the named powers `P = E[X²]` and `N = E[Z²]`:
the output power of the additive Gaussian channel is `P + N`.  This is the relation
exposed as the hypothesis `hvar` in the parent's converse bound. -/
theorem awgn_output_power [IsProbabilityMeasure μ] {X Z : Ω → ℝ}
    (hX : MemLp X 2 μ) (hZ : MemLp Z 2 μ) (hindep : IndepFun X Z μ)
    (hX0 : μ[X] = 0) (hZ0 : μ[Z] = 0) {P N : ℝ}
    (hP : μ[X ^ 2] = P) (hN : μ[Z ^ 2] = N) :
    μ[(X + Z) ^ 2] = P + N := by
  rw [awgn_second_moment hX hZ hindep hX0 hZ0, hP, hN]

end ShannonAWGNSecondMoment
