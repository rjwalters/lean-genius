import Mathlib

/-
# The Arcsine Law — density, derivative, and FTC normalization

## Research Problem: ballot-problem-oq-02-oq-03
"Arcsine Law Axiomatization in Lean."

## Context

Lévy's Arcsine Law is the continuous-time culmination of the ballot problem.
For a standard Brownian motion on `[0, 1]`, the occupation time of the positive
half-line, the time of the maximum, and the time of the last zero all share the
**arcsine distribution** on `[0, 1]`, with cumulative distribution function

      F(x) = (2/π) · arcsin(√x),        x ∈ [0, 1],

and density

      f(x) = 1 / (π · √(x(1-x))),       x ∈ (0, 1).

The graduated sibling `BallotProblemOQ02OQ04.lean` ("The Arcsine Distribution:
verified core") establishes the *static* analytic facts about `F` and `f`:
the endpoints `F 0 = 0`, `F 1 = 1`, the median `F (1/2) = 1/2`, monotonicity,
the reflection symmetry `F x + F (1-x) = 1`, and the U-shape of `f`. In that file
the density `f` and the CDF `F` are introduced as *separate* objects, and the
fundamental link between them — that `f` is the derivative of `F`, hence that `f`
integrates to the total probability mass `1` — is left unproved.

## What this file adds (0 sorries, 0 axioms)

This file supplies exactly that missing link, axiom-free:

  * `arcsineCDF_hasDerivAt`        : `F' x = f x` for `x ∈ (0,1)` — the density is the
                                     genuine derivative of the CDF (chain rule through
                                     `Real.arcsin` and `Real.sqrt`);
  * `arcsineDensity_continuousOn`  : `f` is continuous on every `[a,b] ⊂ (0,1)`;
  * `arcsineDensity_intervalIntegral`
                                   : `∫ x in a..b, f x = F b - F a` for `0 < a ≤ b < 1`
                                     (Fundamental Theorem of Calculus);
  * `arcsineCDF_continuous`        : `F` is continuous on all of `ℝ`;
  * `arcsineDensity_symmetric_integral_tendsto_one`
                                   : the symmetric exhausting integral
                                     `∫ x in a..(1-a), f x → 1` as `a → 0⁺`.

The last theorem is the **total-mass normalization**: it certifies that `f` is a
genuine probability density — its (improper) integral over `(0,1)` equals `1` —
obtained as the limit of the proper integrals over `[a, 1-a]` via the FTC and the
continuity of `F` at the endpoints. The density itself is unbounded at `0` and `1`,
so this is a genuinely improper integral; the symmetric exhaustion `[a, 1-a] ↑ (0,1)`
is the standard way to make sense of it.

The fully probabilistic statement (that these analytic facts describe the law of the
occupation time of an actual Brownian motion) requires Brownian local-time theory,
which Mathlib v4.26.0 does not yet contain; the parent `BallotProblemOQ02.lean`
axiomatizes the Brownian-motion facts it needs. This file commits to no such axioms.

## References
- Lévy (1939): *Sur certains processus stochastiques homogènes*.
- Karatzas–Shreve (1991): *Brownian Motion and Stochastic Calculus*, §6.3.
- Mörters–Peres (2010): *Brownian Motion*, §5.2 and Thm 5.28.
-/

namespace ArcsineLawDensity

open Real Set intervalIntegral
open scoped Topology

/-- The cumulative distribution function of the arcsine law on `[0,1]`:
    `F(x) = (2/π) · arcsin(√x)`. -/
noncomputable def arcsineCDF (x : ℝ) : ℝ := (2 / π) * arcsin (Real.sqrt x)

/-- The arcsine density on `(0,1)`: `f(x) = 1 / (π · √(x(1-x)))`. -/
noncomputable def arcsineDensity (x : ℝ) : ℝ := 1 / (π * Real.sqrt (x * (1 - x)))

/-! ### The density is the derivative of the CDF -/

/-- **The fundamental link**: on the open interval `(0,1)` the arcsine density `f`
    is the derivative of the arcsine CDF `F`. This is the chain rule applied to
    `F = (2/π) · arcsin ∘ √`, with `(arcsin)'(√x) = 1/√(1-x)` and `(√)'(x) = 1/(2√x)`,
    recombined via `√x · √(1-x) = √(x(1-x))`. -/
theorem arcsineCDF_hasDerivAt {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    HasDerivAt arcsineCDF (arcsineDensity x) x := by
  have hxne : x ≠ 0 := ne_of_gt hx0
  have hsqx_nonneg : (0 : ℝ) ≤ Real.sqrt x := Real.sqrt_nonneg x
  have hsqx_pos : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.mpr hx0
  -- `√x ≠ 1` because `x < 1`, and `√x ≠ -1` because `√x ≥ 0`.
  have hsx_ne_one : Real.sqrt x ≠ 1 := by
    intro h
    have : x = 1 := by
      have := Real.sq_sqrt hx0.le
      rw [h] at this; simpa using this.symm
    exact (ne_of_lt hx1) this
  have hsx_ne_negone : Real.sqrt x ≠ -1 := by
    intro h; rw [h] at hsqx_nonneg; norm_num at hsqx_nonneg
  -- Derivative of `arcsin` at `√x`.
  have harcsin : HasDerivAt arcsin (1 / Real.sqrt (1 - (Real.sqrt x) ^ 2)) (Real.sqrt x) :=
    Real.hasDerivAt_arcsin hsx_ne_negone hsx_ne_one
  -- Derivative of `√` at `x`.
  have hsqrt : HasDerivAt (fun y => Real.sqrt y) (1 / (2 * Real.sqrt x)) x :=
    Real.hasDerivAt_sqrt hxne
  -- Compose, then scale by `2/π`.
  have hcomp := harcsin.comp x hsqrt
  have hscaled := hcomp.const_mul (2 / π)
  -- `arcsineCDF` is definitionally `(2/π) * (arcsin ∘ √)`.
  have hfun : arcsineCDF = fun y => (2 / π) * (arcsin ∘ fun y => Real.sqrt y) y := by
    funext y; simp [arcsineCDF, Function.comp]
  rw [hfun]
  -- Now identify the derivative value with `arcsineDensity x`.
  convert hscaled using 1
  -- Goal: arcsineDensity x = (2/π) * ((1/√(1-(√x)^2)) * (1/(2√x)))
  have hsq : (Real.sqrt x) ^ 2 = x := Real.sq_sqrt hx0.le
  rw [hsq]
  have h1x : (0 : ℝ) < 1 - x := by linarith
  have hs1x_pos : (0 : ℝ) < Real.sqrt (1 - x) := Real.sqrt_pos.mpr h1x
  have hpi : (0 : ℝ) < π := Real.pi_pos
  have hprod : Real.sqrt (x * (1 - x)) = Real.sqrt x * Real.sqrt (1 - x) :=
    Real.sqrt_mul hx0.le _
  rw [arcsineDensity, hprod]
  field_simp

/-! ### Continuity and interval integrability of the density -/

/-- The density `f` is continuous on every closed subinterval `[a,b] ⊂ (0,1)`.
    (It blows up at the endpoints `0` and `1`, so global continuity fails there.) -/
theorem arcsineDensity_continuousOn {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b < 1) :
    ContinuousOn arcsineDensity (uIcc a b) := by
  have huIcc : uIcc a b = Icc a b := Set.uIcc_of_le hab
  rw [huIcc]
  apply ContinuousOn.div continuousOn_const
  · -- `x ↦ π * √(x(1-x))` is continuous
    exact continuousOn_const.mul
      ((Real.continuous_sqrt.comp
        (continuous_id.mul (continuous_const.sub continuous_id))).continuousOn)
  · -- and nonzero on `[a,b]`, since `x(1-x) > 0` there
    intro x hx
    obtain ⟨hxa, hxb⟩ := hx
    have hx0 : 0 < x := lt_of_lt_of_le ha hxa
    have hx1 : x < 1 := lt_of_le_of_lt hxb hb
    have hpos : 0 < x * (1 - x) := mul_pos hx0 (by linarith)
    have : 0 < Real.sqrt (x * (1 - x)) := Real.sqrt_pos.mpr hpos
    positivity

/-- The density `f` is interval-integrable on every `[a,b] ⊂ (0,1)`. -/
theorem arcsineDensity_intervalIntegrable {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b < 1) :
    IntervalIntegrable arcsineDensity MeasureTheory.volume a b :=
  (arcsineDensity_continuousOn ha hab hb).intervalIntegrable

/-! ### Fundamental Theorem of Calculus on subintervals -/

/-- **FTC for the arcsine law**: on any `[a,b] ⊂ (0,1)`, the integral of the density
    recovers the increment of the CDF, `∫ₐᵇ f = F b - F a`. -/
theorem arcsineDensity_intervalIntegral {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hb : b < 1) :
    ∫ x in a..b, arcsineDensity x = arcsineCDF b - arcsineCDF a := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro x hx
    rw [Set.uIcc_of_le hab] at hx
    obtain ⟨hxa, hxb⟩ := hx
    exact arcsineCDF_hasDerivAt (lt_of_lt_of_le ha hxa) (lt_of_le_of_lt hxb hb)
  · exact arcsineDensity_intervalIntegrable ha hab hb

/-! ### Continuity of the CDF and total-mass normalization -/

/-- The CDF `F = (2/π)·arcsin(√·)` is continuous on all of `ℝ`
    (`Real.arcsin` and `Real.sqrt` are continuous everywhere). -/
theorem arcsineCDF_continuous : Continuous arcsineCDF := by
  unfold arcsineCDF
  exact continuous_const.mul (Real.continuous_arcsin.comp Real.continuous_sqrt)

@[simp] theorem arcsineCDF_zero : arcsineCDF 0 = 0 := by
  simp [arcsineCDF]

@[simp] theorem arcsineCDF_one : arcsineCDF 1 = 1 := by
  rw [arcsineCDF, Real.sqrt_one, Real.arcsin_one]
  field_simp

/-- **Total-mass normalization (improper integral).** The density `f` is unbounded at
    `0` and `1`, but its symmetric exhausting integral over `[a, 1-a]` converges to the
    total probability mass `1` as `a → 0⁺`:

        `∫ x in a..(1-a), f x  →  1`.

    This certifies `f` as a genuine probability density of a law supported on `[0,1]`.
    The proof combines the FTC increment `F (1-a) - F a` with the continuity of `F` at
    the endpoints (`F 0 = 0`, `F 1 = 1`). -/
theorem arcsineDensity_symmetric_integral_tendsto_one :
    Filter.Tendsto (fun a => ∫ x in a..(1 - a), arcsineDensity x)
      (𝓝[>] 0) (𝓝 1) := by
  -- On `(0, 1/2)` the symmetric integral equals `F (1-a) - F a`.
  have hEq : (fun a => ∫ x in a..(1 - a), arcsineDensity x)
      =ᶠ[𝓝[>] 0] (fun a => arcsineCDF (1 - a) - arcsineCDF a) := by
    have hmem : Set.Ioo (0 : ℝ) (1 / 2) ∈ 𝓝[>] (0 : ℝ) := by
      rw [← Set.Ioi_inter_Iio]
      exact Filter.inter_mem self_mem_nhdsWithin
        (mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (by norm_num)))
    filter_upwards [hmem] with a ha
    obtain ⟨ha0, ha2⟩ := ha
    exact arcsineDensity_intervalIntegral ha0 (by linarith) (by linarith)
  rw [Filter.tendsto_congr' hEq]
  -- `F (1-a) - F a → F 1 - F 0 = 1 - 0 = 1` by continuity of `F`.
  have hlim : Filter.Tendsto (fun a => arcsineCDF (1 - a) - arcsineCDF a)
      (𝓝[>] 0) (𝓝 (arcsineCDF 1 - arcsineCDF 0)) := by
    apply Filter.Tendsto.mono_left _ nhdsWithin_le_nhds
    have h1 : Filter.Tendsto (fun a : ℝ => arcsineCDF (1 - a)) (𝓝 0) (𝓝 (arcsineCDF 1)) := by
      have hsub : Filter.Tendsto (fun a : ℝ => (1 : ℝ) - a) (𝓝 0) (𝓝 1) := by
        have hc : Continuous (fun a : ℝ => (1 : ℝ) - a) := continuous_const.sub continuous_id
        simpa using hc.tendsto 0
      exact (arcsineCDF_continuous.tendsto 1).comp hsub
    have h2 : Filter.Tendsto (fun a : ℝ => arcsineCDF a) (𝓝 0) (𝓝 (arcsineCDF 0)) :=
      arcsineCDF_continuous.tendsto 0
    exact h1.sub h2
  rw [arcsineCDF_one, arcsineCDF_zero] at hlim
  simpa using hlim

end ArcsineLawDensity
