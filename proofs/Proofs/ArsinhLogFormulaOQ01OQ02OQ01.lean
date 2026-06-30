/-
# Antiderivative of `1/√(t² − 1)`: the `arcosh` calculus capstone

Research: arsinh-log-formula-oq-01-oq-02-oq-01
Parent:   arsinh-log-formula-oq-01-oq-02 (logarithmic form + addition law of `arcosh`)

The parent entry established the algebraic theory of `Real.arcosh` — its
logarithmic closed form `arcosh t = log(t + √(t² − 1))`, the addition /
subtraction / doubling laws, and concrete values `arcosh (5/4) = log 2`,
`arcosh (5/3) = log 3`.  A sibling open question supplied the calculus side for
`arsinh`: that `arsinh` is an antiderivative of `1/√(1 + t²)`.

This file supplies the **`cosh`-side calculus counterpart**: that `arcosh` is an
antiderivative of `1/√(t² − 1)` on the domain `t > 1`, where the radicand is
positive.  Concretely it provides:

* `hasDerivAt_arcosh` — the antiderivative fact
  `HasDerivAt Real.arcosh (1/√(t² − 1)) t` for `t > 1`.  **Mathlib's `Arcosh`
  file has no derivative lemma at all**, so this is built from scratch by
  differentiating the logarithmic form via the chain rule.
* `deriv_arcosh` — the same as a `deriv` equation.
* `integral_one_div_sqrt_sq_sub_one` — the Fundamental Theorem of Calculus
  evaluation `∫_a^b 1/√(t² − 1) dt = arcosh b − arcosh a` for `1 < a, b`.
* `integral_eq_log_sub_log` — its logarithmic closed form.
* `integral_five_quarters_to_five_thirds` — the concrete value
  `∫_{5/4}^{5/3} 1/√(t² − 1) dt = log (3/2)`, reusing the parent's evaluations.

All results are `0`-axiom and machine-checked.  Unlike the `arsinh` companion,
which restates Mathlib's `Real.hasDerivAt_arsinh`, the derivative here is genuinely
new: Mathlib provides `Real.arcosh` and its inverse facts but no derivative.
-/
import Mathlib

namespace ArsinhLogFormulaOQ01OQ02OQ01

open Real intervalIntegral MeasureTheory

/-- For `t > 1` the radicand `t² − 1` is strictly positive, hence `√(t² − 1) > 0`. -/
theorem sqrt_sq_sub_one_pos {x : ℝ} (hx : 1 < x) : 0 < Real.sqrt (x ^ 2 - 1) :=
  Real.sqrt_pos.mpr (by nlinarith)

/-- **Antiderivative fact (the open question).** `arcosh` is an antiderivative of
`1/√(t² − 1)` on `(1, ∞)`: `HasDerivAt Real.arcosh (1/√(t² − 1)) t` for `t > 1`.

Mathlib's `Mathlib.Analysis.SpecialFunctions.Arcosh` defines `Real.arcosh` and
records its inverse facts (`cosh_arcosh`, `sinh_arcosh`, …) but supplies **no
derivative lemma**.  We build it directly from the logarithmic form
`arcosh t = log(t + √(t² − 1))` by the chain rule:

* `d/dt √(t² − 1) = t/√(t² − 1)`,
* so `d/dt (t + √(t² − 1)) = (√(t² − 1) + t)/√(t² − 1)`,
* and `arcosh' t = [d/dt (t + √(t² − 1))] / (t + √(t² − 1)) = 1/√(t² − 1)`,

the last step because the numerator equals `t + √(t² − 1)`, the denominator. -/
theorem hasDerivAt_arcosh {x : ℝ} (hx : 1 < x) :
    HasDerivAt Real.arcosh (1 / Real.sqrt (x ^ 2 - 1)) x := by
  have hpos : (0 : ℝ) < x ^ 2 - 1 := by nlinarith
  have hs : (0 : ℝ) < Real.sqrt (x ^ 2 - 1) := Real.sqrt_pos.mpr hpos
  have hg : (0 : ℝ) < x + Real.sqrt (x ^ 2 - 1) := by linarith [hs]
  -- derivative of the inner polynomial `t² − 1`
  have h1 : HasDerivAt (fun y : ℝ => y ^ 2 - 1) (2 * x) x := by
    simpa using (hasDerivAt_pow 2 x).sub_const 1
  -- chain rule through `√·`
  have h2 : HasDerivAt (fun y : ℝ => Real.sqrt (y ^ 2 - 1))
      (2 * x / (2 * Real.sqrt (x ^ 2 - 1))) x := h1.sqrt hpos.ne'
  -- add the identity term
  have h3 : HasDerivAt (fun y : ℝ => y + Real.sqrt (y ^ 2 - 1))
      (1 + 2 * x / (2 * Real.sqrt (x ^ 2 - 1))) x := (hasDerivAt_id x).add h2
  -- chain rule through `log·`; the function is definitionally `arcosh`
  have h4 : HasDerivAt (fun y : ℝ => Real.log (y + Real.sqrt (y ^ 2 - 1)))
      ((1 + 2 * x / (2 * Real.sqrt (x ^ 2 - 1))) / (x + Real.sqrt (x ^ 2 - 1))) x :=
    h3.log hg.ne'
  -- the messy derivative collapses to `1/√(x² − 1)` (no `√·² = ·` needed)
  have hval : (1 + 2 * x / (2 * Real.sqrt (x ^ 2 - 1))) / (x + Real.sqrt (x ^ 2 - 1))
      = 1 / Real.sqrt (x ^ 2 - 1) := by
    field_simp
    ring
  rw [hval] at h4
  exact h4

/-- The `deriv` form of the antiderivative fact: `(arcosh)' t = 1/√(t² − 1)` for `t > 1`. -/
theorem deriv_arcosh {x : ℝ} (hx : 1 < x) :
    deriv Real.arcosh x = 1 / Real.sqrt (x ^ 2 - 1) :=
  (hasDerivAt_arcosh hx).deriv

/-- On any interval `[a, b] ⊂ (1, ∞)` the integrand `t ↦ 1/√(t² − 1)` is
continuous (the denominator stays strictly positive). -/
theorem continuousOn_integrand {a b : ℝ} (ha : 1 < a) (hb : 1 < b) :
    ContinuousOn (fun t : ℝ => 1 / Real.sqrt (t ^ 2 - 1)) (Set.uIcc a b) := by
  apply ContinuousOn.div continuousOn_const
  · exact (Real.continuous_sqrt.comp (by continuity)).continuousOn
  · intro t ht
    have h1t : 1 < t := by
      rcases Set.mem_uIcc.mp ht with ⟨h, _⟩ | ⟨h, _⟩ <;> linarith
    exact (sqrt_sq_sub_one_pos h1t).ne'

/-- Consequently the integrand is interval-integrable on `[a, b] ⊂ (1, ∞)`. -/
theorem intervalIntegrable_integrand {a b : ℝ} (ha : 1 < a) (hb : 1 < b) :
    IntervalIntegrable (fun t : ℝ => 1 / Real.sqrt (t ^ 2 - 1)) volume a b :=
  (continuousOn_integrand ha hb).intervalIntegrable

/-- **Fundamental Theorem of Calculus for `arcosh`.**
`∫_a^b 1/√(t² − 1) dt = arcosh b − arcosh a` for `1 < a, b`.

This is the definite-integral incarnation of the antiderivative `arcosh`, and the
precise meaning of "`∫ 1/√(t² − 1) dt = arcosh t + C`" on `(1, ∞)`. -/
theorem integral_one_div_sqrt_sq_sub_one {a b : ℝ} (ha : 1 < a) (hb : 1 < b) :
    ∫ t in a..b, 1 / Real.sqrt (t ^ 2 - 1) = Real.arcosh b - Real.arcosh a := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro x hx
    have h1x : 1 < x := by
      rcases Set.mem_uIcc.mp hx with ⟨h, _⟩ | ⟨h, _⟩ <;> linarith
    exact hasDerivAt_arcosh h1x
  · exact intervalIntegrable_integrand ha hb

/-- **Logarithmic closed form of the integral.**
`∫_a^b 1/√(t² − 1) dt = log(b + √(b² − 1)) − log(a + √(a² − 1))`, obtained by
unfolding `arcosh` to its parent logarithmic form. -/
theorem integral_eq_log_sub_log {a b : ℝ} (ha : 1 < a) (hb : 1 < b) :
    ∫ t in a..b, 1 / Real.sqrt (t ^ 2 - 1) =
      Real.log (b + Real.sqrt (b ^ 2 - 1)) -
        Real.log (a + Real.sqrt (a ^ 2 - 1)) := by
  rw [integral_one_div_sqrt_sq_sub_one ha hb]
  rfl

/-- Helper evaluation: `arcosh (5/3) = log 3`, since `√((5/3)² − 1) = 4/3`. -/
theorem arcosh_five_thirds : Real.arcosh (5 / 3) = Real.log 3 := by
  have h : Real.sqrt ((5 / 3 : ℝ) ^ 2 - 1) = 4 / 3 := by
    rw [show ((5 / 3 : ℝ) ^ 2 - 1) = (4 / 3) ^ 2 by norm_num]
    exact Real.sqrt_sq (by norm_num)
  show Real.log ((5 / 3 : ℝ) + Real.sqrt ((5 / 3) ^ 2 - 1)) = Real.log 3
  rw [h, show (5 / 3 + 4 / 3 : ℝ) = 3 by norm_num]

/-- Helper evaluation: `arcosh (5/4) = log 2`, since `√((5/4)² − 1) = 3/4`. -/
theorem arcosh_five_quarters : Real.arcosh (5 / 4) = Real.log 2 := by
  have h : Real.sqrt ((5 / 4 : ℝ) ^ 2 - 1) = 3 / 4 := by
    rw [show ((5 / 4 : ℝ) ^ 2 - 1) = (3 / 4) ^ 2 by norm_num]
    exact Real.sqrt_sq (by norm_num)
  show Real.log ((5 / 4 : ℝ) + Real.sqrt ((5 / 4) ^ 2 - 1)) = Real.log 2
  rw [h, show (5 / 4 + 3 / 4 : ℝ) = 2 by norm_num]

/-- **Concrete evaluation.** `∫_{5/4}^{5/3} 1/√(t² − 1) dt = log (3/2)`,
combining the FTC statement with the parent's values `arcosh (5/3) = log 3` and
`arcosh (5/4) = log 2`. -/
theorem integral_five_quarters_to_five_thirds :
    ∫ t in (5 / 4 : ℝ)..(5 / 3), 1 / Real.sqrt (t ^ 2 - 1) = Real.log (3 / 2) := by
  rw [integral_one_div_sqrt_sq_sub_one (by norm_num) (by norm_num),
    arcosh_five_thirds, arcosh_five_quarters,
    Real.log_div (by norm_num) (by norm_num)]

end ArsinhLogFormulaOQ01OQ02OQ01
