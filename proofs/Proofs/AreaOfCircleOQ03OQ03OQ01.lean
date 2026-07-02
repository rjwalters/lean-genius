import Mathlib

/-
# Area of a Circle, oq-03-oq-03-oq-01 — The Ellipse Area Formula, Rigorously

Parent entry `area-of-circle-oq-03-oq-03` ("Method of Exhaustion for Ellipses and
Parabolas") states the ellipse area `π·a·b`, but its Lean proof is — in its own
words — an *algebraic placeholder* (`ring`/`rfl`), asserting only tautologies like
`a*b*π = π*a*b`. Its first open question (`area-of-circle-oq-03-oq-03-oq-01`) asks:

> Prove the ellipse area formula rigorously using Mathlib's measure-theoretic
> change of variables. The `integral_comp_mul_right`/`MeasurePreserving` API may
> provide the right tools. The current proof is an algebraic placeholder.

This file supplies the rigorous proof, following exactly the suggested route:
the change-of-variables lemma `intervalIntegral.integral_comp_div`.

## What is proved

The area enclosed by the ellipse `x²/a² + y²/b² = 1` is the integral of its
vertical extent `2·b·√(1 − (x/a)²)` over `x ∈ [−a, a]`:

* `ellipse_halfheight_integral` — `∫ x in −a..a, √(1 − (x/a)²) = a·(π/2)`, obtained
  from Mathlib's unit-circle integral `∫_{−1}^{1} √(1 − x²) = π/2`
  (`integral_sqrt_one_sub_sq`) by the substitution `x ↦ x/a`
  (`intervalIntegral.integral_comp_div`). This is the genuine change of variables.
* `ellipse_area_integral` — `∫ x in −a..a, 2·b·√(1 − (x/a)²) = π·a·b`, the ellipse
  area formula.
* `circle_area_special` — specialising `a = b = r` recovers `π·r²`, the area of a
  disc of radius `r`.
* `ellipse_area_pos` — the area is positive for `a, b > 0`.

Every step is a real integral computation; nothing is a tautological placeholder.
Fully machine-checked, no axioms beyond Mathlib's foundations, no `native_decide`.

Tags: geometry, ellipse, area, integral, change-of-variables, method-of-exhaustion
-/

namespace AreaOfCircleOQ03OQ03OQ01

open Real MeasureTheory intervalIntegral

/-- **Half-height integral of the ellipse via change of variables.** The integral
of the normalized half-height `√(1 − (x/a)²)` over `[−a, a]` equals `a·(π/2)`. This
is the crux: the substitution `x ↦ x/a` (`intervalIntegral.integral_comp_div`)
reduces it to Mathlib's unit-circle integral `∫_{−1}^{1} √(1 − x²) = π/2`. -/
theorem ellipse_halfheight_integral (a : ℝ) (ha : 0 < a) :
    ∫ x in (-a)..a, Real.sqrt (1 - (x / a) ^ 2) = a * (π / 2) := by
  have e1 : -a / a = -1 := by rw [neg_div, div_self ha.ne']
  have e2 : a / a = 1 := div_self ha.ne'
  have key := intervalIntegral.integral_comp_div (a := -a) (b := a)
    (fun t => Real.sqrt (1 - t ^ 2)) ha.ne'
  simp only [e1, e2] at key
  rw [key, integral_sqrt_one_sub_sq, smul_eq_mul]

/-- **The ellipse area formula, rigorously.** The area enclosed by the ellipse
`x²/a² + y²/b² = 1`, computed as `∫ 2·b·√(1 − (x/a)²) dx` over `[−a, a]`, equals
`π·a·b`. -/
theorem ellipse_area_integral (a b : ℝ) (ha : 0 < a) :
    ∫ x in (-a)..a, 2 * b * Real.sqrt (1 - (x / a) ^ 2) = π * a * b := by
  rw [intervalIntegral.integral_const_mul, ellipse_halfheight_integral a ha]
  ring

/-- **Circle as the special case `a = b = r`.** Setting both semi-axes to `r`
recovers the area `π·r²` of a disc of radius `r`. -/
theorem circle_area_special (r : ℝ) (hr : 0 < r) :
    ∫ x in (-r)..r, 2 * r * Real.sqrt (1 - (x / r) ^ 2) = π * r ^ 2 := by
  rw [ellipse_area_integral r r hr]; ring

/-- The ellipse area is strictly positive for positive semi-axes. -/
theorem ellipse_area_pos (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    0 < ∫ x in (-a)..a, 2 * b * Real.sqrt (1 - (x / a) ^ 2) := by
  rw [ellipse_area_integral a b ha]
  have := Real.pi_pos
  positivity

/-- **The filled ellipse as a genuine 2D region, with its Lebesgue measure.** The
solid ellipse — the planar region between the lower arc `y = −b·√(1 − (x/a)²)` and
the upper arc `y = +b·√(1 − (x/a)²)` for `x ∈ [−a, a]` — has 2D Lebesgue measure
exactly `π·a·b`. This upgrades the 1D area integral to the true 2D measure of the
region, via `volume_regionBetween_eq_integral` and the interval integral above. -/
theorem ellipse_volume (a b : ℝ) (ha : 0 < a) (hb : 0 ≤ b) :
    volume (regionBetween
        (fun x => -(b * Real.sqrt (1 - (x / a) ^ 2)))
        (fun x => b * Real.sqrt (1 - (x / a) ^ 2))
        (Set.Icc (-a) a)) = ENNReal.ofReal (π * a * b) := by
  have hcont : Continuous fun x : ℝ => b * Real.sqrt (1 - (x / a) ^ 2) := by fun_prop
  have hhi : IntegrableOn (fun x => b * Real.sqrt (1 - (x / a) ^ 2)) (Set.Icc (-a) a) volume :=
    hcont.integrableOn_Icc
  have hlo : IntegrableOn (fun x => -(b * Real.sqrt (1 - (x / a) ^ 2))) (Set.Icc (-a) a) volume :=
    hcont.neg.integrableOn_Icc
  have hfg : ∀ x ∈ Set.Icc (-a) a,
      -(b * Real.sqrt (1 - (x / a) ^ 2)) ≤ b * Real.sqrt (1 - (x / a) ^ 2) := by
    intro x _
    have : 0 ≤ b * Real.sqrt (1 - (x / a) ^ 2) := by positivity
    linarith
  rw [MeasureTheory.Measure.volume_eq_prod ℝ ℝ,
    volume_regionBetween_eq_integral hlo hhi measurableSet_Icc hfg]
  congr 1
  have hsimp : (fun y => ((fun x => b * Real.sqrt (1 - (x / a) ^ 2))
        - fun x => -(b * Real.sqrt (1 - (x / a) ^ 2))) y)
      = fun y => 2 * b * Real.sqrt (1 - (y / a) ^ 2) := by
    funext y; simp only [Pi.sub_apply]; ring
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith : (-a) ≤ a), hsimp]
  exact ellipse_area_integral a b ha

end AreaOfCircleOQ03OQ03OQ01
