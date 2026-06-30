/-
# Central Limit Theorem OQ-01-OQ-04 — toward a Berry–Esseen rate for α-stable laws

*Open question (central-limit-theorem-oq-01-oq-04).* The Berry–Esseen theorem
gives the rate of convergence in the classical CLT: if `X₁, …, Xₙ` are i.i.d.
with mean 0, variance `σ² > 0` and finite third moment `ρ = E|X|³`, then

  sup_x |F_n(x) − Φ(x)|  ≤  C · ρ / (σ³ √n).

Can this rate-of-convergence theorem be generalized to the α-stable limit laws
(α < 2) that govern the infinite-variance CLT of the parent file? This is genuinely
hard. This entry isolates, axiom-free, *the analytic mechanism* of Berry–Esseen
and *the precise obstruction* to extending it below α = 2.

## The mechanism (reused from Mathlib)

Berry–Esseen compares the characteristic function `φ_n(t)` of the normalized sum
to the Gaussian `e^{−t²/2}`. The comparison rests on Taylor bounds for the
integrand `e^{iax}`:

  ‖e^{ia} − 1‖ ≤ 2|a|,    ‖e^{ia} − (1 + ia)‖ ≤ a².

Integrating the second against the law of `X` turns the `a²` remainder into a
*variance / third-moment* term — this is why a finite third moment yields the
`ρ/(σ³√n)` rate. We restate these deterministic kernel bounds
(`charFun_kernel_first`, `charFun_kernel_second`) from Mathlib's
`Complex.norm_exp_sub_one_le` / `norm_exp_sub_one_sub_id_le`.

## The obstruction (the new content)

For the standard symmetric α-stable law the (real, by symmetry) characteristic
function is `φ_α(t) = exp(−|t|^α)` (parent file). Near `t = 0` the Gaussian
correction is *quadratic* (`1 − t²/2 + …`), but the α-stable correction is
`1 − |t|^α + …` with `|t|^α` **sub-quadratic** for `α < 2`:

  for `0 < t < 1`,  `t² < t^α`  (so `φ_α(t) < φ_2(t)`: α-stable decays faster near 0),
  for `t > 1`,      `t^α < t²`  (so `φ_α(t) > φ_2(t)`: heavier frequency tail),

with the crossover exactly at `t = 1`. The sub-quadratic deviation near `0` is
the analytic signature of infinite variance: the `a²`-remainder argument above
integrates to an infinite (variance) constant, so the classical Berry–Esseen
expansion has **no finite α < 2 analogue** — any α-stable rate theorem must
replace the second-order expansion by one matched to the `|t|^α` exponent. We
make the crossover precise (`stablePhi_lt_gaussian`, `stablePhi_gt_gaussian`,
`exponent_crossover_at_one`) and record the α = 2 (Gaussian) and α = 1 (Cauchy)
specializations.

Everything is checked by the kernel with no axioms and no `native_decide`.
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic

open Real

namespace CLTOQ01OQ04

/-!
## The standard symmetric α-stable characteristic function (real form)

By symmetry the characteristic function is real: `φ_α(t) = exp(−|t|^α)`, where
`|t|^α` is the real power `Real.rpow`. This matches `stableCharFun` of the
parent file on the real axis.
-/

/-- Real form of the standard symmetric α-stable characteristic function,
`φ_α(t) = exp(−|t|^α)`. -/
noncomputable def stablePhi (α t : ℝ) : ℝ := Real.exp (-(|t| ^ α))

/-- α = 2 is the Gaussian: `φ_2(t) = exp(−t²)`. -/
theorem stablePhi_two (t : ℝ) : stablePhi 2 t = Real.exp (-(t ^ 2)) := by
  unfold stablePhi
  rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, Real.rpow_natCast, sq_abs]

/-- α = 1 is the Cauchy law: `φ_1(t) = exp(−|t|)`. -/
theorem stablePhi_one (t : ℝ) : stablePhi 1 t = Real.exp (-|t|) := by
  unfold stablePhi; rw [Real.rpow_one]

/-- `φ_α(0) = 1` for every `α > 0` (a characteristic function at 0). -/
theorem stablePhi_zero (α : ℝ) (hα : 0 < α) : stablePhi α 0 = 1 := by
  unfold stablePhi
  rw [abs_zero, Real.zero_rpow (ne_of_gt hα), neg_zero, Real.exp_zero]

/-- `φ_α(t) > 0`: the real characteristic function is strictly positive. -/
theorem stablePhi_pos (α t : ℝ) : 0 < stablePhi α t := Real.exp_pos _

/-!
## The frequency-domain crossover: α-stable vs Gaussian

The exponent `|t|^α` crosses the Gaussian exponent `t²` exactly at `|t| = 1`.
This is the analytic heart of "infinite variance": sub-quadratic near 0.
-/

/-- Below the crossover (`0 < t < 1`) the α-stable exponent exceeds the Gaussian:
`t² < t^α` for `α < 2`. -/
theorem exponent_gt_sq {α t : ℝ} (hα : α < 2) (ht0 : 0 < t) (ht1 : t < 1) :
    t ^ (2 : ℝ) < t ^ α :=
  Real.rpow_lt_rpow_of_exponent_gt ht0 ht1 hα

/-- Above the crossover (`t > 1`) the Gaussian exponent dominates:
`t^α < t²` for `α < 2`. -/
theorem exponent_lt_sq {α t : ℝ} (hα : α < 2) (ht : 1 < t) :
    t ^ α < t ^ (2 : ℝ) :=
  Real.rpow_lt_rpow_of_exponent_lt ht hα

/-- At the crossover the two exponents agree: `1^α = 1^2 = 1`. -/
theorem exponent_crossover_at_one (α : ℝ) :
    (1 : ℝ) ^ α = (1 : ℝ) ^ (2 : ℝ) := by
  rw [Real.one_rpow, Real.one_rpow]

/-- **Sub-quadratic deviation near 0.** For `0 < t < 1` and `α < 2`, the
α-stable characteristic function lies *below* the Gaussian: it decays faster
near the origin because its exponent is larger there. -/
theorem stablePhi_lt_gaussian {α t : ℝ} (hα : α < 2) (ht0 : 0 < t) (ht1 : t < 1) :
    stablePhi α t < stablePhi 2 t := by
  unfold stablePhi
  apply Real.exp_lt_exp.mpr
  have hat0 : (0 : ℝ) < |t| := by rwa [abs_of_pos ht0]
  have hat1 : |t| < 1 := by rwa [abs_of_pos ht0]
  have h : |t| ^ (2 : ℝ) < |t| ^ α := Real.rpow_lt_rpow_of_exponent_gt hat0 hat1 hα
  linarith

/-- **Heavier frequency tail.** For `t > 1` and `α < 2`, the α-stable
characteristic function lies *above* the Gaussian. -/
theorem stablePhi_gt_gaussian {α t : ℝ} (hα : α < 2) (ht : 1 < t) :
    stablePhi 2 t < stablePhi α t := by
  unfold stablePhi
  apply Real.exp_lt_exp.mpr
  have hat : (1 : ℝ) < |t| := by rwa [abs_of_pos (lt_trans one_pos ht)]
  have h : |t| ^ α < |t| ^ (2 : ℝ) := Real.rpow_lt_rpow_of_exponent_lt hat hα
  linarith

/-- At the crossover point the two laws share the same characteristic value. -/
theorem stablePhi_eq_at_one (α : ℝ) : stablePhi α 1 = stablePhi 2 1 := by
  unfold stablePhi
  rw [abs_one, Real.one_rpow, Real.one_rpow]

/-!
## The deterministic Berry–Esseen kernel

These are the Taylor bounds for the characteristic-function integrand
`e^{ia} = exp(i·a)` (`a = t·x`), restated from Mathlib. Integrating the
second bound against the law of `X` is exactly how Berry–Esseen converts a
finite third moment into the `ρ/(σ³√n)` rate.
-/

/-- First-order kernel bound: `‖e^{ia} − 1‖ ≤ 2|a|` for `|a| ≤ 1`. -/
theorem charFun_kernel_first {a : ℝ} (ha : |a| ≤ 1) :
    ‖Complex.exp ((a : ℂ) * Complex.I) - 1‖ ≤ 2 * |a| := by
  have hnorm : ‖(a : ℂ) * Complex.I‖ = |a| := by
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  have h := Complex.norm_exp_sub_one_le (x := (a : ℂ) * Complex.I) (by rw [hnorm]; exact ha)
  rwa [hnorm] at h

/-- Second-order kernel bound: `‖e^{ia} − (1 + ia)‖ ≤ a²` for `|a| ≤ 1`.
The `a²` remainder is what becomes a variance/third-moment term after
integration — the engine of the classical Berry–Esseen rate. -/
theorem charFun_kernel_second {a : ℝ} (ha : |a| ≤ 1) :
    ‖Complex.exp ((a : ℂ) * Complex.I) - (1 + (a : ℂ) * Complex.I)‖ ≤ a ^ 2 := by
  have hnorm : ‖(a : ℂ) * Complex.I‖ = |a| := by
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  have h := Complex.norm_exp_sub_one_sub_id_le (x := (a : ℂ) * Complex.I)
    (by rw [hnorm]; exact ha)
  rw [hnorm] at h
  calc ‖Complex.exp ((a : ℂ) * Complex.I) - (1 + (a : ℂ) * Complex.I)‖
      = ‖Complex.exp ((a : ℂ) * Complex.I) - 1 - (a : ℂ) * Complex.I‖ := by ring_nf
    _ ≤ |a| ^ 2 := h
    _ = a ^ 2 := sq_abs a

end CLTOQ01OQ04
