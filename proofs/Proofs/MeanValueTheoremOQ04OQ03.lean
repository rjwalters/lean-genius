/-
# Trapezoidal Rule Error Bound via the Peano Kernel

For a `C²` function `f : ℝ → ℝ`, the error of the trapezoidal quadrature rule

  T(a,b) = (b - a)/2 · (f a + f b)

as an approximation to `∫ₐᵇ f` is given *exactly* by an integral against the
**Peano kernel** `K(x) = (x - a)(x - b)/2`:

  ∫ₐᵇ K(x) · f''(x) dx = ∫ₐᵇ f(x) dx − T(a,b).

This is the kernel form of the classical trapezoidal error.  It is obtained by
integrating the kernel integral by parts twice: the kernel and its derivative
both vanish at the right places to kill the boundary terms, peeling off the
quadrature weights one factor at a time.  No mean value theorem and no `ξ` is
needed for the identity itself — it is an exact equality, the starting point
of every quantitative trapezoidal bound.

Consequences proved here:

* `trapezoid_overestimates_of_convex`: since `K ≤ 0` on `[a,b]`, a convex `f`
  (`f'' ≥ 0`) makes the trapezoid rule an **over**estimate, `∫ₐᵇ f ≤ T(a,b)`.
* `trapezoid_underestimates_of_concave`: the concave mirror image.

Mathlib has integration by parts (`integral_mul_deriv_eq_deriv_mul_of_hasDerivAt`)
and the trapezoid set-up, but no trapezoidal rule error identity; this file
supplies the Peano-kernel form.

We use the strong, clean hypothesis that `f` is twice differentiable on all of
`ℝ` with continuous second derivative (a global `C²` assumption), which makes
every regularity side condition immediate.
-/
import Mathlib

open intervalIntegral MeasureTheory Set

namespace TrapezoidalPeanoKernel

variable {f f' f'' : ℝ → ℝ} {a b : ℝ}

/-- Derivative of the Peano kernel `K(x) = (x - a)(x - b)/2`, namely
`K'(x) = (2x - a - b)/2`. -/
lemma hasDerivAt_kernel (a b x : ℝ) :
    HasDerivAt (fun x => (x - a) * (x - b) / 2) ((2 * x - a - b) / 2) x := by
  have h : HasDerivAt (fun x => (x - a) * (x - b)) (1 * (x - b) + (x - a) * 1) x :=
    ((hasDerivAt_id x).sub_const a).mul ((hasDerivAt_id x).sub_const b)
  have h2 := h.div_const 2
  convert h2 using 1
  ring

/-- Derivative of the linear factor `(2x - a - b)/2`, which is the constant `1`. -/
lemma hasDerivAt_kernelDeriv (a b x : ℝ) :
    HasDerivAt (fun x => (2 * x - a - b) / 2) 1 x := by
  have h : HasDerivAt (fun x => 2 * x - a - b) 2 x := by
    have := ((hasDerivAt_id x).const_mul 2).sub_const a |>.sub_const b
    simpa using this
  have h2 := h.div_const 2
  convert h2 using 1
  norm_num

/-- Continuity of `f` from twice differentiability everywhere. -/
private lemma continuous_of_hasDerivAt (hf : ∀ x, HasDerivAt f (f' x) x) :
    Continuous f :=
  continuous_iff_continuousAt.2 fun x => (hf x).continuousAt

/-- **Trapezoidal rule error via the Peano kernel.**

For a globally `C²` function `f`, the integral of the Peano kernel `K(x) =
(x-a)(x-b)/2` against `f''` equals the difference between the exact integral of
`f` and the trapezoidal estimate `(b-a)/2·(f a + f b)`. -/
theorem trapezoidal_peano_kernel
    (hf : ∀ x, HasDerivAt f (f' x) x)
    (hf' : ∀ x, HasDerivAt f' (f'' x) x)
    (hf'' : Continuous f'') :
    ∫ x in a..b, ((x - a) * (x - b) / 2) * f'' x
      = (∫ x in a..b, f x) - (b - a) / 2 * (f a + f b) := by
  have hfc : Continuous f := continuous_of_hasDerivAt hf
  have hf'c : Continuous f' := continuous_of_hasDerivAt hf'
  -- First integration by parts: u = K, v = f', v' = f''.
  have step1 :
      ∫ x in a..b, ((x - a) * (x - b) / 2) * f'' x
        = ((b - a) * (b - b) / 2) * f' b - ((a - a) * (a - b) / 2) * f' a
            - ∫ x in a..b, ((2 * x - a - b) / 2) * f' x :=
    integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
      (u := fun x => (x - a) * (x - b) / 2) (u' := fun x => (2 * x - a - b) / 2)
      (v := f') (v' := f'')
      (by fun_prop) hf'c.continuousOn
      (fun x _ => hasDerivAt_kernel a b x) (fun x _ => hf' x)
      ((show Continuous (fun x => (2 * x - a - b) / 2) by fun_prop).intervalIntegrable a b)
      (hf''.intervalIntegrable a b)
  -- Second integration by parts: u = K', v = f, v' = f'.
  have step2 :
      ∫ x in a..b, ((2 * x - a - b) / 2) * f' x
        = ((2 * b - a - b) / 2) * f b - ((2 * a - a - b) / 2) * f a
            - ∫ x in a..b, (1 : ℝ) * f x :=
    integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
      (u := fun x => (2 * x - a - b) / 2) (u' := fun _ => (1 : ℝ))
      (v := f) (v' := f')
      (by fun_prop) hfc.continuousOn
      (fun x _ => hasDerivAt_kernelDeriv a b x) (fun x _ => hf x)
      intervalIntegral.intervalIntegrable_const (hf'c.intervalIntegrable a b)
  rw [step1, step2]
  simp only [one_mul]
  ring

/-- On `[a,b]` the Peano kernel `K(x) = (x-a)(x-b)/2` is nonpositive. -/
lemma kernel_nonpos {x : ℝ} (hx : x ∈ Set.Icc a b) :
    (x - a) * (x - b) / 2 ≤ 0 := by
  have h1 : 0 ≤ x - a := by linarith [hx.1]
  have h2 : x - b ≤ 0 := by linarith [hx.2]
  have : (x - a) * (x - b) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos h1 h2
  linarith

/-- **Convex functions are overestimated by the trapezoidal rule.**

If `f'' ≥ 0` on `[a,b]` (so `f` is convex there) and `a ≤ b`, the trapezoidal
estimate is at least the true integral. -/
theorem trapezoid_overestimates_of_convex
    (hf : ∀ x, HasDerivAt f (f' x) x)
    (hf' : ∀ x, HasDerivAt f' (f'' x) x)
    (hf'' : Continuous f'')
    (hab : a ≤ b)
    (hconv : ∀ x ∈ Set.Icc a b, 0 ≤ f'' x) :
    (∫ x in a..b, f x) ≤ (b - a) / 2 * (f a + f b) := by
  have hkey := trapezoidal_peano_kernel (a := a) (b := b) hf hf' hf''
  -- The kernel integral is ≤ 0 since K ≤ 0 and f'' ≥ 0 on [a,b].
  have hnonpos : ∫ x in a..b, ((x - a) * (x - b) / 2) * f'' x ≤ 0 := by
    have h := intervalIntegral.integral_nonneg (μ := volume)
      (f := fun x => -(((x - a) * (x - b) / 2) * f'' x)) hab
      (fun u hu => by
        have hk := kernel_nonpos hu
        have hc := hconv u hu
        nlinarith [mul_nonneg (show (0:ℝ) ≤ -((u - a) * (u - b) / 2) by linarith) hc])
    rw [intervalIntegral.integral_neg] at h
    linarith
  rw [hkey] at hnonpos
  linarith

/-- **Concave functions are underestimated by the trapezoidal rule.** -/
theorem trapezoid_underestimates_of_concave
    (hf : ∀ x, HasDerivAt f (f' x) x)
    (hf' : ∀ x, HasDerivAt f' (f'' x) x)
    (hf'' : Continuous f'')
    (hab : a ≤ b)
    (hconc : ∀ x ∈ Set.Icc a b, f'' x ≤ 0) :
    (b - a) / 2 * (f a + f b) ≤ ∫ x in a..b, f x := by
  have hkey := trapezoidal_peano_kernel (a := a) (b := b) hf hf' hf''
  have hnonneg : 0 ≤ ∫ x in a..b, ((x - a) * (x - b) / 2) * f'' x := by
    apply intervalIntegral.integral_nonneg hab
    intro u hu
    have hk := kernel_nonpos hu
    have hc := hconc u hu
    nlinarith [mul_nonneg (show (0:ℝ) ≤ -((u - a) * (u - b) / 2) by linarith)
      (show (0:ℝ) ≤ -(f'' u) by linarith)]
  rw [hkey] at hnonneg
  linarith

end TrapezoidalPeanoKernel
