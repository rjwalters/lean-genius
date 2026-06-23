import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Bochner.FundThmCalculus
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.Basic

/-!
# Fundamental Theorem of Calculus

## What This Proves
We prove both parts of the Fundamental Theorem of Calculus:
- Part 1: d/dx ∫ₐˣ f(t)dt = f(x) (differentiation undoes integration)
- Part 2: ∫ₐᵇ f'(x)dx = f(b) - f(a) (integration undoes differentiation)

## Approach
- **Foundation (from Mathlib):** We use Mathlib's measure theory and calculus
  libraries. The core theorems `integral_hasDerivAt_right` and
  `integral_eq_sub_of_hasDerivAt` are from Mathlib.
- **Original Contributions:** This file provides pedagogical organization,
  wrapper theorems with cleaner hypotheses (like `ftc_part1_continuous`),
  and extensive commentary explaining the theorem's significance.
- **Proof Techniques Demonstrated:** Working with Mathlib's measure theory API,
  continuity and integrability conditions, interval integrals.

## Status
- [x] Complete proof
- [ ] Uses Mathlib for main result
- [ ] Proves extensions/corollaries
- [ ] Pedagogical example
- [ ] Incomplete (has sorries)

## Mathlib Dependencies
- `integral_hasDerivAt_right` : FTC Part 1 (derivative of integral)
- `integral_eq_sub_of_hasDerivAt` : FTC Part 2 (integral of derivative)
- `IntervalIntegrable` : Integrability on intervals
- `HasDerivAt` : Derivative at a point
- `ContinuousAt`, `Continuous` : Continuity definitions

Historical Note: Newton and Leibniz discovered calculus independently in the
late 17th century, but rigorous formulation required Cauchy (1820s) and
Weierstrass (1860s).
-/

-- We work in the real numbers
open MeasureTheory Set Filter Topology intervalIntegral

namespace FundamentalTheoremCalculus

/-
  Part 1: The Derivative of an Integral

  If f is continuous on [a, b], and we define F(x) = ∫ₐˣ f(t) dt,
  then F is differentiable and F'(x) = f(x).

  This says: integration is the "inverse" of differentiation.
-/

-- The integral function: F(x) = ∫ₐˣ f(t) dt
noncomputable def integralFunction (f : ℝ → ℝ) (a : ℝ) : ℝ → ℝ :=
  fun x => ∫ t in a..x, f t

-- FTC Part 1: The derivative of the integral function equals f
-- Uses Mathlib's fundamental theorem
theorem ftc_part1 {f : ℝ → ℝ} {a b : ℝ}
    (hf_cont : ContinuousAt f b) (hf_int : IntervalIntegrable f volume a b)
    (hf_meas : StronglyMeasurableAtFilter f (𝓝 b) volume) :
    HasDerivAt (integralFunction f a) (f b) b :=
  integral_hasDerivAt_right hf_int hf_meas hf_cont

-- Corollary: Under stronger continuity, we get the classic statement
theorem ftc_part1_continuous {f : ℝ → ℝ} {a : ℝ}
    (hf : Continuous f) (x : ℝ) :
    HasDerivAt (integralFunction f a) (f x) x := by
  apply ftc_part1
  · exact hf.continuousAt
  · exact hf.intervalIntegrable a x
  · exact hf.stronglyMeasurableAtFilter volume (𝓝 x)

/-
  Part 2: The Integral of a Derivative

  If F is differentiable on [a, b] with continuous derivative f = F',
  then ∫ₐᵇ f(x) dx = F(b) - F(a).

  This is the evaluation theorem: to compute a definite integral,
  find an antiderivative and evaluate at the endpoints.
-/

-- FTC Part 2: The integral of a derivative equals the net change
theorem ftc_part2 {F f : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b)
    (hF_cont : ContinuousOn F (Icc a b))
    (hF_deriv : ∀ x ∈ Ioo a b, HasDerivAt F (f x) x)
    (hf_int : IntervalIntegrable f volume a b) :
    ∫ x in a..b, f x = F b - F a :=
  integral_eq_sub_of_hasDerivAt_of_le hab hF_cont hF_deriv hf_int

-- Version without the a ≤ b assumption, using uIcc
theorem ftc_part2_general {F f : ℝ → ℝ} {a b : ℝ}
    (hF_cont : ContinuousOn F (uIcc a b))
    (hF_deriv : ∀ x ∈ Ioo (min a b) (max a b), HasDerivWithinAt F (f x) (Ioi x) x)
    (hf_int : IntervalIntegrable f volume a b) :
    ∫ x in a..b, f x = F b - F a :=
  integral_eq_sub_of_hasDeriv_right hF_cont hF_deriv hf_int

/-
  The Unity of Calculus

  Together, FTC Parts 1 and 2 establish that differentiation and integration
  are inverse operations (up to constants):

  - If you integrate then differentiate, you get back the original: d/dx ∫ₐˣ f = f
  - If you differentiate then integrate, you get back (up to constant): ∫ₐˣ F' = F - F(a)

  This is why we call F an "antiderivative" of f when F' = f.
-/

-- Antiderivative: F is an antiderivative of f if F' = f everywhere
def IsAntiderivative (F f : ℝ → ℝ) : Prop :=
  ∀ x, HasDerivAt F (f x) x

-- The integral function is an antiderivative of f (when f is continuous)
theorem integral_is_antiderivative {f : ℝ → ℝ} {a : ℝ}
    (hf : Continuous f) :
    IsAntiderivative (integralFunction f a) f := by
  intro x
  exact ftc_part1_continuous hf x

-- Helper: a function with everywhere-zero derivative is constant
-- This follows from the mean value theorem
theorem hasDerivAt_zero_implies_constant {F : ℝ → ℝ}
    (hF : ∀ x, HasDerivAt F 0 x) :
    ∀ x y, F x = F y := by
  have hdiff : Differentiable ℝ F := fun z => (hF z).differentiableAt
  have hderiv : ∀ z, deriv F z = 0 := fun z => (hF z).deriv
  intro x y
  -- Use is_const_of_deriv_eq_zero
  exact is_const_of_deriv_eq_zero hdiff hderiv x y

-- Antiderivatives differ by a constant
-- If F and G are both antiderivatives of f, then F - G is constant
theorem antiderivatives_differ_by_constant {F G f : ℝ → ℝ}
    (hF : IsAntiderivative F f) (hG : IsAntiderivative G f) :
    ∃ c : ℝ, ∀ x, F x - G x = c := by
  -- The derivative of (F - G) is f - f = 0
  use F 0 - G 0
  intro x
  -- The derivative of F - G is 0
  have h : ∀ y, HasDerivAt (fun z => F z - G z) 0 y := by
    intro y
    have := (hF y).sub (hG y)
    simp at this
    exact this
  -- Apply the constant function theorem
  have hconst := hasDerivAt_zero_implies_constant h
  have := hconst x 0
  linarith

end FundamentalTheoremCalculus

#check FundamentalTheoremCalculus.ftc_part1
#check FundamentalTheoremCalculus.ftc_part2
#check FundamentalTheoremCalculus.integral_is_antiderivative
#check FundamentalTheoremCalculus.antiderivatives_differ_by_constant
