/-
  The Fundamental Theorem of Calculus

  A formal proof in Lean 4 demonstrating the profound connection between
  differentiation and integration - the two pillars of calculus.

  Historical context: Though Newton and Leibniz independently discovered
  calculus in the late 17th century, the rigorous formulation of FTC required
  the epsilon-delta definitions of Cauchy (1820s) and Weierstrass (1860s).

  The theorem has two parts:
  - FTC Part 1: The derivative of an integral recovers the original function
  - FTC Part 2: The integral of a derivative equals the net change

  This formalization demonstrates these relationships using interval integrals
  and derivatives, following Mathlib's analysis conventions.
-/

import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import Mathlib.Analysis.Calculus.Integral.FundThm

-- We work in the real numbers
open MeasureTheory Set Filter Topology

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
-- This is the key theorem from Mathlib
theorem ftc_part1 {f : ℝ → ℝ} {a x : ℝ}
    (hf : ContinuousAt f x) (hfi : IntervalIntegrable f volume a x) :
    HasDerivAt (integralFunction f a) (f x) x :=
  integral_hasDerivAt_right hfi hf

-- Corollary: Under stronger continuity, we get the classic statement
theorem ftc_part1_continuous {f : ℝ → ℝ} {a b : ℝ}
    (hf : Continuous f) (x : ℝ) (hx : x ∈ Icc a b) :
    HasDerivAt (integralFunction f a) (f x) x := by
  apply ftc_part1
  · exact hf.continuousAt
  · exact hf.intervalIntegrable a x

/-
  Part 2: The Integral of a Derivative

  If F is differentiable on [a, b] with continuous derivative f = F',
  then ∫ₐᵇ f(x) dx = F(b) - F(a).

  This is the evaluation theorem: to compute a definite integral,
  find an antiderivative and evaluate at the endpoints.
-/

-- FTC Part 2: The integral of a derivative equals the net change
theorem ftc_part2 {F : ℝ → ℝ} {a b : ℝ}
    (hF : ∀ x ∈ Icc a b, HasDerivAt F (deriv F x) x)
    (hF' : ContinuousOn (deriv F) (Icc a b))
    (hab : a ≤ b) :
    ∫ x in a..b, deriv F x = F b - F a :=
  integral_eq_sub_of_hasDerivAt (fun x hx => hF x (Icc_subset_Icc_left (le_refl a) hx))
    (hF'.mono Ioc_subset_Icc_self) (intervalIntegrable_of_continuous hab hF')

-- Simplified version using Mathlib's interval integral theorem
theorem ftc_part2_simple {F f : ℝ → ℝ} {a b : ℝ}
    (hF : ∀ x ∈ [[a, b]], HasDerivAt F (f x) x)
    (hf : ContinuousOn f [[a, b]]) :
    ∫ x in a..b, f x = F b - F a :=
  intervalIntegral.integral_eq_sub_of_hasDerivAt hF
    (hf.mono Ioc_subset_Icc_self) (hf.intervalIntegrable)

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
  apply ftc_part1
  · exact hf.continuousAt
  · exact hf.intervalIntegrable a x

-- Antiderivatives differ by a constant
-- If F and G are both antiderivatives of f, then F - G is constant
theorem antiderivatives_differ_by_constant {F G f : ℝ → ℝ}
    (hF : IsAntiderivative F f) (hG : IsAntiderivative G f) :
    ∃ c : ℝ, ∀ x, F x - G x = c := by
  -- The derivative of (F - G) is f - f = 0
  -- A function with zero derivative is constant
  use F 0 - G 0
  intro x
  -- This follows from the mean value theorem
  have h : ∀ y, HasDerivAt (fun z => F z - G z) 0 y := by
    intro y
    have := (hF y).sub (hG y)
    simp at this
    exact this
  -- Apply the constant function theorem
  have hconst := hasDerivAt_zero_constant h
  exact hconst x 0

-- Helper: a function with everywhere-zero derivative is constant
theorem hasDerivAt_zero_constant {F : ℝ → ℝ}
    (hF : ∀ x, HasDerivAt F 0 x) :
    ∀ x y, F x = F y := by
  intro x y
  by_cases hxy : x = y
  · rw [hxy]
  · -- Use the mean value theorem
    have hderiv : ∀ z, HasDerivAt F 0 z := hF
    have hcont : Continuous F := by
      apply Differentiable.continuous
      intro z
      exact (hF z).differentiableAt
    -- F' = 0 everywhere implies F is constant
    have := Convex.is_const_of_fderivWithin_eq_zero convex_univ
      (hcont.continuousOn) (fun z _ => (hF z).hasFDerivAt.hasFDerivWithinAt)
      (fun z _ => by simp [ContinuousLinearMap.ext_iff]) (mem_univ x) (mem_univ y)
    exact this

#check ftc_part1
#check ftc_part2
#check integral_is_antiderivative
#check antiderivatives_differ_by_constant
