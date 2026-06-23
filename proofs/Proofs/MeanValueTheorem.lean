import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# Mean Value Theorem

## What This Proves
We prove the Mean Value Theorem (MVT): if f is a real-valued function that is
continuous on a closed interval [a, b] and differentiable on the open interval
(a, b), then there exists some c in (a, b) such that:

  f'(c) = (f(b) - f(a)) / (b - a)

Geometrically, this means there is a point where the tangent line is parallel
to the secant line connecting (a, f(a)) and (b, f(b)).

## Wiedijk 100 Theorems: #75
This is entry #75 in Freek Wiedijk's list of 100 famous theorems.

## Approach
- **Foundation (from Mathlib):** We use Mathlib's `exists_deriv_eq_slope` theorem,
  which is the standard formulation of Lagrange's Mean Value Theorem.
- **Original Contributions:** This file provides pedagogical organization,
  wrapper theorems with classical statements (including the `HasDerivAt` version
  and Cauchy's MVT as a generalization), and commentary on applications.
- **Proof Techniques Demonstrated:** Working with Mathlib's calculus framework,
  differentiability and continuity conditions, and the relationship between
  `deriv` and `HasDerivAt`.

## Status
- [x] Complete proof
- [x] Uses Mathlib for main result
- [x] Proves extensions/corollaries
- [ ] Pedagogical example
- [ ] Incomplete (has sorries)

## Mathlib Dependencies
- `exists_deriv_eq_slope` : Lagrange's Mean Value Theorem (deriv version)
- `exists_hasDerivAt_eq_slope` : Lagrange's MVT (HasDerivAt version)
- `exists_ratio_deriv_eq_ratio_slope` : Cauchy's Mean Value Theorem

Historical Note: The Mean Value Theorem was first proved by Joseph-Louis Lagrange
in 1797, though special cases were known earlier. Augustin-Louis Cauchy later
generalized it to the form now known as Cauchy's Mean Value Theorem (1821).
The theorem is fundamental to analysis, forming the basis for L'Hopital's rule,
Taylor's theorem, and the fundamental theorem of calculus.
-/

open Set Filter Topology

namespace MeanValueTheorem

/-!
## The Classical Statement (Lagrange's Mean Value Theorem)

If f : ℝ → ℝ is continuous on [a, b] and differentiable on (a, b), then
there exists c ∈ (a, b) such that f'(c) = (f(b) - f(a)) / (b - a).

The derivative at c equals the average rate of change over the interval.
-/

/-- **Mean Value Theorem (Wiedijk #75)**

Lagrange's Mean Value Theorem: For a function f that is continuous on [a, b]
and differentiable on (a, b), there exists a point c in the open interval
(a, b) where the derivative equals the slope of the secant line.

This is the cornerstone of differential calculus, connecting local behavior
(the derivative) to global behavior (the secant slope). -/
theorem mvt {a b : ℝ} (hab : a < b) {f : ℝ → ℝ}
    (hfc : ContinuousOn f (Icc a b))
    (hfd : DifferentiableOn ℝ f (Ioo a b)) :
    ∃ c ∈ Ioo a b, deriv f c = (f b - f a) / (b - a) :=
  exists_deriv_eq_slope f hab hfc hfd

/-- The `HasDerivAt` version of MVT, useful when you have explicit derivative values.

This form is often more convenient when working with specific functions
where you know the derivative explicitly. -/
theorem mvt_hasDerivAt {a b : ℝ} (hab : a < b) {f f' : ℝ → ℝ}
    (hfc : ContinuousOn f (Icc a b))
    (hff' : ∀ x ∈ Ioo a b, HasDerivAt f (f' x) x) :
    ∃ c ∈ Ioo a b, f' c = (f b - f a) / (b - a) :=
  exists_hasDerivAt_eq_slope f f' hab hfc hff'

/-!
## Cauchy's Mean Value Theorem

A generalization that relates two functions. When g(x) = x, this reduces
to Lagrange's MVT.
-/

/-- **Cauchy's Mean Value Theorem**

For two functions f and g that are continuous on [a, b] and differentiable
on (a, b), there exists c ∈ (a, b) such that:

  (g(b) - g(a)) · f'(c) = (f(b) - f(a)) · g'(c)

This generalizes Lagrange's MVT (take g(x) = x) and is the key lemma for
proving L'Hopital's rule. -/
theorem cauchy_mvt {a b : ℝ} (hab : a < b) {f g : ℝ → ℝ}
    (hfc : ContinuousOn f (Icc a b))
    (hfd : DifferentiableOn ℝ f (Ioo a b))
    (hgc : ContinuousOn g (Icc a b))
    (hgd : DifferentiableOn ℝ g (Ioo a b)) :
    ∃ c ∈ Ioo a b, (g b - g a) * deriv f c = (f b - f a) * deriv g c :=
  exists_ratio_deriv_eq_ratio_slope f hab hfc hfd g hgc hgd

/-!
## Corollaries and Applications
-/

/-- If the derivative is zero everywhere on (a, b), the function is constant on [a, b].

This is a key consequence of MVT: zero derivative implies constant function. -/
theorem constant_of_deriv_zero {a b : ℝ} (hab : a < b) {f : ℝ → ℝ}
    (hfc : ContinuousOn f (Icc a b))
    (hfd : DifferentiableOn ℝ f (Ioo a b))
    (hf0 : ∀ x ∈ Ioo a b, deriv f x = 0) :
    f b = f a := by
  obtain ⟨c, hc, hc_eq⟩ := mvt hab hfc hfd
  have : deriv f c = 0 := hf0 c hc
  rw [this] at hc_eq
  have hab_pos : b - a > 0 := sub_pos.mpr hab
  field_simp at hc_eq
  linarith

/-!
## Geometric Interpretation

The Mean Value Theorem has a beautiful geometric interpretation:

Given a curve y = f(x) from point A = (a, f(a)) to point B = (b, f(b)),
there is at least one point C on the curve where the tangent line is
parallel to the secant line AB.

The secant line has slope (f(b) - f(a)) / (b - a), and MVT guarantees
a point c where f'(c) equals this slope.

## Key Applications

1. **L'Hopital's Rule**: Cauchy's MVT is the foundation for evaluating
   limits of indeterminate forms like 0/0 or ∞/∞.

2. **Taylor's Theorem**: The remainder term in Taylor expansions is
   expressed using MVT, guaranteeing error bounds.

3. **Monotonicity Testing**: If f' > 0 on an interval, f is strictly
   increasing (proven via MVT).

4. **Uniqueness of Antiderivatives**: Two antiderivatives of the same
   function differ by a constant (using constant_of_deriv_zero).
-/

end MeanValueTheorem

-- Verification that our theorems type-check correctly
#check MeanValueTheorem.mvt
#check MeanValueTheorem.mvt_hasDerivAt
#check MeanValueTheorem.cauchy_mvt
#check MeanValueTheorem.constant_of_deriv_zero
