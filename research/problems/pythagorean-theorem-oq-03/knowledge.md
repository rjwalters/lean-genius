# Knowledge Base

## Insights
- Non-Euclidean Pythagorean theorems (hyperbolic: cosh(c)=cosh(a)cosh(b), spherical: cos(c)=cos(a)cos(b)) share algebraic structure f(c) = f(a)·f(b)
- MVT-based proofs (monotoneOn_of_deriv_nonneg) effective for inequalities like sinh(x) >= x and cosh(x) >= 1 + x²/2
- Generalized cosine C_κ parameterized by curvature unifies all three geometries
- All results provable from Mathlib's exponential and trigonometric library - no axioms needed
- cosh strict monotonicity on [0,∞) enables converting cosh-level inequalities to side-length inequalities

## Built Items
- sinh_ge_id: sinh(x) >= x for x >= 0 via MVT
- cosh_ge_one_add_sq_div_two: cosh(x) >= 1 + x²/2 for all x (convexity bound)
- cosh_product_ge_approx: cosh(a)·cosh(b) >= 1 + (a²+b²)/2

## References
- Mathlib.Analysis.Calculus.MeanValue (monotoneOn_of_deriv_nonneg)
- Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic (cosh, sinh, cos, sin)
- Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv (HasDerivAt for trig)
