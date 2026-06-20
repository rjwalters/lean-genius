/-
  Sum-to-product (prosthaphaeresis) identities and their triangle half-angle
  corollaries.

  The four **sum-to-product** identities turn a sum of two sinusoids into a
  product of two sinusoids:

      cos x + cos y =  2·cos((x+y)/2)·cos((x−y)/2)
      cos x − cos y = −2·sin((x+y)/2)·sin((x−y)/2)
      sin x + sin y =  2·sin((x+y)/2)·cos((x−y)/2)
      sin x − sin y =  2·cos((x+y)/2)·sin((x−y)/2)

  They are the converse of the Werner product-to-sum family (cf.
  `triangle-angle-sum-oq-04`/`oq-05`): there a product becomes a sum; here a
  sum becomes a product, factored through the **mean** (x+y)/2 and the
  **half-difference** (x−y)/2.  Each is proved directly from the addition
  formulas: writing x = (x+y)/2 + (x−y)/2 and y = (x+y)/2 − (x−y)/2, the two
  cosines (resp. sines) expand and combine.  Mathlib records these as
  `Real.cos_add_cos`, `Real.cos_sub_cos`, `Real.sin_add_sin`, `Real.sin_sub_sin`;
  the gallery had no sum-to-product identity, so they are anchored here, derived
  from `Real.cos_add` / `Real.cos_sub` rather than cited.

  The substantive content beyond Mathlib is the pair of **triangle half-angle
  product identities**, which Mathlib does not record.  For angles of a triangle
  (A + B + C = π):

      sin A + sin B + sin C = 4·cos(A/2)·cos(B/2)·cos(C/2)
      cos A + cos B + cos C = 1 + 4·sin(A/2)·sin(B/2)·sin(C/2).

  Both are the prosthaphaeresis payoff: pairing two of the three terms with a
  sum-to-product step and collapsing the half-angle (A+B)/2 = π/2 − C/2 turns
  the linear combination of three sinusoids into a single product of three
  half-angle factors.  They are proved here in the general "half-angle" form
  (for a + b + c = π/2) and specialised to the triangle.

  Verified: 0 sorries, 0 axioms (only the foundational propext / Classical.choice
  / Quot.sound; no native_decide, no Lean.ofReduceBool).
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.LinearCombination

open Real

namespace TriangleAngleSumOQ06

/-! ### The four sum-to-product (prosthaphaeresis) identities

Each is derived from the addition formulas via the mean / half-difference
substitution x = (x+y)/2 + (x−y)/2, y = (x+y)/2 − (x−y)/2. -/

/-- **Sum-to-product, cosine sum**: `cos x + cos y = 2·cos((x+y)/2)·cos((x−y)/2)`.
This is the `triangle-angle-sum-oq-06` identity, derived from `Real.cos_add` /
`Real.cos_sub` (it coincides with Mathlib's `Real.cos_add_cos`). -/
theorem cos_add_cos (x y : ℝ) :
    cos x + cos y = 2 * cos ((x + y) / 2) * cos ((x - y) / 2) := by
  have e1 : (x + y) / 2 + (x - y) / 2 = x := by ring
  have e2 : (x + y) / 2 - (x - y) / 2 = y := by ring
  calc cos x + cos y
      = cos ((x + y) / 2 + (x - y) / 2) + cos ((x + y) / 2 - (x - y) / 2) := by
        rw [e1, e2]
    _ = 2 * cos ((x + y) / 2) * cos ((x - y) / 2) := by
        rw [Real.cos_add, Real.cos_sub]; ring

/-- **Sum-to-product, cosine difference**:
`cos x − cos y = −2·sin((x+y)/2)·sin((x−y)/2)`. -/
theorem cos_sub_cos (x y : ℝ) :
    cos x - cos y = -2 * sin ((x + y) / 2) * sin ((x - y) / 2) := by
  have e1 : (x + y) / 2 + (x - y) / 2 = x := by ring
  have e2 : (x + y) / 2 - (x - y) / 2 = y := by ring
  calc cos x - cos y
      = cos ((x + y) / 2 + (x - y) / 2) - cos ((x + y) / 2 - (x - y) / 2) := by
        rw [e1, e2]
    _ = -2 * sin ((x + y) / 2) * sin ((x - y) / 2) := by
        rw [Real.cos_add, Real.cos_sub]; ring

/-- **Sum-to-product, sine sum**: `sin x + sin y = 2·sin((x+y)/2)·cos((x−y)/2)`.
This is the `triangle-angle-sum-oq-07` identity, derived from `Real.sin_add` /
`Real.sin_sub` (it coincides with Mathlib's `Real.sin_add_sin`). -/
theorem sin_add_sin (x y : ℝ) :
    sin x + sin y = 2 * sin ((x + y) / 2) * cos ((x - y) / 2) := by
  have e1 : (x + y) / 2 + (x - y) / 2 = x := by ring
  have e2 : (x + y) / 2 - (x - y) / 2 = y := by ring
  calc sin x + sin y
      = sin ((x + y) / 2 + (x - y) / 2) + sin ((x + y) / 2 - (x - y) / 2) := by
        rw [e1, e2]
    _ = 2 * sin ((x + y) / 2) * cos ((x - y) / 2) := by
        rw [Real.sin_add, Real.sin_sub]; ring

/-- **Sum-to-product, sine difference**:
`sin x − sin y = 2·cos((x+y)/2)·sin((x−y)/2)`. -/
theorem sin_sub_sin (x y : ℝ) :
    sin x - sin y = 2 * cos ((x + y) / 2) * sin ((x - y) / 2) := by
  have e1 : (x + y) / 2 + (x - y) / 2 = x := by ring
  have e2 : (x + y) / 2 - (x - y) / 2 = y := by ring
  calc sin x - sin y
      = sin ((x + y) / 2 + (x - y) / 2) - sin ((x + y) / 2 - (x - y) / 2) := by
        rw [e1, e2]
    _ = 2 * cos ((x + y) / 2) * sin ((x - y) / 2) := by
        rw [Real.sin_add, Real.sin_sub]; ring

/-! ### Triangle half-angle product identities

The original content: for a + b + c = π/2 (the half-angles of a triangle),
the sum of `sin (2·)` factors as `4·cos·cos·cos`, and the sum of `cos (2·)`
factors as `1 + 4·sin·sin·sin`.  These are not in Mathlib. -/

/-- **Half-angle sine identity**: if `a + b + c = π/2` then
`sin(2a) + sin(2b) + sin(2c) = 4·cos a·cos b·cos c`.

Substituting `c = π/2 − (a+b)` turns `sin(2c)` into `sin(2(a+b))` (via
`sin(π − ·) = sin`) and `cos c` into `sin(a+b)` (via `cos(π/2 − ·) = sin`);
expanding the double and sum angles reduces the goal to a polynomial identity
in `sin a, cos a, sin b, cos b`, closed by the Pythagorean identity. -/
theorem half_angle_sin_sum (a b c : ℝ) (h : a + b + c = π / 2) :
    sin (2 * a) + sin (2 * b) + sin (2 * c) = 4 * cos a * cos b * cos c := by
  have hc : c = π / 2 - (a + b) := by linarith
  subst hc
  have e1 : 2 * (π / 2 - (a + b)) = π - 2 * (a + b) := by ring
  rw [e1, Real.sin_pi_sub, Real.cos_pi_div_two_sub]
  simp only [Real.sin_two_mul, Real.sin_add, Real.cos_add]
  linear_combination (-2 * Real.sin a * Real.cos a) * Real.sin_sq_add_cos_sq b
    + (-2 * Real.sin b * Real.cos b) * Real.sin_sq_add_cos_sq a

/-- **Half-angle cosine identity**: if `a + b + c = π/2` then
`cos(2a) + cos(2b) + cos(2c) = 1 + 4·sin a·sin b·sin c`.

Substituting `c = π/2 − (a+b)` turns `cos(2c)` into `−cos(2(a+b))` (via
`cos(π − ·) = −cos`) and `sin c` into `cos(a+b)` (via `sin(π/2 − ·) = cos`);
expanding via the double-angle and addition formulas reduces to a polynomial
identity closed by the Pythagorean identity. -/
theorem half_angle_cos_sum (a b c : ℝ) (h : a + b + c = π / 2) :
    cos (2 * a) + cos (2 * b) + cos (2 * c) = 1 + 4 * sin a * sin b * sin c := by
  have hc : c = π / 2 - (a + b) := by linarith
  subst hc
  have e1 : 2 * (π / 2 - (a + b)) = π - 2 * (a + b) := by ring
  rw [e1, Real.cos_pi_sub, Real.sin_pi_div_two_sub]
  simp only [Real.cos_two_mul, Real.cos_add]
  linear_combination (2 - 2 * Real.cos b ^ 2) * Real.sin_sq_add_cos_sq a
    + (2 * Real.sin a ^ 2) * Real.sin_sq_add_cos_sq b

/-- **Triangle sine identity**: for the angles of a triangle (`A + B + C = π`),
`sin A + sin B + sin C = 4·cos(A/2)·cos(B/2)·cos(C/2)`.  A classical identity
not recorded in Mathlib; the prosthaphaeresis payoff. -/
theorem triangle_sin_sum (A B C : ℝ) (h : A + B + C = π) :
    sin A + sin B + sin C = 4 * cos (A / 2) * cos (B / 2) * cos (C / 2) := by
  have h2 : A / 2 + B / 2 + C / 2 = π / 2 := by linarith
  have key := half_angle_sin_sum (A / 2) (B / 2) (C / 2) h2
  rw [show 2 * (A / 2) = A by ring, show 2 * (B / 2) = B by ring,
     show 2 * (C / 2) = C by ring] at key
  exact key

/-- **Triangle cosine identity**: for the angles of a triangle (`A + B + C = π`),
`cos A + cos B + cos C = 1 + 4·sin(A/2)·sin(B/2)·sin(C/2)`.  A classical identity
not recorded in Mathlib. -/
theorem triangle_cos_sum (A B C : ℝ) (h : A + B + C = π) :
    cos A + cos B + cos C = 1 + 4 * sin (A / 2) * sin (B / 2) * sin (C / 2) := by
  have h2 : A / 2 + B / 2 + C / 2 = π / 2 := by linarith
  have key := half_angle_cos_sum (A / 2) (B / 2) (C / 2) h2
  rw [show 2 * (A / 2) = A by ring, show 2 * (B / 2) = B by ring,
     show 2 * (C / 2) = C by ring] at key
  exact key

/-! ### Worked instance -/

/-- The equilateral triangle (`A = B = C = π/3`) instance of the triangle sine
identity: `3·sin(π/3) = 4·cos(π/6)³`, obtained from `triangle_sin_sum` without
evaluating the surds. -/
example :
    sin (π / 3) + sin (π / 3) + sin (π / 3)
      = 4 * cos (π / 6) * cos (π / 6) * cos (π / 6) := by
  have key := triangle_sin_sum (π / 3) (π / 3) (π / 3) (by ring)
  rw [show (π / 3) / 2 = π / 6 by ring] at key
  exact key

end TriangleAngleSumOQ06
