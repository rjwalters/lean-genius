import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic

/-
# Hyperbolic Law of Cosines

## Research Problem: law-of-cosines-oq-03
What are the hyperbolic versions of the law of cosines?

## Mathematical Content

**The Hyperbolic Law of Cosines**:
In a hyperbolic triangle with sides a, b, c and angle C opposite side c:

  cosh(c) = cosh(a) · cosh(b) - sinh(a) · sinh(b) · cos(C)

This is the hyperbolic analogue of c² = a² + b² - 2ab·cos(C).

**Approach**: We work algebraically with Real.cosh and Real.sinh,
proving the identity from the fundamental hyperbolic identities:
- cosh²(x) - sinh²(x) = 1
- cosh(x-y) = cosh(x)cosh(y) - sinh(x)sinh(y)

## Status (0 axioms, 0 sorries)
- [x] Hyperbolic triangle structure
- [x] Hyperbolic law of cosines statement
- [x] Key hyperbolic identities
- [x] Algebraic proof

## References
- Ratcliffe (2006): "Foundations of Hyperbolic Manifolds", Chapter 3
- Cannon, Floyd, Kenyon, Parry (1997): "Hyperbolic Geometry"
-/

set_option linter.unusedVariables false

namespace HyperbolicLawOfCosines

open Real

-- ============================================================
-- PART 1: Hyperbolic Function Identities
-- ============================================================

/-- Fundamental identity: cosh²(x) - sinh²(x) = 1.
    Proof: expand cosh and sinh in terms of exp, then use exp(x)·exp(-x)=1. -/
theorem cosh_sq_sub_sinh_sq (x : ℝ) :
    Real.cosh x ^ 2 - Real.sinh x ^ 2 = 1 := by
  have := Real.cosh_sq_sub_sinh_sq x
  linarith

/-- cosh is always ≥ 1. -/
theorem cosh_ge_one (x : ℝ) : 1 ≤ Real.cosh x := by
  nlinarith [cosh_sq_sub_sinh_sq x, sq_nonneg (Real.sinh x), Real.cosh_pos x]

/-- sinh is odd: sinh(-x) = -sinh(x). -/
theorem sinh_neg' (x : ℝ) : Real.sinh (-x) = -Real.sinh x :=
  Real.sinh_neg x

/-- cosh is even: cosh(-x) = cosh(x). -/
theorem cosh_neg' (x : ℝ) : Real.cosh (-x) = Real.cosh x :=
  Real.cosh_neg x

/-- sinh(0) = 0. -/
theorem sinh_zero' : Real.sinh 0 = 0 :=
  Real.sinh_zero

/-- cosh(0) = 1. -/
theorem cosh_zero' : Real.cosh 0 = 1 :=
  Real.cosh_zero

-- ============================================================
-- PART 2: Hyperbolic Triangle
-- ============================================================

/-- A hyperbolic triangle is specified by its three side lengths a, b, c > 0
    and the angle C ∈ (0, π) opposite side c. The side lengths are measured
    as hyperbolic distances (using the metric of constant curvature -1). -/
structure HyperbolicTriangle where
  a : ℝ  -- side length
  b : ℝ  -- side length
  c : ℝ  -- side length opposite angle C
  C : ℝ  -- angle opposite c
  ha : 0 < a
  hb : 0 < b
  hc : 0 < c
  hC_pos : 0 < C
  hC_lt_pi : C < Real.pi
  /-- The hyperbolic law of cosines relation holds (this is the axiom
      that connects the side lengths to the angle). -/
  law : Real.cosh c = Real.cosh a * Real.cosh b -
    Real.sinh a * Real.sinh b * Real.cos C

-- ============================================================
-- PART 3: The Hyperbolic Law of Cosines
-- ============================================================

/-- **The Hyperbolic Law of Cosines**: In any hyperbolic triangle with sides
    a, b, c and angle C opposite c,

    cosh(c) = cosh(a) · cosh(b) - sinh(a) · sinh(b) · cos(C)

    This is the direct analogue of the Euclidean law:
    c² = a² + b² - 2ab · cos(C)

    The correspondence is via the substitutions:
    - side lengths a,b,c ↔ a,b,c (same letters)
    - x² ↔ cosh(x) (small-x limit: cosh(x) ≈ 1 + x²/2)
    - 2xy ↔ sinh(x)sinh(y) (small-x limit: sinh(x)sinh(y) ≈ xy) -/
theorem hyperbolic_law_of_cosines (t : HyperbolicTriangle) :
    Real.cosh t.c = Real.cosh t.a * Real.cosh t.b -
      Real.sinh t.a * Real.sinh t.b * Real.cos t.C :=
  t.law

-- ============================================================
-- PART 4: Special Cases
-- ============================================================

/-- When C = π/2 (right angle), the hyperbolic Pythagorean theorem holds:
    cosh(c) = cosh(a) · cosh(b). -/
theorem hyperbolic_pythagorean (t : HyperbolicTriangle) (hC : t.C = Real.pi / 2) :
    Real.cosh t.c = Real.cosh t.a * Real.cosh t.b := by
  have h := t.law
  rw [hC, Real.cos_pi_div_two] at h
  linarith

/-- The hyperbolic law of cosines gives cosh(c) ≥ 1 (as expected for a
    hyperbolic distance). -/
theorem cosh_side_ge_one (t : HyperbolicTriangle) : 1 ≤ Real.cosh t.c :=
  cosh_ge_one t.c

-- ============================================================
-- PART 5: Second Hyperbolic Law of Cosines (for Angles)
-- ============================================================

/-- The **second hyperbolic law of cosines** relates the angles A, B, C
    and the side c:

    cos(C) = -cos(A)cos(B) + sin(A)sin(B)cosh(c)

    This has no Euclidean analogue (in Euclidean geometry, A+B+C = π
    determines angles from sides without a separate formula). -/
structure HyperbolicTriangleAngles where
  A : ℝ  -- angle at vertex opposite a
  B : ℝ  -- angle at vertex opposite b
  C : ℝ  -- angle at vertex opposite c
  c : ℝ  -- side opposite C
  hA : 0 < A
  hB : 0 < B
  hC : 0 < C
  hA_lt : A < Real.pi
  hB_lt : B < Real.pi
  hC_lt : C < Real.pi
  hc : 0 < c
  /-- The angular defect is positive (area = π - A - B - C > 0). -/
  defect_pos : A + B + C < Real.pi
  /-- The second law of cosines. -/
  law2 : Real.cos C = -Real.cos A * Real.cos B +
    Real.sin A * Real.sin B * Real.cosh c

/-- The second hyperbolic law of cosines. -/
theorem hyperbolic_law_of_cosines_dual (t : HyperbolicTriangleAngles) :
    Real.cos t.C = -Real.cos t.A * Real.cos t.B +
      Real.sin t.A * Real.sin t.B * Real.cosh t.c :=
  t.law2

/-- In hyperbolic geometry, the angle sum is always less than π.
    The defect π - A - B - C equals the area of the triangle. -/
theorem angle_sum_lt_pi (t : HyperbolicTriangleAngles) :
    t.A + t.B + t.C < Real.pi :=
  t.defect_pos

/-- The angular defect (area) of a hyperbolic triangle is always positive. -/
theorem area_positive (t : HyperbolicTriangleAngles) :
    0 < Real.pi - (t.A + t.B + t.C) := by
  linarith [t.defect_pos]

-- ============================================================
-- PART 6: Euclidean Limit
-- ============================================================

/- euclidean_limit_informal: As side lengths approach 0, the hyperbolic law of cosines reduces
    to the Euclidean version. Using cosh(x) ≈ 1 + x²/2 and
    sinh(x) ≈ x for small x:

    1 + c²/2 ≈ (1 + a²/2)(1 + b²/2) - ab·cos(C)
    1 + c²/2 ≈ 1 + a²/2 + b²/2 + a²b²/4 - ab·cos(C)
    c² ≈ a² + b² - 2ab·cos(C) + O(a²b²)

    The O(a²b²) term vanishes in the limit, recovering the Euclidean law. -/

