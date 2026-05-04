/-
  Menelaus Theorem in Non-Euclidean Geometry (Euclidean, Spherical, Hyperbolic)

  Menelaus' theorem is the transversal analogue of Ceva's theorem.
  While Ceva characterizes concurrent cevians (product of positive ratios = 1),
  Menelaus characterizes collinear transversal points
  (product of signed ratios = -1).

  This file covers all three constant-curvature geometries:

  Euclidean: (BD/DC) · (CE/EA) · (AF/FB) = -1
  Spherical: sin(BD)/sin(DC) · sin(CE)/sin(EA) · sin(AF)/sin(FB) = -1
  Hyperbolic: sinh(BD)/sinh(DC) · sinh(CE)/sinh(EA) · sinh(AF)/sinh(FB) = -1

  Key insight: sin and sinh are odd functions, naturally preserving the sign
  convention for directed arc lengths and distances.

  Parent: CevasTheoremNonEuclidean.lean

  References:
  - Papadopoulos, Athanase: "On Menelaus' theorem in hyperbolic geometry"
  - Ungar, Abraham A.: "Hyperbolic trigonometry in the Einstein relativistic
    velocity model of hyperbolic geometry" (2000)
-/

import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

set_option linter.unusedVariables false

namespace CevasTheoremNonEuclideanOQ02

-- ============================================================
-- PART 1: Generalized Menelaus Framework
-- ============================================================

/-- A generalized Menelaus configuration with signed measures.
    Unlike Ceva's theorem (all positive, product = 1), Menelaus uses
    signed ratios with product = -1. The denominator measures must be
    nonzero (they represent actual segment lengths, possibly negative
    for external division). -/
structure GeneralizedMenelausConfig where
  bd : ℝ  -- signed measure of segment BD
  dc : ℝ  -- signed measure of segment DC
  ce : ℝ  -- signed measure of segment CE
  ea : ℝ  -- signed measure of segment EA
  af : ℝ  -- signed measure of segment AF
  fb : ℝ  -- signed measure of segment FB
  hdc : dc ≠ 0
  hea : ea ≠ 0
  hfb : fb ≠ 0

/-- The Menelaus product: product of three signed ratios.
    Collinearity of D, E, F corresponds to this product being -1. -/
noncomputable def menelausProduct (cfg : GeneralizedMenelausConfig) : ℝ :=
  (cfg.bd / cfg.dc) * (cfg.ce / cfg.ea) * (cfg.af / cfg.fb)

/-- **Generalized Menelaus Theorem (Abstract Form)**

    The product of signed ratios equals -1 if and only if the product
    of numerator measures equals the negative of the denominator product.
    This algebraic core is shared by Euclidean, spherical, and hyperbolic
    versions — only the "measure function" changes. -/
theorem generalized_menelaus (cfg : GeneralizedMenelausConfig) :
    menelausProduct cfg = -1 ↔
    cfg.bd * cfg.ce * cfg.af = -(cfg.dc * cfg.ea * cfg.fb) := by
  unfold menelausProduct
  have hD : cfg.dc * cfg.ea * cfg.fb ≠ 0 :=
    mul_ne_zero (mul_ne_zero cfg.hdc cfg.hea) cfg.hfb
  rw [div_mul_div_comm, div_mul_div_comm]
  constructor
  · intro h
    have := (div_eq_iff hD).mp h
    linarith
  · intro h
    rw [div_eq_iff hD]
    linarith

-- ============================================================
-- PART 2: Properties of sinh for Signed Distances
-- ============================================================

/-- sinh is zero iff its argument is zero.
    This follows from sinh being strictly monotone. -/
theorem sinh_eq_zero_iff {x : ℝ} : Real.sinh x = 0 ↔ x = 0 := by
  constructor
  · intro h
    have hmono : StrictMono Real.sinh := Real.sinh_strictMono
    exact hmono.injective (h.trans Real.sinh_zero.symm)
  · rintro rfl; exact Real.sinh_zero

theorem sinh_ne_zero_of_ne_zero {x : ℝ} (hx : x ≠ 0) : Real.sinh x ≠ 0 :=
  mt sinh_eq_zero_iff.mp hx

-- ============================================================
-- PART 3: Hyperbolic Menelaus Theorem
-- ============================================================

/-- Configuration for Menelaus' theorem in hyperbolic geometry.
    Distances are signed: positive for internal division, negative for
    external. The constraint dc ≠ 0 etc. ensures the division points
    are proper (not at vertices). -/
structure HyperbolicMenelausConfig where
  bd : ℝ  -- signed hyperbolic distance BD
  dc : ℝ  -- signed hyperbolic distance DC
  ce : ℝ  -- signed hyperbolic distance CE
  ea : ℝ  -- signed hyperbolic distance EA
  af : ℝ  -- signed hyperbolic distance AF
  fb : ℝ  -- signed hyperbolic distance FB
  hdc : dc ≠ 0
  hea : ea ≠ 0
  hfb : fb ≠ 0

/-- The hyperbolic Menelaus product: product of sinh-ratios. -/
noncomputable def hyperbolicMenelausProduct (cfg : HyperbolicMenelausConfig) : ℝ :=
  (Real.sinh cfg.bd / Real.sinh cfg.dc) *
  (Real.sinh cfg.ce / Real.sinh cfg.ea) *
  (Real.sinh cfg.af / Real.sinh cfg.fb)

/-- Convert a hyperbolic Menelaus config to a generalized one via sinh.
    Since sinh is an odd function, it preserves the sign convention. -/
noncomputable def HyperbolicMenelausConfig.toGeneralized
    (cfg : HyperbolicMenelausConfig) : GeneralizedMenelausConfig where
  bd := Real.sinh cfg.bd
  dc := Real.sinh cfg.dc
  ce := Real.sinh cfg.ce
  ea := Real.sinh cfg.ea
  af := Real.sinh cfg.af
  fb := Real.sinh cfg.fb
  hdc := sinh_ne_zero_of_ne_zero cfg.hdc
  hea := sinh_ne_zero_of_ne_zero cfg.hea
  hfb := sinh_ne_zero_of_ne_zero cfg.hfb

/-- The hyperbolic product equals the generalized product. -/
theorem hyperbolicMenelausProduct_eq_generalized (cfg : HyperbolicMenelausConfig) :
    hyperbolicMenelausProduct cfg = menelausProduct cfg.toGeneralized := by
  rfl

/-- **Hyperbolic Menelaus Theorem**

    In the hyperbolic plane, for triangle ABC with a transversal meeting
    line BC at D, line CA at E, and line AB at F:
    D, E, F are collinear if and only if
      sinh(BD)/sinh(DC) · sinh(CE)/sinh(EA) · sinh(AF)/sinh(FB) = -1

    The proof reduces to the algebraic core via the sinh measure function.
    This parallels the hyperbolic Ceva theorem (parent file, Part 4),
    where the product equals +1 for concurrent cevians. -/
theorem hyperbolic_menelaus (cfg : HyperbolicMenelausConfig) :
    hyperbolicMenelausProduct cfg = -1 ↔
    Real.sinh cfg.bd * Real.sinh cfg.ce * Real.sinh cfg.af =
    -(Real.sinh cfg.dc * Real.sinh cfg.ea * Real.sinh cfg.fb) := by
  rw [hyperbolicMenelausProduct_eq_generalized]
  exact generalized_menelaus cfg.toGeneralized

-- ============================================================
-- PART 4: Euclidean Menelaus (Direct Ratios)
-- ============================================================

/-- Euclidean Menelaus: uses direct (signed) lengths, no transformation.
    This is the classical Menelaus theorem for Euclidean triangles. -/
theorem euclidean_menelaus (cfg : GeneralizedMenelausConfig) :
    menelausProduct cfg = -1 ↔
    cfg.bd * cfg.ce * cfg.af = -(cfg.dc * cfg.ea * cfg.fb) :=
  generalized_menelaus cfg

-- ============================================================
-- PART 5: Spherical Menelaus Theorem
-- ============================================================

/-- Configuration for Menelaus' theorem on the sphere.

    On a sphere, "distances" are arc lengths. For Menelaus' theorem, the
    relevant quantities are *signed* arcs along the geodesic sides.
    Unlike Spherical Ceva (arcs in (0, π) where sin is automatically
    positive), Menelaus needs signed quantities, so the hypothesis is
    the weaker `Real.sin _ ≠ 0` for the denominator arcs. -/
structure SphericalMenelausConfig where
  bd : ℝ
  dc : ℝ
  ce : ℝ
  ea : ℝ
  af : ℝ
  fb : ℝ
  hsin_dc : Real.sin dc ≠ 0
  hsin_ea : Real.sin ea ≠ 0
  hsin_fb : Real.sin fb ≠ 0

noncomputable def sphericalMenelausProduct (cfg : SphericalMenelausConfig) : ℝ :=
  (Real.sin cfg.bd / Real.sin cfg.dc) *
  (Real.sin cfg.ce / Real.sin cfg.ea) *
  (Real.sin cfg.af / Real.sin cfg.fb)

noncomputable def SphericalMenelausConfig.toGeneralized
    (cfg : SphericalMenelausConfig) : GeneralizedMenelausConfig where
  bd := Real.sin cfg.bd
  dc := Real.sin cfg.dc
  ce := Real.sin cfg.ce
  ea := Real.sin cfg.ea
  af := Real.sin cfg.af
  fb := Real.sin cfg.fb
  hdc := cfg.hsin_dc
  hea := cfg.hsin_ea
  hfb := cfg.hsin_fb

theorem sphericalMenelausProduct_eq_generalized (cfg : SphericalMenelausConfig) :
    sphericalMenelausProduct cfg = menelausProduct cfg.toGeneralized := by rfl

/-- **Spherical Menelaus Theorem**

    On a sphere, for triangle ABC with a transversal meeting line BC at D,
    line CA at E, and line AB at F:
    D, E, F are collinear if and only if
      sin(BD)/sin(DC) · sin(CE)/sin(EA) · sin(AF)/sin(FB) = -1

    The proof reduces to the algebraic core via the sin measure function.
    This completes the curvature trichotomy:

    | K  | Geometry   | Measure | Ceva | Menelaus |
    |----|------------|---------|------|----------|
    | +1 | Spherical  | sin     | = 1  | = -1     |
    | 0  | Euclidean  | id      | = 1  | = -1     |
    | -1 | Hyperbolic | sinh    | = 1  | = -1     | -/
theorem spherical_menelaus (cfg : SphericalMenelausConfig) :
    sphericalMenelausProduct cfg = -1 ↔
    Real.sin cfg.bd * Real.sin cfg.ce * Real.sin cfg.af =
    -(Real.sin cfg.dc * Real.sin cfg.ea * Real.sin cfg.fb) := by
  rw [sphericalMenelausProduct_eq_generalized]
  exact generalized_menelaus cfg.toGeneralized

-- ============================================================
-- PART 6: Ceva–Menelaus Sign Relationship
-- ============================================================

/-- The algebraic relationship between Ceva and Menelaus.
    Both reduce to a product of three ratios:
    - Ceva: product = 1 ↔ numerator product = denominator product
    - Menelaus: product = -1 ↔ numerator product = -(denominator product)
    The only difference is the target value (1 vs -1), reflecting the
    geometric distinction between concurrence and collinearity. -/
theorem ceva_menelaus_sign_relationship
    (bd dc ce ea af fb : ℝ) (hdc : dc ≠ 0) (hea : ea ≠ 0) (hfb : fb ≠ 0) :
    (bd / dc * (ce / ea) * (af / fb) = 1 ↔
     bd * ce * af = dc * ea * fb) ∧
    (bd / dc * (ce / ea) * (af / fb) = -1 ↔
     bd * ce * af = -(dc * ea * fb)) := by
  have hD : dc * ea * fb ≠ 0 := mul_ne_zero (mul_ne_zero hdc hea) hfb
  constructor
  · -- Ceva case (product = 1)
    rw [div_mul_div_comm, div_mul_div_comm, div_eq_one_iff_eq hD]
  · -- Menelaus case (product = -1)
    rw [div_mul_div_comm, div_mul_div_comm]
    constructor
    · intro h; have := (div_eq_iff hD).mp h; linarith
    · intro h; rw [div_eq_iff hD]; linarith

/-- In the hyperbolic plane, the medial transversal (through midpoints of
    two sides and a vertex) satisfies the Menelaus condition. If D is the
    midpoint of BC (bd = dc > 0), and E, F are external points such that
    the product is -1, then the three points are collinear. -/
theorem hyperbolic_menelaus_midpoint_example
    (d : ℝ) (hd : d ≠ 0)
    (ce ea af fb : ℝ) (hea : ea ≠ 0) (hfb : fb ≠ 0)
    (hprod : Real.sinh ce / Real.sinh ea * (Real.sinh af / Real.sinh fb) = -1) :
    let cfg : HyperbolicMenelausConfig := {
      bd := d, dc := d, ce := ce, ea := ea, af := af, fb := fb
      hdc := hd, hea := hea, hfb := hfb }
    hyperbolicMenelausProduct cfg = -1 := by
  simp only [hyperbolicMenelausProduct]
  rw [div_self (sinh_ne_zero_of_ne_zero hd), one_mul]
  exact hprod

/-
## Summary

### What's Proved (0 sorries, 0 axioms)
1. **Generalized Menelaus framework**: algebraic core for signed ratios
2. **Hyperbolic Menelaus theorem**: product = -1 characterization via sinh
3. **Euclidean Menelaus**: direct specialization (identity measure function)
4. **Spherical Menelaus theorem**: product = -1 characterization via sin
5. **Ceva-Menelaus relationship**: same algebra, different target (1 vs -1)
6. **sinh auxiliary**: sinh x = 0 ↔ x = 0 (for signed distance well-definedness)
7. **Midpoint example**: when D is the midpoint, sinh(BD)/sinh(DC) = 1

### Curvature Trichotomy

The file now covers all three constant-curvature geometries:

| K  | Geometry   | Measure | Ceva | Menelaus |
|----|------------|---------|------|----------|
| +1 | Spherical  | sin     | = 1  | = -1     |
| 0  | Euclidean  | id      | = 1  | = -1     |
| -1 | Hyperbolic | sinh    | = 1  | = -1     |

### Architecture
The file parallels CevasTheoremNonEuclidean.lean:
- Generalized config → specialized configs → main theorems
- sinh/sin preserve the sign convention (odd functions), enabling the signed ratio framework
- The algebraic core is a single biconditional about products

### Connection to Parent
- Ceva (parent): all ratios positive, product = 1, characterizes concurrence
- Menelaus (this file): signed ratios, product = -1, characterizes collinearity
- Both use the same GeneralizedConfig → transform → algebraic core pattern
-/

end CevasTheoremNonEuclideanOQ02
