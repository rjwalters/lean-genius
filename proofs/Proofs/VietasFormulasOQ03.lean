/-
# Newton's Identities

Newton's identities express the power sums pₖ = ∑ xᵢᵏ in terms of
elementary symmetric polynomials eⱼ, and vice versa.

For n variables x₁, ..., xₙ:
  p₁ = e₁
  p₂ = e₁ · p₁ − 2 · e₂
  p₃ = e₁ · p₂ − e₂ · p₁ + 3 · e₃
  p₄ = e₁ · p₃ − e₂ · p₂ + e₃ · p₁ − 4 · e₄

General form:
  pₖ = ∑_{i=1}^{k} (−1)^{i−1} eᵢ · p_{k−i}  for i < k
       + (−1)^{k−1} · k · eₖ

These identities are fundamental to symmetric function theory and connect
Vieta's formulas (coefficients ↔ roots) to trace-like invariants.

Isaac Newton stated these in Arithmetica Universalis (1707), though
Albert Girard had earlier versions (1629).

Applications:
- Computing traces of matrix powers from characteristic polynomial
- Expressing discriminants via power sums
- The Cayley–Hamilton trace identities
-/

import Mathlib.Tactic

namespace NewtonIdentities

/-
## Two Variables

Elementary symmetric polynomials of x, y:
  e₁ = x + y
  e₂ = x · y

Power sums:
  p₁ = x + y
  p₂ = x² + y²
  p₃ = x³ + y³
  p₄ = x⁴ + y⁴
-/
section TwoVariables

variable {R : Type*} [CommRing R] (x y : R)

/-- Newton's first identity (n = 2): p₁ = e₁.
    Trivially, the sum of first powers equals e₁. -/
theorem newton_id_2_1 :
    x + y = (x + y) := rfl

/-- Newton's second identity (n = 2): p₂ = e₁ · p₁ − 2 · e₂.
    x² + y² = (x + y)² − 2xy -/
theorem newton_id_2_2 :
    x ^ 2 + y ^ 2 = (x + y) ^ 2 - 2 * (x * y) := by ring

/-- Newton's third identity (n = 2): p₃ = e₁ · p₂ − e₂ · p₁.
    x³ + y³ = (x + y)(x² + y²) − xy(x + y) -/
theorem newton_id_2_3 :
    x ^ 3 + y ^ 3 =
    (x + y) * (x ^ 2 + y ^ 2) - (x * y) * (x + y) := by ring

/-- Newton's fourth identity (n = 2): p₄ = e₁ · p₃ − e₂ · p₂.
    x⁴ + y⁴ = (x + y)(x³ + y³) − xy(x² + y²) -/
theorem newton_id_2_4 :
    x ^ 4 + y ^ 4 =
    (x + y) * (x ^ 3 + y ^ 3) - (x * y) * (x ^ 2 + y ^ 2) := by ring

/-- Express p₂ purely in terms of e₁, e₂. -/
theorem power_sum_2_via_esymm :
    x ^ 2 + y ^ 2 = (x + y) ^ 2 - 2 * (x * y) := by ring

/-- Express p₃ purely in terms of e₁, e₂. -/
theorem power_sum_3_via_esymm_2var :
    x ^ 3 + y ^ 3 = (x + y) ^ 3 - 3 * (x * y) * (x + y) := by ring

/-- Express p₄ purely in terms of e₁, e₂.
    p₄ = e₁⁴ − 4e₁²e₂ + 2e₂² -/
theorem power_sum_4_via_esymm_2var :
    x ^ 4 + y ^ 4 =
    (x + y) ^ 4 - 4 * (x * y) * (x + y) ^ 2 + 2 * (x * y) ^ 2 := by ring

end TwoVariables

/-
## Three Variables

Elementary symmetric polynomials of x, y, z:
  e₁ = x + y + z
  e₂ = xy + xz + yz
  e₃ = xyz

Power sums:
  p₁ = x + y + z
  p₂ = x² + y² + z²
  p₃ = x³ + y³ + z³
  p₄ = x⁴ + y⁴ + z⁴
-/
section ThreeVariables

variable {R : Type*} [CommRing R] (x y z : R)

-- Convenient abbreviations (noncomputable to avoid decidability)
private abbrev e1_3 (x y z : R) := x + y + z
private abbrev e2_3 (x y z : R) := x * y + x * z + y * z
private abbrev e3_3 (x y z : R) := x * y * z
private abbrev p1_3 (x y z : R) := x + y + z
private abbrev p2_3 (x y z : R) := x ^ 2 + y ^ 2 + z ^ 2
private abbrev p3_3 (x y z : R) := x ^ 3 + y ^ 3 + z ^ 3
private abbrev p4_3 (x y z : R) := x ^ 4 + y ^ 4 + z ^ 4

/-- Newton's first identity (n = 3): p₁ = e₁ -/
theorem newton_id_3_1 :
    p1_3 x y z = e1_3 x y z := rfl

/-- Newton's second identity (n = 3): p₂ = e₁ · p₁ − 2 · e₂ -/
theorem newton_id_3_2 :
    p2_3 x y z =
    e1_3 x y z * p1_3 x y z - 2 * e2_3 x y z := by
  unfold p2_3 e1_3 p1_3 e2_3; ring

/-- Newton's third identity (n = 3): p₃ = e₁ · p₂ − e₂ · p₁ + 3 · e₃ -/
theorem newton_id_3_3 :
    p3_3 x y z =
    e1_3 x y z * p2_3 x y z - e2_3 x y z * p1_3 x y z
    + 3 * e3_3 x y z := by
  unfold p3_3 e1_3 p2_3 e2_3 p1_3 e3_3; ring

/-- Newton's fourth identity (n = 3): p₄ = e₁·p₃ − e₂·p₂ + e₃·p₁ -/
theorem newton_id_3_4 :
    p4_3 x y z =
    e1_3 x y z * p3_3 x y z - e2_3 x y z * p2_3 x y z
    + e3_3 x y z * p1_3 x y z := by
  unfold p4_3 e1_3 p3_3 e2_3 p2_3 e3_3 p1_3; ring

/-- Express p₂ purely in terms of e₁, e₂ (3 variables). -/
theorem power_sum_2_via_esymm_3var :
    p2_3 x y z = (e1_3 x y z) ^ 2 - 2 * e2_3 x y z := by
  unfold p2_3 e1_3 e2_3; ring

/-- Express p₃ purely in terms of e₁, e₂, e₃ (3 variables).
    p₃ = e₁³ − 3e₁e₂ + 3e₃ -/
theorem power_sum_3_via_esymm_3var :
    p3_3 x y z =
    (e1_3 x y z) ^ 3 - 3 * e1_3 x y z * e2_3 x y z
    + 3 * e3_3 x y z := by
  unfold p3_3 e1_3 e2_3 e3_3; ring

/-- Express p₄ purely in terms of e₁, e₂, e₃ (3 variables).
    p₄ = e₁⁴ − 4e₁²e₂ + 2e₂² + 4e₁e₃ -/
theorem power_sum_4_via_esymm_3var :
    p4_3 x y z =
    (e1_3 x y z) ^ 4 - 4 * (e1_3 x y z) ^ 2 * e2_3 x y z
    + 2 * (e2_3 x y z) ^ 2 + 4 * e1_3 x y z * e3_3 x y z := by
  unfold p4_3 e1_3 e2_3 e3_3; ring

end ThreeVariables

/-
## Four Variables

Elementary symmetric polynomials of a, b, c, d:
  e₁ = a + b + c + d
  e₂ = ab + ac + ad + bc + bd + cd
  e₃ = abc + abd + acd + bcd
  e₄ = abcd
-/
section FourVariables

variable {R : Type*} [CommRing R] (a b c d : R)

private abbrev e1_4 (a b c d : R) := a + b + c + d
private abbrev e2_4 (a b c d : R) := a*b + a*c + a*d + b*c + b*d + c*d
private abbrev e3_4 (a b c d : R) := a*b*c + a*b*d + a*c*d + b*c*d
private abbrev e4_4 (a b c d : R) := a * b * c * d
private abbrev p1_4 (a b c d : R) := a + b + c + d
private abbrev p2_4 (a b c d : R) := a^2 + b^2 + c^2 + d^2
private abbrev p3_4 (a b c d : R) := a^3 + b^3 + c^3 + d^3
private abbrev p4_4 (a b c d : R) := a^4 + b^4 + c^4 + d^4

/-- Newton's second identity (n = 4): p₂ = e₁·p₁ − 2·e₂ -/
theorem newton_id_4_2 :
    p2_4 a b c d =
    e1_4 a b c d * p1_4 a b c d - 2 * e2_4 a b c d := by
  unfold p2_4 e1_4 p1_4 e2_4; ring

/-- Newton's third identity (n = 4): p₃ = e₁·p₂ − e₂·p₁ + 3·e₃ -/
theorem newton_id_4_3 :
    p3_4 a b c d =
    e1_4 a b c d * p2_4 a b c d - e2_4 a b c d * p1_4 a b c d
    + 3 * e3_4 a b c d := by
  unfold p3_4 e1_4 p2_4 e2_4 p1_4 e3_4; ring

/-- Newton's fourth identity (n = 4): p₄ = e₁·p₃ − e₂·p₂ + e₃·p₁ − 4·e₄ -/
theorem newton_id_4_4 :
    p4_4 a b c d =
    e1_4 a b c d * p3_4 a b c d - e2_4 a b c d * p2_4 a b c d
    + e3_4 a b c d * p1_4 a b c d - 4 * e4_4 a b c d := by
  unfold p4_4 e1_4 p3_4 e2_4 p2_4 e3_4 p1_4 e4_4; ring

end FourVariables

/-
## Inversion: Elementary Symmetric from Power Sums

Newton's identities also work in reverse — expressing eₖ in terms of
power sums. This is useful for recovering polynomial coefficients
from traces of matrix powers.
-/
section Inversion

variable {R : Type*} [Field R] [CharZero R] (x y z : R)

/-- Recover e₂ from p₁, p₂ (2 or 3 variables):
    e₂ = (p₁² − p₂) / 2 -/
theorem esymm2_from_power_sums :
    x * y + x * z + y * z =
    ((x + y + z) ^ 2 - (x ^ 2 + y ^ 2 + z ^ 2)) / 2 := by
  field_simp; ring

/-- Recover e₃ from p₁, p₂, p₃ (3 variables):
    e₃ = (p₁³ − 3p₁p₂ + 2p₃) / 6 -/
theorem esymm3_from_power_sums :
    x * y * z =
    ((x + y + z) ^ 3 - 3 * (x + y + z) * (x ^ 2 + y ^ 2 + z ^ 2)
     + 2 * (x ^ 3 + y ^ 3 + z ^ 3)) / 6 := by
  field_simp; ring

end Inversion

/-
## Application: Polynomial Discriminant

The discriminant of a polynomial can be expressed via power sums.
For a monic quadratic x² − sx + p with roots r₁, r₂:
  Δ = (r₁ − r₂)² = p₂ − p₁² + 2·(r₁r₂) · 2  ... simplifies to
  Δ = s² − 4p = e₁² − 4e₂
-/
section Discriminant

variable {R : Type*} [CommRing R]

/-- The discriminant of a monic quadratic in terms of roots. -/
theorem discriminant_quadratic (r₁ r₂ : R) :
    (r₁ - r₂) ^ 2 = (r₁ + r₂) ^ 2 - 4 * (r₁ * r₂) := by ring

/-- The discriminant in terms of power sums.
    Δ = (r₁ − r₂)² = 2p₂ − p₁²  (using p₂ = r₁²+r₂² and p₁ = r₁+r₂) -/
theorem discriminant_via_power_sums (r₁ r₂ : R) :
    (r₁ - r₂) ^ 2 = 2 * (r₁ ^ 2 + r₂ ^ 2) - (r₁ + r₂) ^ 2 := by ring

/-- Cubic discriminant in terms of elementary symmetric polynomials.
    For x³ − e₁x² + e₂x − e₃ with roots r₁, r₂, r₃:
    Δ = e₁²e₂² − 4e₂³ − 4e₁³e₃ + 18e₁e₂e₃ − 27e₃² -/
theorem discriminant_cubic (r₁ r₂ r₃ : R) :
    (r₁ - r₂) ^ 2 * (r₁ - r₃) ^ 2 * (r₂ - r₃) ^ 2 =
    let e₁ := r₁ + r₂ + r₃
    let e₂ := r₁ * r₂ + r₁ * r₃ + r₂ * r₃
    let e₃ := r₁ * r₂ * r₃
    e₁ ^ 2 * e₂ ^ 2 - 4 * e₂ ^ 3 - 4 * e₁ ^ 3 * e₃
    + 18 * e₁ * e₂ * e₃ - 27 * e₃ ^ 2 := by ring

end Discriminant

/-
## Application: Matrix Traces

For an n×n matrix A with eigenvalues λ₁, ..., λₙ:
  tr(A) = p₁ = e₁
  tr(A²) = p₂ = e₁² − 2e₂
  tr(A³) = p₃ = e₁³ − 3e₁e₂ + 3e₃

The characteristic polynomial is det(xI − A) = xⁿ − e₁xⁿ⁻¹ + e₂xⁿ⁻² − ...
So Newton's identities recover the characteristic polynomial from traces alone.

We demonstrate this for 2×2 matrices.
-/
section MatrixTrace

variable {R : Type*} [CommRing R] (μ₁ μ₂ : R)

/-- For a 2×2 matrix: the second coefficient of the characteristic polynomial
    equals (tr² − tr(A²)) / 2, i.e., e₂ = (p₁² − p₂) / 2 -/
theorem char_poly_from_traces_2x2 :
    2 * (μ₁ * μ₂) = (μ₁ + μ₂) ^ 2 - (μ₁ ^ 2 + μ₂ ^ 2) := by ring

/-- For a 2×2 matrix: the Cayley-Hamilton identity in trace form.
    A² - tr(A)A + det(A)I = 0
    Equivalently: p₂ - e₁p₁ + 2e₂ = 0 (which is Newton's identity!) -/
theorem cayley_hamilton_trace_2x2 :
    (μ₁ ^ 2 + μ₂ ^ 2) - (μ₁ + μ₂) * (μ₁ + μ₂) + 2 * (μ₁ * μ₂) = 0 := by ring

end MatrixTrace

/-
## Classical Form: Recurrence

Newton's identities can be stated as a single recurrence:
  pₖ = ∑_{i=1}^{min(k,n)} (−1)^{i−1} eᵢ · p_{k−i}  +  (−1)^{k−1} · k · eₖ [if k ≤ n]
  pₖ = ∑_{i=1}^{n} (−1)^{i−1} eᵢ · p_{k−i}                                    [if k > n]

For k > n, the eₖ term vanishes (eₖ = 0 for k > n variables).
We verify the recurrence formula for all identities proved above.
-/
section Recurrence

variable {R : Type*} [CommRing R]

/-- Recurrence check: For 3 variables, p₅ uses only e₁, e₂, e₃ since e₄ = e₅ = 0.
    p₅ = e₁·p₄ − e₂·p₃ + e₃·p₂ -/
theorem newton_id_3_5 (x y z : R) :
    x ^ 5 + y ^ 5 + z ^ 5 =
    (x + y + z) * (x ^ 4 + y ^ 4 + z ^ 4)
    - (x*y + x*z + y*z) * (x ^ 3 + y ^ 3 + z ^ 3)
    + (x*y*z) * (x ^ 2 + y ^ 2 + z ^ 2) := by ring

/-- Recurrence check: For 2 variables, p₅ = e₁·p₄ − e₂·p₃ -/
theorem newton_id_2_5 (x y : R) :
    x ^ 5 + y ^ 5 =
    (x + y) * (x ^ 4 + y ^ 4) - (x * y) * (x ^ 3 + y ^ 3) := by ring

/-- For 2 variables, p₆ = e₁·p₅ − e₂·p₄ -/
theorem newton_id_2_6 (x y : R) :
    x ^ 6 + y ^ 6 =
    (x + y) * (x ^ 5 + y ^ 5) - (x * y) * (x ^ 4 + y ^ 4) := by ring

end Recurrence

/-
## Connection to Vieta's Formulas

Newton's identities bridge Vieta's formulas (coefficients ↔ roots) with
power sums. Given a monic polynomial with known roots, Vieta gives the
coefficients; Newton then gives ALL power sums from those coefficients.

For the monic polynomial (x − r₁)(x − r₂)···(x − rₙ), the
coefficient of xⁿ⁻ᵏ is (−1)ᵏ eₖ(r₁,...,rₙ). Newton's identities
let us compute tr(Aᵏ) = pₖ from det(xI − A) alone.
-/
section VietaConnection

variable {R : Type*} [CommRing R] (r₁ r₂ r₃ : R)

/-- Vieta: monic quadratic from roots -/
theorem vieta_quadratic :
    ∀ x : R, (x - r₁) * (x - r₂) =
    x ^ 2 - (r₁ + r₂) * x + r₁ * r₂ := by intro x; ring

/-- Vieta: monic cubic from roots -/
theorem vieta_cubic :
    ∀ x : R, (x - r₁) * (x - r₂) * (x - r₃) =
    x ^ 3 - (r₁ + r₂ + r₃) * x ^ 2
    + (r₁*r₂ + r₁*r₃ + r₂*r₃) * x - r₁*r₂*r₃ := by intro x; ring

/-- Full pipeline: from cubic coefficients to sum of cubes.
    If x³ + ax² + bx + c has roots r₁, r₂, r₃, then:
    r₁³ + r₂³ + r₃³ = −a³ + 3ab − 3c

    (Here a = −e₁, b = e₂, c = −e₃, so p₃ = e₁³ − 3e₁e₂ + 3e₃) -/
theorem sum_cubes_from_coefficients :
    r₁ ^ 3 + r₂ ^ 3 + r₃ ^ 3 =
    (r₁ + r₂ + r₃) ^ 3 - 3 * (r₁ + r₂ + r₃) * (r₁*r₂ + r₁*r₃ + r₂*r₃)
    + 3 * (r₁ * r₂ * r₃) := by ring

/-- The famous identity: x³ + y³ + z³ − 3xyz = (x + y + z)(x² + y² + z² − xy − xz − yz).
    This factors the left side and connects to Newton's p₃ = e₁(p₂ − e₂) + 3e₃ = e₁³ − 3e₁e₂ + 3e₃. -/
theorem sum_cubes_factorization :
    r₁ ^ 3 + r₂ ^ 3 + r₃ ^ 3 - 3 * r₁ * r₂ * r₃ =
    (r₁ + r₂ + r₃) * (r₁ ^ 2 + r₂ ^ 2 + r₃ ^ 2
     - r₁ * r₂ - r₁ * r₃ - r₂ * r₃) := by ring

end VietaConnection

#check @newton_id_2_2
#check @newton_id_3_3
#check @newton_id_4_4
#check @discriminant_cubic
#check @sum_cubes_factorization

end NewtonIdentities
