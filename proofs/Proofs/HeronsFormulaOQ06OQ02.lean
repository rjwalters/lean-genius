/-
  Gerretsen's Inequality  s² ≤ 4R² + 4Rr + 3r²

  For any nondegenerate triangle with sides a, b, c, semi-perimeter
  s = (a+b+c)/2, circumradius R and inradius r, Gerretsen's inequality states

      s² ≤ 4R² + 4Rr + 3r².

  This is a child of `herons-formula-oq-06` (Euler's triangle bound).  It uses
  the *same* Ravi-substitution sum-of-squares engine that powers the parent's
  Euler inequality `R ≥ 2r`: write x = s-a, y = s-b, z = s-c (all positive for a
  nondegenerate triangle).  Then a = y+z, b = z+x, c = x+y, the area satisfies
  Area² = s·xyz, and

      R = abc/(4·Area),   r = Area/s.

  Substituting and clearing denominators (only the *square* Area² = s·xyz ever
  appears, because the cross term 4Rr = abc/s is already area-free) reduces the
  whole inequality to the area-free polynomial statement

      4·(x+y+z)³·xyz ≤ ((x+y)(y+z)(z+x))² + 4xyz·(x+y)(y+z)(z+x) + 12(xyz)² ,

  i.e. `0 ≤ gerretsenPoly x y z`.  Concretely, the difference of the two sides
  of Gerretsen's inequality is exactly `gerretsenPoly (s-a) (s-b) (s-c)/(4·Area²)`.

  The algebraic heart `gerretsenPoly x y z ≥ 0` has the certificate

      E = x⁴(y-z)² + y⁴(z-x)² + z⁴(x-y)²
            + 2·[ x²(y-z)²(xy+xz-yz) + y²z²(x-y)(x-z) ].

  The bracket is a Schur-type term (it is *negative* for some signed inputs, so
  positivity of x, y, z is essential); it is settled by a WLOG ordering, under
  which `xy+xz-yz = y² + (x-y)(y+z) ≥ 0` and `(x-y)(x-z) ≥ 0`.

  Tight (equality) at x = y = z, i.e. the equilateral triangle, matching the
  classical sharpness of Gerretsen's inequality.

  Builds on the verified parent `Proofs.HeronsFormulaOQ06`
  (`EulerInequalityHeronOQ06`), reusing its triangle data
  (`semiperimeter`, `area`, `circumradius`, `inradius`, `area_sq`, …).

  Axioms: 0
  Sorries: 0
-/
import Proofs.HeronsFormulaOQ06
import Mathlib.Tactic

namespace GerretsenHeronOQ06OQ02

open Real EulerInequalityHeronOQ06

-- ════════════════════════════════════════════════════════════════
-- PART I: The algebraic core — `gerretsenPoly x y z ≥ 0`
-- ════════════════════════════════════════════════════════════════

/-- The area-free polynomial whose nonnegativity *is* Gerretsen's inequality.
    With `x = s-a, y = s-b, z = s-c`, Gerretsen's `4R²+4Rr+3r² - s²` equals
    `gerretsenPoly x y z / (4·Area²)`. -/
noncomputable def gerretsenPoly (x y z : ℝ) : ℝ :=
  ((x + y) * (y + z) * (z + x)) ^ 2
    + 4 * (x * y * z) * ((x + y) * (y + z) * (z + x))
    + 12 * (x * y * z) ^ 2
    - 4 * (x + y + z) ^ 3 * (x * y * z)

/-- The core inequality under a fixed ordering `z ≤ y ≤ x`.  The certificate is
    `gerretsenPoly = Σ x⁴(y-z)² + 2x²(y-z)²(xy+xz-yz) + 2y²z²(x-y)(x-z)`, and the
    ordering makes every summand manifestly nonnegative (in particular
    `xy+xz-yz = y² + (x-y)(y+z) ≥ 0`). -/
theorem gerretsen_core_ordered {x y z : ℝ}
    (hz : 0 ≤ z) (hzy : z ≤ y) (hyx : y ≤ x) :
    0 ≤ ((x + y) * (y + z) * (z + x)) ^ 2
        + 4 * (x * y * z) * ((x + y) * (y + z) * (z + x))
        + 12 * (x * y * z) ^ 2
        - 4 * (x + y + z) ^ 3 * (x * y * z) := by
  have hy : 0 ≤ y := le_trans hz hzy
  have hx : 0 ≤ x := le_trans hy hyx
  -- `xy + xz - yz = y² + (x-y)(y+z) ≥ 0`.
  have hABC : 0 ≤ x * y + x * z - y * z := by
    nlinarith [mul_nonneg (sub_nonneg.2 hyx) (show (0:ℝ) ≤ y + z by linarith),
               sq_nonneg y]
  nlinarith [mul_nonneg (show (0:ℝ) ≤ x ^ 4 by positivity) (sq_nonneg (y - z)),
             mul_nonneg (show (0:ℝ) ≤ y ^ 4 by positivity) (sq_nonneg (z - x)),
             mul_nonneg (show (0:ℝ) ≤ z ^ 4 by positivity) (sq_nonneg (x - y)),
             mul_nonneg (mul_nonneg (sq_nonneg x) (sq_nonneg (y - z))) hABC,
             mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg y) (sq_nonneg z))
                          (sub_nonneg.2 hyx)) (sub_nonneg.2 (le_trans hzy hyx))]

/-- **Algebraic core of Gerretsen's inequality.** For all nonnegative reals,
    `0 ≤ gerretsenPoly x y z`.  Reduces to the ordered case by the symmetry of
    `gerretsenPoly`. -/
theorem gerretsen_core {x y z : ℝ}
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    0 ≤ gerretsenPoly x y z := by
  unfold gerretsenPoly
  obtain hxy | hyx := le_total x y
  · obtain hyz | hzy := le_total y z
    · -- x ≤ y ≤ z
      nlinarith [gerretsen_core_ordered hx hxy hyz]
    · obtain hxz | hzx := le_total x z
      · -- x ≤ z ≤ y
        nlinarith [gerretsen_core_ordered hx hxz hzy]
      · -- z ≤ x ≤ y
        nlinarith [gerretsen_core_ordered hz hzx hxy]
  · obtain hyz | hzy := le_total y z
    · obtain hxz | hzx := le_total x z
      · -- y ≤ x ≤ z
        nlinarith [gerretsen_core_ordered hy hyx hxz]
      · -- y ≤ z ≤ x
        nlinarith [gerretsen_core_ordered hy hyz hzx]
    · -- z ≤ y ≤ x
      nlinarith [gerretsen_core_ordered hz hzy hyx]

-- ════════════════════════════════════════════════════════════════
-- PART II: Area-free rewrites of `R²`, `R·r`, `r²`
-- ════════════════════════════════════════════════════════════════

/-- `R² = (abc)² / (16·Area²)`, with `Area² = heronProduct`. -/
theorem circumradius_sq {a b c : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : a < b + c) (hbc : b < a + c) (hca : c < a + b) :
    circumradius a b c ^ 2 = (a * b * c) ^ 2 / (16 * heronProduct a b c) := by
  have hA2 : area a b c ^ 2 = heronProduct a b c := area_sq ha hb hc hab hbc hca
  unfold circumradius
  rw [div_pow, show (4 * area a b c) ^ 2 = 16 * area a b c ^ 2 by ring, hA2]

/-- `r² = Area² / s² = heronProduct / s²`. -/
theorem inradius_sq {a b c : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : a < b + c) (hbc : b < a + c) (hca : c < a + b) :
    inradius a b c ^ 2 = heronProduct a b c / semiperimeter a b c ^ 2 := by
  have hA2 : area a b c ^ 2 = heronProduct a b c := area_sq ha hb hc hab hbc hca
  unfold inradius
  rw [div_pow, hA2]

/-- The cross term is area-free: `R·r = abc / (4s)`. -/
theorem circumradius_mul_inradius {a b c : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : a < b + c) (hbc : b < a + c) (hca : c < a + b) :
    circumradius a b c * inradius a b c = a * b * c / (4 * semiperimeter a b c) := by
  have hs : 0 < semiperimeter a b c := semiperimeter_pos ha hb hc
  have hA : 0 < area a b c := area_pos ha hb hc hab hbc hca
  unfold circumradius inradius
  field_simp

-- ════════════════════════════════════════════════════════════════
-- PART III: Gerretsen's inequality
-- ════════════════════════════════════════════════════════════════

/-- **Gerretsen's inequality.** For any nondegenerate triangle,
    `s² ≤ 4R² + 4Rr + 3r²`. -/
theorem gerretsen {a b c : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : a < b + c) (hbc : b < a + c) (hca : c < a + b) :
    semiperimeter a b c ^ 2 ≤
      4 * circumradius a b c ^ 2
        + 4 * (circumradius a b c * inradius a b c)
        + 3 * inradius a b c ^ 2 := by
  have hs : 0 < semiperimeter a b c := semiperimeter_pos ha hb hc
  have hH : 0 < heronProduct a b c := heronProduct_pos ha hb hc hab hbc hca
  have hsa : 0 ≤ semiperimeter a b c - a := by unfold semiperimeter; linarith
  have hsb : 0 ≤ semiperimeter a b c - b := by unfold semiperimeter; linarith
  have hsc : 0 ≤ semiperimeter a b c - c := by unfold semiperimeter; linarith
  -- The difference of the two sides is `gerretsenPoly (s-a) (s-b) (s-c) / (4·Area²)`.
  have hge : 0 ≤ gerretsenPoly (semiperimeter a b c - a) (semiperimeter a b c - b)
      (semiperimeter a b c - c) / (4 * heronProduct a b c) :=
    div_nonneg (gerretsen_core hsa hsb hsc) (by linarith)
  have hEq :
      4 * circumradius a b c ^ 2
        + 4 * (circumradius a b c * inradius a b c)
        + 3 * inradius a b c ^ 2
        - semiperimeter a b c ^ 2
      = gerretsenPoly (semiperimeter a b c - a) (semiperimeter a b c - b)
          (semiperimeter a b c - c) / (4 * heronProduct a b c) := by
    rw [circumradius_sq ha hb hc hab hbc hca,
        circumradius_mul_inradius ha hb hc hab hbc hca,
        inradius_sq ha hb hc hab hbc hca]
    rw [gerretsenPoly]
    field_simp
    unfold heronProduct semiperimeter
    ring
  linarith [hEq, hge]

end GerretsenHeronOQ06OQ02
