/-
  Euler's Inequality R ≥ 2r from Heron's Formula

  For any nondegenerate triangle with sides a, b, c, the circumradius R
  and inradius r satisfy Euler's inequality

      R ≥ 2r,

  with equality if and only if the triangle is equilateral.

  This is a child of the Heron's formula gallery entry (oq-06). The standard
  circumradius / inradius formulas are

      R = abc / (4·Area),      r = Area / s,

  where s = (a+b+c)/2 is the semi-perimeter and Area = √(s(s-a)(s-b)(s-c)) is
  Heron's area. Euler's inequality is purely algebraic once these are plugged in:

      R ≥ 2r
    ⟺ abc / (4·Area) ≥ 2·Area / s          (Area, s > 0)
    ⟺ abc · s ≥ 8·Area²
    ⟺ abc · s ≥ 8·s·(s-a)(s-b)(s-c)        (Heron: Area² = s(s-a)(s-b)(s-c))
    ⟺ abc ≥ 8·(s-a)(s-b)(s-c).             (s > 0)

  Writing x = s-a, y = s-b, z = s-c (all positive for a nondegenerate triangle),
  we have a = y+z, b = z+x, c = x+y, and the inequality becomes the symmetric
  AM-GM consequence

      (y+z)(z+x)(x+y) ≥ 8·xyz,

  with equality iff x = y = z, i.e. a = b = c. This last inequality is the
  mathematical heart of Euler's inequality; the SOS certificate is

      (y+z)(z+x)(x+y) - 8xyz = x(y-z)² + y(z-x)² + z(x-y)²  ≥ 0.

  Axioms: 0
  Sorries: 0
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

namespace EulerInequalityHeronOQ06

open Real

-- ════════════════════════════════════════════════════════════════
-- PART I: The algebraic core — an SOS form of AM-GM
-- ════════════════════════════════════════════════════════════════

/-- The mathematical heart of Euler's inequality: for nonnegative reals,
    `(y+z)(z+x)(x+y) ≥ 8·xyz`.

    The certificate is the sum-of-squares identity
    `(y+z)(z+x)(x+y) - 8xyz = x(y-z)² + y(z-x)² + z(x-y)²`. -/
theorem prod_sum_ge_eight_mul {x y z : ℝ}
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    8 * (x * y * z) ≤ (y + z) * (z + x) * (x + y) := by
  nlinarith [mul_nonneg hx (sq_nonneg (y - z)),
             mul_nonneg hy (sq_nonneg (z - x)),
             mul_nonneg hz (sq_nonneg (x - y)),
             mul_nonneg (mul_nonneg hx hy) hz]

/-- The SOS identity made explicit (gives the equality certificate). -/
theorem prod_sum_sub_eight_mul (x y z : ℝ) :
    (y + z) * (z + x) * (x + y) - 8 * (x * y * z)
      = x * (y - z) ^ 2 + y * (z - x) ^ 2 + z * (x - y) ^ 2 := by
  ring

/-- Equality in AM-GM forces `x = y = z` when the variables are positive. -/
theorem prod_sum_eq_iff {x y z : ℝ}
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    (y + z) * (z + x) * (x + y) = 8 * (x * y * z) ↔ x = y ∧ y = z := by
  constructor
  · intro h
    -- The SOS form is zero, so each nonnegative summand vanishes.
    have hsos : x * (y - z) ^ 2 + y * (z - x) ^ 2 + z * (x - y) ^ 2 = 0 := by
      have := prod_sum_sub_eight_mul x y z
      linarith
    have t1 : 0 ≤ x * (y - z) ^ 2 := mul_nonneg hx.le (sq_nonneg _)
    have t2 : 0 ≤ y * (z - x) ^ 2 := mul_nonneg hy.le (sq_nonneg _)
    have t3 : 0 ≤ z * (x - y) ^ 2 := mul_nonneg hz.le (sq_nonneg _)
    have e3 : z * (x - y) ^ 2 = 0 := by linarith
    have e2 : y * (z - x) ^ 2 = 0 := by linarith
    have hsq_xy : (x - y) ^ 2 = 0 := by
      rcases mul_eq_zero.1 e3 with h0 | h0
      · exact absurd h0 (ne_of_gt hz)
      · exact h0
    have hsq_zx : (z - x) ^ 2 = 0 := by
      rcases mul_eq_zero.1 e2 with h0 | h0
      · exact absurd h0 (ne_of_gt hy)
      · exact h0
    have hxy0 : x - y = 0 := by
      have := sq_eq_zero_iff.mp hsq_xy; linarith
    have hzx0 : z - x = 0 := by
      have := sq_eq_zero_iff.mp hsq_zx; linarith
    exact ⟨by linarith, by linarith⟩
  · rintro ⟨hxy, hyz⟩
    subst hxy; subst hyz; ring

-- ════════════════════════════════════════════════════════════════
-- PART II: Triangle data — semi-perimeter, Heron product, area
-- ════════════════════════════════════════════════════════════════

/-- Semi-perimeter. -/
noncomputable def semiperimeter (a b c : ℝ) : ℝ := (a + b + c) / 2

/-- Heron's product `s(s-a)(s-b)(s-c)`; the squared area. -/
noncomputable def heronProduct (a b c : ℝ) : ℝ :=
  semiperimeter a b c * (semiperimeter a b c - a)
    * (semiperimeter a b c - b) * (semiperimeter a b c - c)

/-- Heron's area `√(s(s-a)(s-b)(s-c))`. -/
noncomputable def area (a b c : ℝ) : ℝ := sqrt (heronProduct a b c)

/-- Circumradius `R = abc / (4·Area)`. -/
noncomputable def circumradius (a b c : ℝ) : ℝ := a * b * c / (4 * area a b c)

/-- Inradius `r = Area / s`. -/
noncomputable def inradius (a b c : ℝ) : ℝ := area a b c / semiperimeter a b c

/-- For a nondegenerate triangle the semi-perimeter is strictly positive. -/
theorem semiperimeter_pos {a b c : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    0 < semiperimeter a b c := by
  unfold semiperimeter; linarith

theorem heronProduct_pos {a b c : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : a < b + c) (hbc : b < a + c) (hca : c < a + b) :
    0 < heronProduct a b c := by
  unfold heronProduct semiperimeter
  have hs : 0 < (a + b + c) / 2 := by linarith
  have hsa : 0 < (a + b + c) / 2 - a := by linarith
  have hsb : 0 < (a + b + c) / 2 - b := by linarith
  have hsc : 0 < (a + b + c) / 2 - c := by linarith
  positivity

theorem area_pos {a b c : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : a < b + c) (hbc : b < a + c) (hca : c < a + b) :
    0 < area a b c := by
  unfold area
  exact sqrt_pos.mpr (heronProduct_pos ha hb hc hab hbc hca)

/-- Area squared equals Heron's product (no sqrt remaining). -/
theorem area_sq {a b c : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : a < b + c) (hbc : b < a + c) (hca : c < a + b) :
    area a b c ^ 2 = heronProduct a b c := by
  unfold area
  rw [sq_sqrt (heronProduct_pos ha hb hc hab hbc hca).le]

-- ════════════════════════════════════════════════════════════════
-- PART III: The reduced side inequality `abc ≥ 8(s-a)(s-b)(s-c)`
-- ════════════════════════════════════════════════════════════════

/-- The product inequality in triangle form: `abc ≥ 8(s-a)(s-b)(s-c)`.
    Obtained from `prod_sum_ge_eight_mul` via `x = s-a`, `y = s-b`, `z = s-c`. -/
theorem sides_ge_eight_prod {a b c : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : a < b + c) (hbc : b < a + c) (hca : c < a + b) :
    8 * ((semiperimeter a b c - a) * (semiperimeter a b c - b)
        * (semiperimeter a b c - c)) ≤ a * b * c := by
  have hsa : 0 ≤ semiperimeter a b c - a := by unfold semiperimeter; linarith
  have hsb : 0 ≤ semiperimeter a b c - b := by unfold semiperimeter; linarith
  have hsc : 0 ≤ semiperimeter a b c - c := by unfold semiperimeter; linarith
  have key := prod_sum_ge_eight_mul hsa hsb hsc
  have ea : a = (semiperimeter a b c - b) + (semiperimeter a b c - c) := by
    unfold semiperimeter; ring
  have eb : b = (semiperimeter a b c - c) + (semiperimeter a b c - a) := by
    unfold semiperimeter; ring
  have ec : c = (semiperimeter a b c - a) + (semiperimeter a b c - b) := by
    unfold semiperimeter; ring
  calc 8 * ((semiperimeter a b c - a) * (semiperimeter a b c - b)
            * (semiperimeter a b c - c))
      ≤ ((semiperimeter a b c - b) + (semiperimeter a b c - c))
        * ((semiperimeter a b c - c) + (semiperimeter a b c - a))
        * ((semiperimeter a b c - a) + (semiperimeter a b c - b)) := key
    _ = a * b * c := by rw [← ea, ← eb, ← ec]

-- ════════════════════════════════════════════════════════════════
-- PART IV: Euler's inequality R ≥ 2r
-- ════════════════════════════════════════════════════════════════

/-- **Euler's inequality.** For any nondegenerate triangle, `R ≥ 2r`. -/
theorem euler_inequality {a b c : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : a < b + c) (hbc : b < a + c) (hca : c < a + b) :
    2 * inradius a b c ≤ circumradius a b c := by
  have hs : 0 < semiperimeter a b c := semiperimeter_pos ha hb hc
  have hA : 0 < area a b c := area_pos ha hb hc hab hbc hca
  have hA2 : area a b c ^ 2 = heronProduct a b c := area_sq ha hb hc hab hbc hca
  have hsides := sides_ge_eight_prod ha hb hc hab hbc hca
  -- 8·Area² ≤ abc·s
  have hkey : 8 * area a b c ^ 2 ≤ a * b * c * semiperimeter a b c := by
    rw [hA2]; unfold heronProduct
    nlinarith [mul_le_mul_of_nonneg_left hsides hs.le]
  -- Clear denominators in R ≥ 2r.
  unfold inradius circumradius
  rw [← mul_div_assoc, div_le_div_iff₀ hs (mul_pos (by norm_num) hA)]
  nlinarith [hkey]

/-- **Equality case.** `R = 2r` holds iff the triangle is equilateral. -/
theorem euler_equality_iff {a b c : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : a < b + c) (hbc : b < a + c) (hca : c < a + b) :
    2 * inradius a b c = circumradius a b c ↔ a = b ∧ b = c := by
  have hs : 0 < semiperimeter a b c := semiperimeter_pos ha hb hc
  have hA : 0 < area a b c := area_pos ha hb hc hab hbc hca
  have hA2 : area a b c ^ 2 = heronProduct a b c := area_sq ha hb hc hab hbc hca
  -- `R = 2r` ⟺ `abc·s = 8·Area²`.
  have requiv : 2 * inradius a b c = circumradius a b c
      ↔ a * b * c * semiperimeter a b c = 8 * area a b c ^ 2 := by
    unfold circumradius inradius
    rw [← mul_div_assoc,
        div_eq_div_iff hs.ne' (mul_pos (by norm_num) hA).ne']
    constructor
    · intro h; linear_combination -h
    · intro h; linear_combination -h
  rw [requiv, hA2]
  unfold heronProduct
  set s := semiperimeter a b c with hsdef
  have hsa : 0 < s - a := by rw [hsdef]; unfold semiperimeter; linarith
  have hsb : 0 < s - b := by rw [hsdef]; unfold semiperimeter; linarith
  have hsc : 0 < s - c := by rw [hsdef]; unfold semiperimeter; linarith
  have ea : a = (s - b) + (s - c) := by rw [hsdef]; unfold semiperimeter; ring
  have eb : b = (s - c) + (s - a) := by rw [hsdef]; unfold semiperimeter; ring
  have ec : c = (s - a) + (s - b) := by rw [hsdef]; unfold semiperimeter; ring
  rw [show a * b * c * s = s * (a * b * c) by ring,
      show (8 : ℝ) * (s * (s - a) * (s - b) * (s - c))
        = s * (8 * ((s - a) * (s - b) * (s - c))) by ring]
  constructor
  · intro h
    have hcancel : a * b * c = 8 * ((s - a) * (s - b) * (s - c)) :=
      mul_left_cancel₀ hs.ne' h
    have hform : ((s - b) + (s - c)) * ((s - c) + (s - a)) * ((s - a) + (s - b))
                  = 8 * ((s - a) * (s - b) * (s - c)) := by
      rw [← ea, ← eb, ← ec]; exact hcancel
    obtain ⟨h1, h2⟩ := (prod_sum_eq_iff hsa hsb hsc).1 hform
    exact ⟨by linarith, by linarith⟩
  · rintro ⟨hab', hbc'⟩
    have hform : ((s - b) + (s - c)) * ((s - c) + (s - a)) * ((s - a) + (s - b))
                  = 8 * ((s - a) * (s - b) * (s - c)) :=
      (prod_sum_eq_iff hsa hsb hsc).2 ⟨by linarith, by linarith⟩
    rw [← ea, ← eb, ← ec] at hform
    rw [hform]

end EulerInequalityHeronOQ06
