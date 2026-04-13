/-
  Isoperimetric Inequality for Triangles

  Among all triangles with a fixed perimeter, the equilateral triangle
  maximizes the area.

  Equivalently, for a triangle with sides a, b, c and semi-perimeter
  s = (a+b+c)/2:

    Area² ≤ s⁴/27

  with equality if and only if a = b = c (equilateral triangle).

  Proof approach:
  - Set x = s-a, y = s-b, z = s-c; note x + y + z = s.
  - Heron's formula: Area² = s·x·y·z
  - By 3-variable AM-GM: xyz ≤ ((x+y+z)/3)³ = (s/3)³
  - So Area² ≤ s·(s/3)³ = s⁴/27
  - Equality iff x = y = z iff a = b = c (equilateral)

  The AM-GM key identity:
    (x+y+z)³ - 27xyz
    = (x+y+z)(x²+y²+z²-xy-yz-xz) + 3(x(y-z)² + y(x-z)² + z(x-y)²)
  Both summands are ≥ 0 for x, y, z ≥ 0.

  Axioms: 0
  Sorries: 0
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

namespace IsoperimetricTriangle

open Real

-- ════════════════════════════════════════════════════════════════
-- PART I: Definitions
-- ════════════════════════════════════════════════════════════════

/-- Heron's product s(s-a)(s-b)(s-c) where s = (a+b+c)/2.
    The area of a triangle with sides a, b, c is √(heron_product a b c). -/
noncomputable def heron_product (a b c : ℝ) : ℝ :=
  let s := (a + b + c) / 2
  s * (s - a) * (s - b) * (s - c)

/-- Heron product non-negativity for valid triangles. -/
theorem heron_product_nonneg {a b c : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : a < b + c) (hbc : b < a + c) (hca : c < a + b) :
    0 ≤ heron_product a b c := by
  unfold heron_product
  have hs : 0 < (a + b + c) / 2 := by linarith
  have hsa : 0 < (a + b + c) / 2 - a := by linarith
  have hsb : 0 < (a + b + c) / 2 - b := by linarith
  have hsc : 0 < (a + b + c) / 2 - c := by linarith
  apply mul_nonneg
  apply mul_nonneg
  apply mul_nonneg
  all_goals linarith

/-- Classical Heron area formula: Area = √(s(s-a)(s-b)(s-c)) -/
noncomputable def triangle_area (a b c : ℝ) : ℝ :=
  sqrt (heron_product a b c)

-- ════════════════════════════════════════════════════════════════
-- PART II: Three-Variable AM-GM
-- ════════════════════════════════════════════════════════════════

/-!
### AM-GM for Three Non-negative Reals

The key inequality: xyz ≤ ((x+y+z)/3)³ for x, y, z ≥ 0.

Proof via the algebraic identity:
  (x+y+z)³ - 27xyz
  = (x+y+z)(x²+y²+z²-xy-yz-xz) + 3·[x(y-z)² + y(x-z)² + z(x-y)²]

Both summands are non-negative:
- x+y+z ≥ 0 and x²+y²+z²-xy-yz-xz = ½[(x-y)²+(y-z)²+(x-z)²] ≥ 0
- Each term x(y-z)² ≥ 0 since x ≥ 0 and squares are non-negative
-/

/-- **Key algebraic identity** for the AM-GM proof.
    The gap (x+y+z)³ - 27xyz decomposes into two non-negative parts. -/
private lemma amgm_three_identity (x y z : ℝ) :
    (x + y + z) ^ 3 - 27 * (x * y * z) =
    (x + y + z) * (x ^ 2 + y ^ 2 + z ^ 2 - x * y - y * z - x * z) +
    3 * (x * (y - z) ^ 2 + y * (x - z) ^ 2 + z * (x - y) ^ 2) := by ring

/-- **Three-variable AM-GM inequality**: xyz ≤ ((x+y+z)/3)³ for non-negative reals.

    This is the classical arithmetic-geometric mean inequality for three variables:
    the geometric mean is bounded above by the arithmetic mean. -/
theorem amgm_three_nonneg {x y z : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    x * y * z ≤ ((x + y + z) / 3) ^ 3 := by
  -- Show 0 ≤ (x+y+z)^3 - 27xyz using the algebraic decomposition
  have hgap : 0 ≤ (x + y + z) ^ 3 - 27 * (x * y * z) := by
    rw [amgm_three_identity]
    apply add_nonneg
    · apply mul_nonneg
      · linarith
      · nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (x - z)]
    · have h1 : 0 ≤ x * (y - z) ^ 2 := mul_nonneg hx (sq_nonneg _)
      have h2 : 0 ≤ y * (x - z) ^ 2 := mul_nonneg hy (sq_nonneg _)
      have h3 : 0 ≤ z * (x - y) ^ 2 := mul_nonneg hz (sq_nonneg _)
      linarith
  -- Conclude xyz ≤ ((x+y+z)/3)^3
  nlinarith [show ((x + y + z) / 3) ^ 3 = (x + y + z) ^ 3 / 27 from by ring]

/-- **Equality in AM-GM**: xyz = ((x+y+z)/3)³ iff x = y = z, for positive reals. -/
theorem amgm_three_eq_iff {x y z : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    x * y * z = ((x + y + z) / 3) ^ 3 ↔ x = y ∧ y = z := by
  constructor
  · intro heq
    -- From equality, the gap is 0
    have hgap_zero : (x + y + z) * (x ^ 2 + y ^ 2 + z ^ 2 - x * y - y * z - x * z) +
                3 * (x * (y - z) ^ 2 + y * (x - z) ^ 2 + z * (x - y) ^ 2) = 0 := by
      have hconv : ((x + y + z) / 3) ^ 3 = (x + y + z) ^ 3 / 27 := by ring
      nlinarith [amgm_three_identity x y z]
    -- Each term in the sum is ≥ 0
    have h1 : 0 ≤ x * (y - z) ^ 2 := mul_nonneg hx.le (sq_nonneg _)
    have h2 : 0 ≤ y * (x - z) ^ 2 := mul_nonneg hy.le (sq_nonneg _)
    have h3 : 0 ≤ z * (x - y) ^ 2 := mul_nonneg hz.le (sq_nonneg _)
    have hq1 : 0 ≤ (x + y + z) * (x ^ 2 + y ^ 2 + z ^ 2 - x * y - y * z - x * z) := by
      apply mul_nonneg
      · linarith
      · nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (x - z)]
    -- So each part must be 0
    have hpart2 : x * (y - z) ^ 2 + y * (x - z) ^ 2 + z * (x - y) ^ 2 = 0 := by
      nlinarith
    -- From x*(y-z)² = 0 and x > 0: y = z
    have hyz_term : x * (y - z) ^ 2 = 0 := by nlinarith
    have hxy_term : z * (x - y) ^ 2 = 0 := by nlinarith
    have hyz : y = z := by
      rcases mul_eq_zero.mp hyz_term with h | h
      · linarith
      · have := sq_eq_zero_iff.mp h; linarith
    have hxy : x = y := by
      rcases mul_eq_zero.mp hxy_term with h | h
      · linarith
      · have := sq_eq_zero_iff.mp h; linarith
    exact ⟨hxy, hyz⟩
  · intro ⟨hxy, hyz⟩
    subst hxy; subst hyz
    ring

-- ════════════════════════════════════════════════════════════════
-- PART III: Main Isoperimetric Inequality
-- ════════════════════════════════════════════════════════════════

/-!
### Isoperimetric Inequality for Triangles

For a triangle with sides a, b, c, the equilateral triangle with the
same perimeter has maximum area.

Algebraically: heron_product a b c ≤ heron_product t t t
where t = (a+b+c)/3 (equilateral side length with same perimeter).

Since heron_product t t t = s⁴/27 (where s = (a+b+c)/2), this gives
the quantitative bound.
-/

/-- The Heron product of an equilateral triangle with side t. -/
theorem heron_product_equilateral (t : ℝ) :
    heron_product t t t = (3 * t / 2) ^ 4 / 27 := by
  unfold heron_product; ring

/-- **Main theorem**: The Heron product is bounded above by the equilateral case.

    For any triangle with sides a, b, c and semi-perimeter s = (a+b+c)/2,
      heron_product a b c ≤ s⁴/27
    with equality iff a = b = c. -/
theorem heron_product_le_equilateral {a b c : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : a < b + c) (hbc : b < a + c) (hca : c < a + b) :
    heron_product a b c ≤ heron_product ((a + b + c) / 3) ((a + b + c) / 3) ((a + b + c) / 3) := by
  -- Set s = (a+b+c)/2, and x = s-a, y = s-b, z = s-c
  set s := (a + b + c) / 2 with hs_def
  set x := s - a with hx_def
  set y := s - b with hy_def
  set z := s - c with hz_def
  have hx : 0 < x := by rw [hx_def, hs_def]; linarith
  have hy : 0 < y := by rw [hy_def, hs_def]; linarith
  have hz : 0 < z := by rw [hz_def, hs_def]; linarith
  have hxyz_sum : x + y + z = s := by rw [hx_def, hy_def, hz_def]; ring
  have hs_pos : 0 < s := by rw [hs_def]; linarith
  -- Heron product = s * x * y * z
  have hprod_expand : heron_product a b c = s * (x * y * z) := by
    unfold heron_product; rw [hx_def, hy_def, hz_def]; ring
  -- Equilateral case: heron_product t t t = s⁴/27 where t = (a+b+c)/3
  have hequil : heron_product ((a + b + c) / 3) ((a + b + c) / 3) ((a + b + c) / 3) =
    s ^ 4 / 27 := by
    unfold heron_product; rw [hs_def]; ring
  rw [hprod_expand, hequil]
  -- By AM-GM: xyz ≤ ((x+y+z)/3)³ = (s/3)³
  have hamgm : x * y * z ≤ ((x + y + z) / 3) ^ 3 :=
    amgm_three_nonneg hx.le hy.le hz.le
  rw [hxyz_sum] at hamgm
  -- s * xyz ≤ s * (s/3)³ = s⁴/27
  have hs47 : s * (s / 3) ^ 3 = s ^ 4 / 27 := by ring
  linarith [mul_le_mul_of_nonneg_left hamgm hs_pos.le, hs47]

/-- **Equality characterization**: The maximum is achieved iff the triangle is equilateral. -/
theorem heron_product_eq_equilateral_iff {a b c : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : a < b + c) (hbc : b < a + c) (hca : c < a + b) :
    heron_product a b c = heron_product ((a + b + c) / 3) ((a + b + c) / 3) ((a + b + c) / 3) ↔
    a = b ∧ b = c := by
  set s := (a + b + c) / 2 with hs_def
  set x := s - a with hx_def
  set y := s - b with hy_def
  set z := s - c with hz_def
  have hx : 0 < x := by rw [hx_def, hs_def]; linarith
  have hy : 0 < y := by rw [hy_def, hs_def]; linarith
  have hz : 0 < z := by rw [hz_def, hs_def]; linarith
  have hxyz_sum : x + y + z = s := by rw [hx_def, hy_def, hz_def]; ring
  have hs_pos : 0 < s := by rw [hs_def]; linarith
  have hprod_expand : heron_product a b c = s * (x * y * z) := by
    unfold heron_product; rw [hx_def, hy_def, hz_def]; ring
  have hequil : heron_product ((a + b + c) / 3) ((a + b + c) / 3) ((a + b + c) / 3) =
    s ^ 4 / 27 := by
    unfold heron_product; rw [hs_def]; ring
  rw [hprod_expand, hequil]
  constructor
  · intro heq
    -- s * xyz = s⁴/27 → xyz = (s/3)³
    have hxyz_eq : x * y * z = (s / 3) ^ 3 := by
      have h47 : s ^ 4 / 27 = s * (s / 3) ^ 3 := by ring
      have := mul_left_cancel₀ hs_pos.ne' (by linarith [h47] : s * (x * y * z) = s * (s / 3) ^ 3)
      exact this
    rw [← hxyz_sum] at hxyz_eq
    obtain ⟨hxy, hyz⟩ := (amgm_three_eq_iff hx hy hz).mp hxyz_eq
    constructor
    · -- x = y means s - a = s - b means a = b
      have hxa : x = s - a := hx_def
      have hyb : y = s - b := hy_def
      linarith [hxa ▸ hyb ▸ hxy]
    · have hyb : y = s - b := hy_def
      have hzc : z = s - c := hz_def
      linarith [hyb ▸ hzc ▸ hyz]
  · intro ⟨hab_eq, hbc_eq⟩
    subst hab_eq; subst hbc_eq
    -- Now a = b = c, so x = y = z = s/3
    have hxy : x = y := by rw [hx_def, hy_def]
    have hyz : y = z := by rw [hy_def, hz_def]
    have hxyz_eq : x * y * z = ((x + y + z) / 3) ^ 3 :=
      (amgm_three_eq_iff hx hy hz).mpr ⟨hxy, hyz⟩
    rw [hxyz_sum] at hxyz_eq
    calc s * (x * y * z) = s * (s / 3) ^ 3 := by rw [hxyz_eq]
      _ = s ^ 4 / 27 := by ring

-- ════════════════════════════════════════════════════════════════
-- PART IV: Quantitative Bounds
-- ════════════════════════════════════════════════════════════════

/-!
### Quantitative Area Bounds

The isoperimetric inequality has the quantitative form:

  Area² = heron_product ≤ s⁴/27

where s = (a+b+c)/2 is the semi-perimeter.

Equivalently: Area ≤ s² / √27 = s² / (3√3).
-/

/-- The Heron product is bounded by s⁴/27. -/
theorem heron_product_le_s4_27 {a b c : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : a < b + c) (hbc : b < a + c) (hca : c < a + b) :
    heron_product a b c ≤ ((a + b + c) / 2) ^ 4 / 27 := by
  have h := heron_product_le_equilateral ha hb hc hab hbc hca
  have : heron_product ((a + b + c) / 3) ((a + b + c) / 3) ((a + b + c) / 3) =
    ((a + b + c) / 2) ^ 4 / 27 := by
    unfold heron_product; ring
  linarith

/-- **Triangle area bound**: Area² ≤ s⁴/27, equivalently Area ≤ s²/√27. -/
theorem triangle_area_sq_le {a b c : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : a < b + c) (hbc : b < a + c) (hca : c < a + b) :
    (triangle_area a b c) ^ 2 ≤ ((a + b + c) / 2) ^ 4 / 27 := by
  unfold triangle_area
  rw [sq_sqrt (heron_product_nonneg ha hb hc hab hbc hca)]
  exact heron_product_le_s4_27 ha hb hc hab hbc hca

/-- **Isoperimetric ratio**: heron_product ≤ P⁴/432 where P is the perimeter. -/
theorem isoperimetric_ratio {a b c : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : a < b + c) (hbc : b < a + c) (hca : c < a + b) :
    heron_product a b c ≤ (a + b + c) ^ 4 / 432 := by
  have h := heron_product_le_s4_27 ha hb hc hab hbc hca
  linarith [show ((a + b + c) / 2) ^ 4 / 27 = (a + b + c) ^ 4 / 432 from by ring]

-- ════════════════════════════════════════════════════════════════
-- PART V: Worked Examples
-- ════════════════════════════════════════════════════════════════

/-!
### Verification for Specific Triangles
-/

/-- Explicit value: heron_product 3 4 5 = 36 (area = 6) -/
theorem heron_product_345 : heron_product 3 4 5 = 36 := by
  unfold heron_product; norm_num

/-- Bound for 3-4-5 right triangle: heron_product ≤ s⁴/27 = 1296/27 = 48 -/
theorem heron_product_345_bound :
    heron_product 3 4 5 ≤ ((3 + 4 + (5 : ℝ)) / 2) ^ 4 / 27 := by
  rw [heron_product_345]; norm_num

/-- For equilateral triangle with side 2: heron_product = 3, area = √3 -/
theorem heron_product_equilateral_2 : heron_product 2 2 2 = 3 := by
  unfold heron_product; norm_num

/-- Area of equilateral triangle with side 2 equals √3. Bound is equality. -/
theorem equilateral_area_2 :
    triangle_area 2 2 2 = sqrt 3 := by
  unfold triangle_area
  rw [heron_product_equilateral_2]

/-- Equilateral bound is tight for side 2:
    heron_product 2 2 2 = (6/2)⁴/27 = 81/27 = 3 ✓ -/
theorem equilateral_bound_equality :
    heron_product 2 2 2 = ((2 + 2 + (2 : ℝ)) / 2) ^ 4 / 27 := by
  rw [heron_product_equilateral_2]; norm_num

-- ════════════════════════════════════════════════════════════════
-- PART VI: Connection to Wiedijk #57
-- ════════════════════════════════════════════════════════════════

/-!
### Connection to Heron's Formula (Wiedijk #57)

The isoperimetric inequality for triangles is a direct application of
Heron's formula combined with the three-variable AM-GM inequality.

Heron's formula (Wiedijk #57, formalized in HeronsFormula.lean) gives:
  Area = √(s(s-a)(s-b)(s-c))

Setting x = s-a, y = s-b, z = s-c with x+y+z = s, the AM-GM inequality
xyz ≤ (s/3)³ gives:
  Area² = s·xyz ≤ s·(s/3)³ = s⁴/27

This is the cleanest proof of the triangle isoperimetric inequality.

The complementary result for quadrilaterals (square maximizes area for
fixed perimeter among cyclic quadrilaterals) is proved via 4-variable AM-GM
in HeronsFormulaOQ01.lean (Brahmagupta's formula).
-/

-- Export main results for cross-referencing
#check @amgm_three_nonneg               -- xyz ≤ ((x+y+z)/3)³ for x,y,z ≥ 0
#check @amgm_three_eq_iff               -- equality iff x = y = z (for positive reals)
#check @heron_product_le_equilateral    -- main isoperimetric inequality
#check @heron_product_eq_equilateral_iff  -- equality iff equilateral
#check @heron_product_le_s4_27          -- quantitative bound: hp ≤ s⁴/27
#check @isoperimetric_ratio             -- hp ≤ P⁴/432

end IsoperimetricTriangle
