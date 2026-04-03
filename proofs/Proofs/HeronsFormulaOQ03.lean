/-
  Kahan's Numerically Stable Heron's Formula

  William Kahan (1986) demonstrated that the classical Heron formula
      Area = √(s(s-a)(s-b)(s-c))
  can suffer catastrophic cancellation in floating-point arithmetic when
  the triangle is nearly degenerate (very flat, with one side nearly equal
  to the sum of the other two).

  Kahan's stable formula rearranges the computation: for sides a ≥ b ≥ c ≥ 0,
  compute
      T = (a + (b + c)) · (c - (a - b)) · (c + (a - b)) · (a + (b - c))
      Area = (1/4) · √T

  In exact arithmetic, T = 16 · s(s-a)(s-b)(s-c) (algebraic identity proved
  below). The numerical advantage of Kahan's grouping is that each factor
  in T involves only additions of quantities with the same sign or small
  subtractions, avoiding the precision loss that occurs when computing
  (s - a) directly for flat triangles where a ≈ b + c.

  Key results:
  1. Kahan product definition and equivalence with Heron product (ring identity)
  2. Symmetric expansion: T = (a+b+c)(b+c-a)(a+c-b)(a+b-c)
  3. Non-negativity from triangle inequality (no ordering needed)
  4. Equivalence of Kahan area with classical triangle area
  5. Stability structure: ordering a ≥ b ≥ c makes each factor individually
     well-conditioned
  6. Worked examples: 3-4-5 and 5-12-13 right triangles

  Axioms: 0
  Sorries: 0

  Reference: Kahan, W. (1986). "Miscalculated Areas". Personal communication,
  widely cited in numerical analysis textbooks.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

namespace KahanHeron

open Real

-- ════════════════════════════════════════════════════════════════
-- PART I: Definitions
-- ════════════════════════════════════════════════════════════════

/-- Heron's product: s(s-a)(s-b)(s-c) where s = (a+b+c)/2.
    The classical formula gives Area = √(heron_product a b c). -/
noncomputable def heron_product (a b c : ℝ) : ℝ :=
  let s := (a + b + c) / 2
  s * (s - a) * (s - b) * (s - c)

/-- **Kahan's expression**: (a+(b+c)) · (c-(a-b)) · (c+(a-b)) · (a+(b-c))
    This equals 16 · heron_product a b c for any reals.

    The specific grouping of additions and subtractions is chosen for
    floating-point stability: each factor avoids computing the difference
    of nearly-equal large numbers directly. -/
noncomputable def kahan_product (a b c : ℝ) : ℝ :=
  (a + (b + c)) * (c - (a - b)) * (c + (a - b)) * (a + (b - c))

/-- **Kahan's numerically stable area formula**: Area = (1/4) · √(kahan_product)
    Equivalent to Heron's formula in exact arithmetic. -/
noncomputable def kahan_area (a b c : ℝ) : ℝ :=
  sqrt (kahan_product a b c) / 4

/-- Classical Heron area formula: Area = √(s(s-a)(s-b)(s-c)) -/
noncomputable def triangle_area (a b c : ℝ) : ℝ :=
  sqrt (heron_product a b c)

-- ════════════════════════════════════════════════════════════════
-- PART II: Algebraic Equivalence
-- ════════════════════════════════════════════════════════════════

/-- **Core Identity**: The Kahan product equals 16 times the Heron product.
    This algebraic identity, proved by ring arithmetic, is the mathematical
    foundation of Kahan's algorithm: the two formulas are exactly equivalent
    in exact arithmetic. -/
theorem kahan_eq_sixteen_heron (a b c : ℝ) :
    kahan_product a b c = 16 * heron_product a b c := by
  unfold kahan_product heron_product
  ring

/-- **Symmetric Expansion**: The Kahan product equals the fully symmetric expression
    (a+b+c)(b+c-a)(a+c-b)(a+b-c).
    This makes the symmetry under permutation of sides manifest. -/
theorem kahan_product_expand (a b c : ℝ) :
    kahan_product a b c = (a + b + c) * (b + c - a) * (a + c - b) * (a + b - c) := by
  unfold kahan_product; ring

/-- **Symmetry under permutation**: The Kahan product is symmetric in a, b, c.
    Area does not depend on which side we call a, b, or c. -/
theorem kahan_product_symm_ab (a b c : ℝ) :
    kahan_product a b c = kahan_product b a c := by
  simp only [kahan_product_expand]; ring

theorem kahan_product_symm_bc (a b c : ℝ) :
    kahan_product a b c = kahan_product a c b := by
  simp only [kahan_product_expand]; ring

theorem kahan_product_cyclic (a b c : ℝ) :
    kahan_product a b c = kahan_product b c a := by
  simp only [kahan_product_expand]; ring

-- ════════════════════════════════════════════════════════════════
-- PART III: Non-negativity from Triangle Inequality
-- ════════════════════════════════════════════════════════════════

/-- **Non-negativity**: The Kahan product is non-negative whenever the three
    sides satisfy the (strict) triangle inequality.
    No ordering assumption on sides is required.

    Each factor in the symmetric expansion is non-negative:
    - (a+b+c) > 0: positive sides
    - (b+c-a) ≥ 0: triangle inequality a < b+c
    - (a+c-b) ≥ 0: triangle inequality b < a+c
    - (a+b-c) ≥ 0: triangle inequality c < a+b -/
theorem kahan_product_nonneg {a b c : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : a < b + c) (hbc : b < a + c) (hca : c < a + b) :
    0 ≤ kahan_product a b c := by
  rw [kahan_product_expand]
  apply mul_nonneg
  apply mul_nonneg
  apply mul_nonneg
  · linarith
  · linarith
  · linarith
  · linarith

/-- **Heron product non-negativity**: The Heron product is non-negative for valid
    triangles, as a corollary of the Kahan non-negativity result. -/
theorem heron_product_nonneg {a b c : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : a < b + c) (hbc : b < a + c) (hca : c < a + b) :
    0 ≤ heron_product a b c := by
  have h := kahan_product_nonneg ha hb hc hab hbc hca
  rw [kahan_eq_sixteen_heron] at h
  linarith

-- ════════════════════════════════════════════════════════════════
-- PART IV: Equivalence of Area Formulas
-- ════════════════════════════════════════════════════════════════

/-- **Helper**: √(16 · x) = 4 · √x for x ≥ 0. -/
private lemma sqrt_sixteen_mul {x : ℝ} (hx : 0 ≤ x) : sqrt (16 * x) = 4 * sqrt x := by
  have h16 : sqrt 16 = 4 := by
    rw [show (16 : ℝ) = 4 ^ 2 from by norm_num]
    exact sqrt_sq (by norm_num : (0 : ℝ) ≤ 4)
  rw [sqrt_mul (by norm_num : (0 : ℝ) ≤ 16), h16]

/-- **Main Theorem**: Kahan's area formula is equivalent to Heron's formula.

    For any valid triangle (sides satisfying the triangle inequality),
    the Kahan formula and the classical Heron formula give the same area.
    This proves the mathematical correctness of Kahan's algorithm. -/
theorem kahan_area_eq_triangle_area {a b c : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : a < b + c) (hbc : b < a + c) (hca : c < a + b) :
    kahan_area a b c = triangle_area a b c := by
  unfold kahan_area triangle_area
  have hH := heron_product_nonneg ha hb hc hab hbc hca
  rw [kahan_eq_sixteen_heron, sqrt_sixteen_mul hH]
  ring

-- ════════════════════════════════════════════════════════════════
-- PART V: Numerical Stability Structure
-- ════════════════════════════════════════════════════════════════

/-!
### Why Kahan's Ordering Matters for Floating-Point

When sides satisfy a ≥ b ≥ c, each factor in the Kahan product is
individually non-negative:

  a + (b + c) = a + b + c ≥ a > 0           [clearly positive]
  c - (a - b) = b + c - a ≥ 0               [from a < b + c]
  c + (a - b) ≥ 0                            [since a ≥ b, so a - b ≥ 0]
  a + (b - c) ≥ 0                            [since b ≥ c, so b - c ≥ 0]

Moreover, the grouping `c - (a - b)` computes `a - b` first (which is
small when a ≈ b), then subtracts this small quantity from c. This is
more accurate than computing `b + c - a` directly when a ≈ b + c, where
catastrophic cancellation would occur.
-/

/-- **Stability Lemma**: When a ≥ b ≥ c > 0 with the triangle inequality a < b + c,
    each factor in the Kahan product is individually non-negative.

    The ordering a ≥ b ≥ c ensures that a - b ≥ 0 and b - c ≥ 0, making
    each intermediate computation `c - (a - b)` and `a + (b - c)` a
    subtraction of a non-negative quantity — the most favorable case
    for floating-point precision. -/
theorem kahan_factors_nonneg_ordered {a b c : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab_ord : b ≤ a) (hbc_ord : c ≤ b)
    (htri : a < b + c) :  -- Only the "hardest" triangle inequality needed
    0 ≤ a + (b + c) ∧
    0 ≤ c - (a - b) ∧
    0 ≤ c + (a - b) ∧
    0 ≤ a + (b - c) := by
  constructor
  · linarith  -- a + b + c ≥ a > 0
  constructor
  · linarith  -- b + c - a ≥ 0 by triangle inequality
  constructor
  · linarith  -- c + (a - b) ≥ 0: since a ≥ b, so a - b ≥ 0
  · linarith  -- a + (b - c) ≥ 0: since b ≥ c, so b - c ≥ 0

/-- **Sharpness**: The triangle inequality a < b + c is exactly the condition
    ensuring c - (a - b) ≥ 0, i.e., b + c > a.
    This factor vanishes as the triangle becomes degenerate (a → b + c). -/
theorem kahan_degenerate_factor {a b c : ℝ}
    (h : a = b + c) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab_ord : b ≤ a) (hbc_ord : c ≤ b) :
    c - (a - b) = 0 := by
  linarith

-- ════════════════════════════════════════════════════════════════
-- PART VI: Worked Examples
-- ════════════════════════════════════════════════════════════════

/-!
### 3-4-5 Right Triangle

For the 3-4-5 right triangle (with sides in any order):
- Kahan product: (3+(4+5)) · (5-(3-4)) · (5+(3-4)) · (3+(4-5))
                = 12 · 6 · 4 · 2 = 576
- Kahan area: √576 / 4 = 24 / 4 = 6 ✓
  (matches direct: (1/2) · 3 · 4 = 6)
-/

theorem kahan_product_345 : kahan_product 3 4 5 = 576 := by
  unfold kahan_product; norm_num

theorem kahan_product_534 : kahan_product 5 4 3 = 576 := by
  unfold kahan_product; norm_num

theorem kahan_area_345 : kahan_area 3 4 5 = 6 := by
  unfold kahan_area
  rw [kahan_product_345]
  have h : sqrt 576 = 24 := by
    rw [show (576 : ℝ) = 24 ^ 2 from by norm_num]
    exact sqrt_sq (by norm_num : (0 : ℝ) ≤ 24)
  rw [h]; norm_num

/-!
### 5-12-13 Right Triangle

For the 5-12-13 right triangle (ordered: a=13, b=12, c=5):
- Kahan product: (13+(12+5)) · (5-(13-12)) · (5+(13-12)) · (13+(12-5))
                = 30 · 4 · 6 · 20 = 14400
- Kahan area: √14400 / 4 = 120 / 4 = 30 ✓
  (matches direct: (1/2) · 5 · 12 = 30)
-/

theorem kahan_product_5_12_13 : kahan_product 13 12 5 = 14400 := by
  unfold kahan_product; norm_num

theorem kahan_area_5_12_13 : kahan_area 13 12 5 = 30 := by
  unfold kahan_area
  rw [kahan_product_5_12_13]
  have h : sqrt 14400 = 120 := by
    rw [show (14400 : ℝ) = 120 ^ 2 from by norm_num]
    exact sqrt_sq (by norm_num : (0 : ℝ) ≤ 120)
  rw [h]; norm_num

/-!
### Nearly Degenerate Triangle: 10-10-1

For sides 10, 10, 1 (isoceles, very flat in ratio 20:1):
- Semi-perimeter: s = 10.5
- Heron product: 10.5 · 0.5 · 0.5 · 9.5 = 24.9375
- Kahan product: 399 = 16 · 24.9375
- The factor c - (a - b) = 1 - (10 - 10) = 1 (stays well-conditioned).
  Classical formula: s - a = 10.5 - 10 = 0.5 (one small subtraction).

For even flatter triangles (e.g., 100 - 100 - ε), the Kahan grouping
prevents loss of precision in floating-point, while the naive
computation of s - a = (b + c - a)/2 would lose precision.
-/

theorem kahan_product_10_10_1 : kahan_product 10 10 1 = 399 := by
  unfold kahan_product; norm_num

theorem kahan_product_10_10_1_eq_sixteen_heron :
    (16 : ℝ) * heron_product 10 10 1 = 399 := by
  rw [← kahan_eq_sixteen_heron, kahan_product_10_10_1]

-- ════════════════════════════════════════════════════════════════
-- PART VII: Summary
-- ════════════════════════════════════════════════════════════════

-- Export key results
#check @kahan_eq_sixteen_heron      -- kahan = 16 * heron (ring identity)
#check @kahan_product_nonneg        -- non-negativity from triangle inequality
#check @kahan_area_eq_triangle_area -- Kahan area = Heron area
#check @kahan_factors_nonneg_ordered -- ordering gives factor-wise non-negativity

end KahanHeron
