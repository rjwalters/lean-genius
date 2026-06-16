/-
  Weitzenböck's Inequality

  For a triangle with side lengths a, b, c and area T:

    a² + b² + c² ≥ 4·√3·T

  with equality if and only if the triangle is equilateral (a = b = c).

  Proof approach (purely elementary, no transcendental estimates):
  - Encode the area through Heron's product: T = √(s(s-a)(s-b)(s-c)),
    so 16·T² = 2a²b² + 2b²c² + 2c²a² − a⁴ − b⁴ − c⁴.
  - Square the target: since both sides are non-negative it suffices to show
      (a² + b² + c²)² ≥ 48·T².
  - Substituting the Heron expansion, the gap is the sum of squares
      (a² + b² + c²)² − 48·T² = 2·[(a²−b²)² + (b²−c²)² + (c²−a²)²] ≥ 0.
  - Equality forces each (a²−b²)² = 0, hence a = b = c (positivity).

  Axioms: 0
  Sorries: 0
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

namespace WeitzenbockInequality

open Real

-- ════════════════════════════════════════════════════════════════
-- PART I: Area via Heron's product
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

/-- Classical Heron area: Area = √(s(s-a)(s-b)(s-c)). -/
noncomputable def triangle_area (a b c : ℝ) : ℝ :=
  sqrt (heron_product a b c)

/-- The squared area equals the Heron product (for valid triangles). -/
theorem triangle_area_sq {a b c : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : a < b + c) (hbc : b < a + c) (hca : c < a + b) :
    (triangle_area a b c) ^ 2 = heron_product a b c := by
  unfold triangle_area
  exact Real.sq_sqrt (heron_product_nonneg ha hb hc hab hbc hca)

/-- **Heron's 16-fold expansion**: 16·T² is a symmetric polynomial in a, b, c. -/
theorem heron_sixteen (a b c : ℝ) :
    16 * heron_product a b c =
      2 * a ^ 2 * b ^ 2 + 2 * b ^ 2 * c ^ 2 + 2 * c ^ 2 * a ^ 2
      - a ^ 4 - b ^ 4 - c ^ 4 := by
  unfold heron_product; ring

-- ════════════════════════════════════════════════════════════════
-- PART II: The SOS core
-- ════════════════════════════════════════════════════════════════

/-- **Key sum-of-squares identity.** The Weitzenböck gap, after squaring the
    target and clearing the area, is a non-negative sum of squares:

      (a²+b²+c²)² − 48·heron_product = 2·[(a²−b²)²+(b²−c²)²+(c²−a²)²]. -/
theorem weitzenbock_sos_identity (a b c : ℝ) :
    (a ^ 2 + b ^ 2 + c ^ 2) ^ 2 - 48 * heron_product a b c =
      2 * ((a ^ 2 - b ^ 2) ^ 2 + (b ^ 2 - c ^ 2) ^ 2 + (c ^ 2 - a ^ 2) ^ 2) := by
  have h := heron_sixteen a b c
  nlinarith [h]

/-- The squared form of Weitzenböck's inequality:
      (a²+b²+c²)² ≥ 48·heron_product. -/
theorem weitzenbock_sq (a b c : ℝ) :
    48 * heron_product a b c ≤ (a ^ 2 + b ^ 2 + c ^ 2) ^ 2 := by
  have hid := weitzenbock_sos_identity a b c
  nlinarith [sq_nonneg (a ^ 2 - b ^ 2), sq_nonneg (b ^ 2 - c ^ 2),
             sq_nonneg (c ^ 2 - a ^ 2), hid]

-- ════════════════════════════════════════════════════════════════
-- PART III: Weitzenböck's inequality
-- ════════════════════════════════════════════════════════════════

/-- **Weitzenböck's inequality**: for a triangle with sides a, b, c and area
    T = triangle_area a b c,

      a² + b² + c² ≥ 4·√3·T. -/
theorem weitzenbock {a b c : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : a < b + c) (hbc : b < a + c) (hca : c < a + b) :
    a ^ 2 + b ^ 2 + c ^ 2 ≥ 4 * sqrt 3 * triangle_area a b c := by
  have hhp : 0 ≤ heron_product a b c := heron_product_nonneg ha hb hc hab hbc hca
  set T := triangle_area a b c with hT_def
  have hT_nonneg : 0 ≤ T := by rw [hT_def]; unfold triangle_area; exact sqrt_nonneg _
  have hTsq : T ^ 2 = heron_product a b c := triangle_area_sq ha hb hc hab hbc hca
  set c3 := sqrt 3 with hc3_def
  have hc3_nonneg : 0 ≤ c3 := by rw [hc3_def]; exact sqrt_nonneg _
  have hc3sq : c3 ^ 2 = 3 := by rw [hc3_def]; exact Real.sq_sqrt (by norm_num)
  set S := a ^ 2 + b ^ 2 + c ^ 2 with hS_def
  have hS_nonneg : (0 : ℝ) ≤ S := by rw [hS_def]; positivity
  -- The right-hand side squared equals 48·heron_product.
  have hrhs_sq : (4 * c3 * T) ^ 2 = 48 * heron_product a b c := by
    have e : (4 * c3 * T) ^ 2 = 16 * c3 ^ 2 * T ^ 2 := by ring
    rw [e, hc3sq, hTsq]; ring
  have hrhs_nonneg : 0 ≤ 4 * c3 * T :=
    mul_nonneg (mul_nonneg (by norm_num) hc3_nonneg) hT_nonneg
  -- Squared inequality, then descend by monotonicity of √.
  have hsq_le : (4 * c3 * T) ^ 2 ≤ S ^ 2 := by
    rw [hrhs_sq, hS_def]; exact weitzenbock_sq a b c
  have : 4 * c3 * T ≤ S := by
    calc 4 * c3 * T = sqrt ((4 * c3 * T) ^ 2) := (Real.sqrt_sq hrhs_nonneg).symm
      _ ≤ sqrt (S ^ 2) := Real.sqrt_le_sqrt hsq_le
      _ = S := Real.sqrt_sq hS_nonneg
  linarith

-- ════════════════════════════════════════════════════════════════
-- PART IV: Equality characterization
-- ════════════════════════════════════════════════════════════════

/-- **Equality holds iff the triangle is equilateral.** -/
theorem weitzenbock_eq_iff {a b c : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : a < b + c) (hbc : b < a + c) (hca : c < a + b) :
    a ^ 2 + b ^ 2 + c ^ 2 = 4 * sqrt 3 * triangle_area a b c ↔ a = b ∧ b = c := by
  have hhp : 0 ≤ heron_product a b c := heron_product_nonneg ha hb hc hab hbc hca
  have hTsq : (triangle_area a b c) ^ 2 = heron_product a b c :=
    triangle_area_sq ha hb hc hab hbc hca
  constructor
  · intro heq
    -- Square the equality: (a²+b²+c²)² = 48·heron_product.
    have hSsq : (a ^ 2 + b ^ 2 + c ^ 2) ^ 2 = 48 * heron_product a b c := by
      have hrhs_sq : (4 * sqrt 3 * triangle_area a b c) ^ 2 = 48 * heron_product a b c := by
        have e : (4 * sqrt 3 * triangle_area a b c) ^ 2
            = 16 * (sqrt 3) ^ 2 * (triangle_area a b c) ^ 2 := by ring
        rw [e, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3), hTsq]; ring
      rw [heq]; exact hrhs_sq
    -- The SOS gap vanishes.
    have hsos : (a ^ 2 - b ^ 2) ^ 2 + (b ^ 2 - c ^ 2) ^ 2 + (c ^ 2 - a ^ 2) ^ 2 = 0 := by
      have hid := weitzenbock_sos_identity a b c
      nlinarith [hid, hSsq]
    -- Hence each squared difference is zero.
    have e1 : (a ^ 2 - b ^ 2) ^ 2 = 0 :=
      le_antisymm (by nlinarith [sq_nonneg (b ^ 2 - c ^ 2), sq_nonneg (c ^ 2 - a ^ 2), hsos])
        (sq_nonneg _)
    have e2 : (b ^ 2 - c ^ 2) ^ 2 = 0 :=
      le_antisymm (by nlinarith [sq_nonneg (a ^ 2 - b ^ 2), sq_nonneg (c ^ 2 - a ^ 2), hsos])
        (sq_nonneg _)
    -- Recover a = b and b = c using positivity.
    have hab2 : a ^ 2 - b ^ 2 = 0 := pow_eq_zero_iff (by norm_num) |>.mp e1
    have hbc2 : b ^ 2 - c ^ 2 = 0 := pow_eq_zero_iff (by norm_num) |>.mp e2
    have hab' : a = b := by
      have hfac : (a - b) * (a + b) = 0 := by linear_combination hab2
      rcases mul_eq_zero.mp hfac with h | h
      · linarith
      · linarith
    have hbc' : b = c := by
      have hfac : (b - c) * (b + c) = 0 := by linear_combination hbc2
      rcases mul_eq_zero.mp hfac with h | h
      · linarith
      · linarith
    exact ⟨hab', hbc'⟩
  · rintro ⟨hab', hbc'⟩
    rw [hab', hbc']
    -- All sides equal to c; compute both sides directly.
    have hhp3 : heron_product c c c = 3 * c ^ 4 / 16 := by unfold heron_product; ring
    have hT3 : triangle_area c c c = sqrt 3 * (c ^ 2 / 4) := by
      unfold triangle_area
      rw [hhp3, show (3 : ℝ) * c ^ 4 / 16 = 3 * (c ^ 2 / 4) ^ 2 from by ring,
        Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 3), Real.sqrt_sq (by positivity)]
    rw [hT3]
    have h3 : (sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    linear_combination (-c ^ 2) * h3

-- ════════════════════════════════════════════════════════════════
-- PART V: Worked examples / sanity checks
-- ════════════════════════════════════════════════════════════════

/-- Equilateral triangle with side 2: equality is attained. -/
theorem weitzenbock_equilateral_2 :
    (2 : ℝ) ^ 2 + 2 ^ 2 + 2 ^ 2 = 4 * sqrt 3 * triangle_area 2 2 2 := by
  have h : (0:ℝ) < 2 := by norm_num
  exact (weitzenbock_eq_iff h h h (by norm_num) (by norm_num) (by norm_num)).mpr ⟨rfl, rfl⟩

/-- The 3-4-5 right triangle is strictly non-equilateral, so the inequality
    is strict: 9 + 16 + 25 = 50 > 4√3·6 = 24√3 ≈ 41.57. -/
theorem weitzenbock_345_strict :
    4 * sqrt 3 * triangle_area 3 4 5 < (3 : ℝ) ^ 2 + 4 ^ 2 + 5 ^ 2 := by
  have h3 : (0:ℝ) < 3 := by norm_num
  have h4 : (0:ℝ) < 4 := by norm_num
  have h5 : (0:ℝ) < 5 := by norm_num
  have hge := weitzenbock h3 h4 h5 (by norm_num) (by norm_num) (by norm_num)
  rcases lt_or_eq_of_le hge with hlt | heq
  · linarith
  · -- equality would force equilateral, impossible here
    exfalso
    have := (weitzenbock_eq_iff h3 h4 h5 (by norm_num) (by norm_num) (by norm_num)).mp heq.symm
    obtain ⟨hab, _⟩ := this
    norm_num at hab

#check @weitzenbock           -- a²+b²+c² ≥ 4√3·T
#check @weitzenbock_eq_iff    -- equality iff equilateral
#check @weitzenbock_sq        -- squared form
#check @weitzenbock_sos_identity

end WeitzenbockInequality
