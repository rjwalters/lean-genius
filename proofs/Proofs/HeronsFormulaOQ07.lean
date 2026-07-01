/-
  Weitzenböck's Inequality from Heron's Formula

  For any nondegenerate triangle with side lengths a, b, c and area
  Area = √(s(s-a)(s-b)(s-c)) (s = (a+b+c)/2 the semi-perimeter),

      a² + b² + c² ≥ 4·√3·Area,

  with equality if and only if the triangle is equilateral (a = b = c).

  This is a child of the Heron's formula gallery entry (oq-07). Squaring both
  sides turns the statement into a polynomial inequality in a, b, c, because
  (4√3)² = 48 and Area² = s(s-a)(s-b)(s-c):

      (a² + b² + c²)² ≥ 48·s(s-a)(s-b)(s-c).

  The mathematical heart is the sum-of-squares certificate

      (a²+b²+c²)² - 48·s(s-a)(s-b)(s-c)
          = 2·((a²-b²)² + (b²-c²)² + (c²-a²)²)  ≥ 0,

  which holds for ALL reals a, b, c (no triangle inequality needed). The
  triangle inequalities enter only to make Area² ≥ 0, so that Area = √(Area²)
  is real and the squaring step is reversible. Equality forces each square to
  vanish, i.e. a² = b² = c², which for positive sides means a = b = c.

  Axioms: 0
  Sorries: 0
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

namespace WeitzenbockHeronOQ07

open Real

-- ════════════════════════════════════════════════════════════════
-- PART I: Triangle data — semi-perimeter, Heron product, area
-- ════════════════════════════════════════════════════════════════

/-- Semi-perimeter. -/
noncomputable def semiperimeter (a b c : ℝ) : ℝ := (a + b + c) / 2

/-- Heron's product `s(s-a)(s-b)(s-c)`; the squared area. -/
noncomputable def heronProduct (a b c : ℝ) : ℝ :=
  semiperimeter a b c * (semiperimeter a b c - a)
    * (semiperimeter a b c - b) * (semiperimeter a b c - c)

/-- Heron's area `√(s(s-a)(s-b)(s-c))`. -/
noncomputable def area (a b c : ℝ) : ℝ := sqrt (heronProduct a b c)

/-- For a nondegenerate triangle, Heron's product is non-negative. -/
theorem heronProduct_nonneg {a b c : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : a < b + c) (hbc : b < a + c) (hca : c < a + b) :
    0 ≤ heronProduct a b c := by
  unfold heronProduct semiperimeter
  apply mul_nonneg
  apply mul_nonneg
  apply mul_nonneg
  all_goals linarith

-- ════════════════════════════════════════════════════════════════
-- PART II: The algebraic core — a sum-of-squares certificate
-- ════════════════════════════════════════════════════════════════

/-- **The Weitzenböck SOS identity.** For all reals,

    `(a²+b²+c²)² - 48·heronProduct a b c = 2·((a²-b²)²+(b²-c²)²+(c²-a²)²)`.

This is the exact certificate behind the squared inequality; being an identity,
it also supplies the equality case. -/
theorem sq_sum_sub_heron (a b c : ℝ) :
    (a ^ 2 + b ^ 2 + c ^ 2) ^ 2 - 48 * heronProduct a b c
      = 2 * ((a ^ 2 - b ^ 2) ^ 2 + (b ^ 2 - c ^ 2) ^ 2 + (c ^ 2 - a ^ 2) ^ 2) := by
  unfold heronProduct semiperimeter
  ring

/-- **The squared Weitzenböck inequality** (holds for all reals, no triangle
condition): `48·heronProduct a b c ≤ (a²+b²+c²)²`. -/
theorem weitzenbock_sq (a b c : ℝ) :
    48 * heronProduct a b c ≤ (a ^ 2 + b ^ 2 + c ^ 2) ^ 2 := by
  nlinarith [sq_nonneg (a ^ 2 - b ^ 2), sq_nonneg (b ^ 2 - c ^ 2),
             sq_nonneg (c ^ 2 - a ^ 2), sq_sum_sub_heron a b c]

/-- Equality in the squared inequality forces `a² = b²` and `b² = c²`. -/
theorem weitzenbock_sq_eq_iff (a b c : ℝ) :
    (a ^ 2 + b ^ 2 + c ^ 2) ^ 2 = 48 * heronProduct a b c ↔
      a ^ 2 = b ^ 2 ∧ b ^ 2 = c ^ 2 := by
  constructor
  · intro h
    have hsos : (a ^ 2 - b ^ 2) ^ 2 + (b ^ 2 - c ^ 2) ^ 2 + (c ^ 2 - a ^ 2) ^ 2 = 0 := by
      have := sq_sum_sub_heron a b c; linarith
    have t1 : 0 ≤ (a ^ 2 - b ^ 2) ^ 2 := sq_nonneg _
    have t2 : 0 ≤ (b ^ 2 - c ^ 2) ^ 2 := sq_nonneg _
    have t3 : 0 ≤ (c ^ 2 - a ^ 2) ^ 2 := sq_nonneg _
    have e1 : (a ^ 2 - b ^ 2) ^ 2 = 0 := by linarith
    have e2 : (b ^ 2 - c ^ 2) ^ 2 = 0 := by linarith
    exact ⟨by nlinarith [sq_eq_zero_iff.mp e1], by nlinarith [sq_eq_zero_iff.mp e2]⟩
  · rintro ⟨h1, h2⟩
    have := sq_sum_sub_heron a b c
    nlinarith [this, h1, h2]

-- ════════════════════════════════════════════════════════════════
-- PART III: Weitzenböck's inequality
-- ════════════════════════════════════════════════════════════════

/-- **Weitzenböck's inequality.** For a nondegenerate triangle,

    `4·√3·Area ≤ a² + b² + c²`.

The area is `√(heronProduct a b c)`; both sides are non-negative, so the claim
is equivalent to the squared inequality `weitzenbock_sq`, upgraded through
`Real.sqrt` monotonicity. -/
theorem weitzenbock {a b c : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : a < b + c) (hbc : b < a + c) (hca : c < a + b) :
    4 * Real.sqrt 3 * area a b c ≤ a ^ 2 + b ^ 2 + c ^ 2 := by
  have hp : 0 ≤ heronProduct a b c := heronProduct_nonneg ha hb hc hab hbc hca
  set A : ℝ := area a b c with hA
  have hA2 : A ^ 2 = heronProduct a b c := by rw [hA, area]; exact Real.sq_sqrt hp
  have hA0 : 0 ≤ A := by rw [hA, area]; exact Real.sqrt_nonneg _
  set s3 : ℝ := Real.sqrt 3 with hs3
  have hs32 : s3 ^ 2 = 3 := by rw [hs3]; exact Real.sq_sqrt (by norm_num)
  have hs30 : 0 ≤ s3 := by rw [hs3]; exact Real.sqrt_nonneg _
  -- the squared inequality, phrased for Y = 4·s3·A and X = a²+b²+c²
  have hYsq : (4 * s3 * A) ^ 2 = 48 * heronProduct a b c := by
    have : (4 * s3 * A) ^ 2 = 16 * s3 ^ 2 * A ^ 2 := by ring
    rw [this, hs32, hA2]; ring
  have hsq : (4 * s3 * A) ^ 2 ≤ (a ^ 2 + b ^ 2 + c ^ 2) ^ 2 := by
    rw [hYsq]; exact weitzenbock_sq a b c
  have hY0 : 0 ≤ 4 * s3 * A := by positivity
  have hX0 : 0 ≤ a ^ 2 + b ^ 2 + c ^ 2 := by positivity
  have h := Real.sqrt_le_sqrt hsq
  rwa [Real.sqrt_sq hY0, Real.sqrt_sq hX0] at h

/-- **Equality in Weitzenböck's inequality holds iff the triangle is
equilateral.** -/
theorem weitzenbock_eq_iff {a b c : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : a < b + c) (hbc : b < a + c) (hca : c < a + b) :
    4 * Real.sqrt 3 * area a b c = a ^ 2 + b ^ 2 + c ^ 2 ↔ a = b ∧ b = c := by
  have hp : 0 ≤ heronProduct a b c := heronProduct_nonneg ha hb hc hab hbc hca
  have hA2 : area a b c ^ 2 = heronProduct a b c := by rw [area]; exact Real.sq_sqrt hp
  have hA0 : 0 ≤ area a b c := by rw [area]; exact Real.sqrt_nonneg _
  have hs32 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hs30 : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg _
  have hYsq : (4 * Real.sqrt 3 * area a b c) ^ 2 = 48 * heronProduct a b c := by
    have : (4 * Real.sqrt 3 * area a b c) ^ 2
        = 16 * Real.sqrt 3 ^ 2 * area a b c ^ 2 := by ring
    rw [this, hs32, hA2]; ring
  have hY0 : 0 ≤ 4 * Real.sqrt 3 * area a b c := by positivity
  have hX0 : 0 ≤ a ^ 2 + b ^ 2 + c ^ 2 := by positivity
  constructor
  · intro h
    -- equality of nonneg values ⇒ equality of squares ⇒ SOS = 0
    have hsqeq : (a ^ 2 + b ^ 2 + c ^ 2) ^ 2 = 48 * heronProduct a b c := by
      rw [← hYsq, h]
    obtain ⟨hab2, hbc2⟩ := (weitzenbock_sq_eq_iff a b c).mp hsqeq
    have hab' : a = b := by
      have hs : (0 : ℝ) < a + b := by linarith
      have : (a - b) * (a + b) = 0 := by nlinarith [hab2]
      rcases mul_eq_zero.mp this with h0 | h0
      · linarith
      · linarith
    have hbc' : b = c := by
      have hs : (0 : ℝ) < b + c := by linarith
      have : (b - c) * (b + c) = 0 := by nlinarith [hbc2]
      rcases mul_eq_zero.mp this with h0 | h0
      · linarith
      · linarith
    exact ⟨hab', hbc'⟩
  · rintro ⟨hab', hbc'⟩
    subst hab'; subst hbc'
    -- reduce to the squared identity: both sides nonneg with equal squares
    have hsqeq : (a ^ 2 + a ^ 2 + a ^ 2) ^ 2 = (4 * Real.sqrt 3 * area a a a) ^ 2 := by
      rw [hYsq]
      have := sq_sum_sub_heron a a a
      nlinarith [this]
    have h := Real.sqrt_le_sqrt (le_of_eq hsqeq)
    have h' := Real.sqrt_le_sqrt (le_of_eq hsqeq.symm)
    have hX0' : 0 ≤ a ^ 2 + a ^ 2 + a ^ 2 := by positivity
    have hY0' : 0 ≤ 4 * Real.sqrt 3 * area a a a := by positivity
    rw [Real.sqrt_sq hX0', Real.sqrt_sq hY0'] at h
    rw [Real.sqrt_sq hY0', Real.sqrt_sq hX0'] at h'
    linarith

end WeitzenbockHeronOQ07
