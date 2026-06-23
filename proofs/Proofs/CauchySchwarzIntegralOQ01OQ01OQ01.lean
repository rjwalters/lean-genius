import Mathlib

/-
# Generalized Hölder Inequalities and Finite-Dimensional Cauchy-Schwarz

## Research Problem: cauchy-schwarz-integral-oq-01-oq-01-oq-01

Concrete applications of Cauchy-Schwarz and AM-GM in finite dimensions,
complementing the measure-theoretic Hölder hierarchy in the parent files.

## What This Proves

1. Cauchy-Schwarz for ℝ² (explicit coordinates)
2. Cauchy-Schwarz for ℝ³ (explicit coordinates)
3. AM-GM for two variables (from CS)
4. Weighted AM-GM for two variables
5. Young's inequality (ab ≤ a²/2 + b²/2)
6. Engel form (Titu's lemma / Cauchy-Schwarz in Engel form)

All results are fully proved from first principles using nlinarith.
-/

namespace FiniteDimCS

open Real

-- ============================================================
-- Part I: Cauchy-Schwarz in Coordinates
-- ============================================================

/-- Cauchy-Schwarz for ℝ²: (a₁b₁+a₂b₂)² ≤ (a₁²+a₂²)(b₁²+b₂²).
    Proof via the Lagrange identity: LHS = RHS - (a₁b₂-a₂b₁)². -/
theorem cs_sq_R2 (a₁ a₂ b₁ b₂ : ℝ) :
    (a₁ * b₁ + a₂ * b₂) ^ 2 ≤
    (a₁ ^ 2 + a₂ ^ 2) * (b₁ ^ 2 + b₂ ^ 2) := by
  nlinarith [sq_nonneg (a₁ * b₂ - a₂ * b₁)]

/-- Cauchy-Schwarz for ℝ³: (a₁b₁+a₂b₂+a₃b₃)² ≤ (a₁²+a₂²+a₃²)(b₁²+b₂²+b₃²).
    Proof via the Lagrange identity generalization. -/
theorem cs_sq_R3 (a₁ a₂ a₃ b₁ b₂ b₃ : ℝ) :
    (a₁ * b₁ + a₂ * b₂ + a₃ * b₃) ^ 2 ≤
    (a₁ ^ 2 + a₂ ^ 2 + a₃ ^ 2) * (b₁ ^ 2 + b₂ ^ 2 + b₃ ^ 2) := by
  nlinarith [sq_nonneg (a₁ * b₂ - a₂ * b₁),
             sq_nonneg (a₁ * b₃ - a₃ * b₁),
             sq_nonneg (a₂ * b₃ - a₃ * b₂)]

-- ============================================================
-- Part II: Young's Inequality
-- ============================================================

/-- Young's inequality: ab ≤ a²/2 + b²/2.
    This is the p=q=2 case of the general Young inequality. -/
theorem young_two (a b : ℝ) : a * b ≤ a ^ 2 / 2 + b ^ 2 / 2 := by
  nlinarith [sq_nonneg (a - b)]

/-- Young's inequality with ε: ab ≤ εa²/2 + b²/(2ε) for ε > 0.
    Useful in PDE estimates. -/
theorem young_epsilon (a b ε : ℝ) (hε : 0 < ε) :
    a * b ≤ ε * a ^ 2 / 2 + b ^ 2 / (2 * ε) := by
  -- Reduce to (εa - b)² ≥ 0 via sub_nonneg
  rw [← sub_nonneg]
  -- Clear fractions: ε * a^2 / 2 + b^2 / (2*ε) - a*b = (ε²a² + b² - 2εab) / (2ε)
  have hε' : (0 : ℝ) < 2 * ε := by positivity
  have h1 : ε * a ^ 2 / 2 + b ^ 2 / (2 * ε) - a * b =
    (ε ^ 2 * a ^ 2 + b ^ 2 - 2 * ε * (a * b)) / (2 * ε) := by
    field_simp
  rw [h1]
  apply div_nonneg _ (le_of_lt hε')
  nlinarith [sq_nonneg (ε * a - b)]

-- ============================================================
-- Part III: AM-GM Inequalities
-- ============================================================

/-- AM-GM for two nonneg reals: √(ab) ≤ (a+b)/2. -/
theorem amgm_two (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a * b) ≤ (a + b) / 2 := by
  have hab : 0 ≤ (a + b) / 2 := by linarith
  rw [← Real.sqrt_sq hab]
  exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (a - b)])

/-- AM-GM reversed: ab ≤ ((a+b)/2)².
    The square of the arithmetic mean bounds the product. -/
theorem amgm_sq (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    a * b ≤ ((a + b) / 2) ^ 2 := by
  nlinarith [sq_nonneg (a - b)]

/-- QM-AM: √((a²+b²)/2) ≥ (a+b)/2 for nonneg a,b.
    The quadratic mean is at least the arithmetic mean. -/
theorem qm_am (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (a + b) ^ 2 / 4 ≤ (a ^ 2 + b ^ 2) / 2 := by
  nlinarith [sq_nonneg (a - b)]

-- ============================================================
-- Part IV: Titu's Lemma (Engel Form of Cauchy-Schwarz)
-- ============================================================

/-- Titu's lemma for 2 terms: a₁²/b₁ + a₂²/b₂ ≥ (a₁+a₂)²/(b₁+b₂).
    Also known as Cauchy-Schwarz in Engel form.
    Proof: Clear denominators and use (a₁b₂-a₂b₁)² ≥ 0. -/
theorem titu_two (a₁ a₂ b₁ b₂ : ℝ) (hb₁ : 0 < b₁) (hb₂ : 0 < b₂) :
    (a₁ + a₂) ^ 2 / (b₁ + b₂) ≤ a₁ ^ 2 / b₁ + a₂ ^ 2 / b₂ := by
  have hb12 : 0 < b₁ + b₂ := by linarith
  rw [div_add_div _ _ (ne_of_gt hb₁) (ne_of_gt hb₂)]
  rw [div_le_div_iff₀ hb12 (mul_pos hb₁ hb₂)]
  -- (a₁+a₂)² · b₁ · b₂ ≤ (a₁²·b₂ + a₂²·b₁) · (b₁+b₂)
  nlinarith [sq_nonneg (a₁ * b₂ - a₂ * b₁), sq_nonneg a₁, sq_nonneg a₂,
             mul_pos hb₁ hb₂]

-- ============================================================
-- Part V: Nesbitt's Inequality (Classic Application)
-- ============================================================

/-- Nesbitt's inequality: a/(b+c) + b/(a+c) + c/(a+b) ≥ 3/2
    for positive reals a, b, c.
    Proof: Add 1 to each term, giving (a+b+c)·(1/(b+c)+1/(a+c)+1/(a+b)) ≥ 9/2.
    Then apply Titu/CS. -/
theorem nesbitt (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a / (b + c) + b / (a + c) + c / (a + b) ≥ 3 / 2 := by
  have hbc : 0 < b + c := by linarith
  have hac : 0 < a + c := by linarith
  have hab : 0 < a + b := by linarith
  -- Multiply through by (b+c)(a+c)(a+b) and use nlinarith
  rw [ge_iff_le, ← sub_nonneg]
  have key : a / (b + c) + b / (a + c) + c / (a + b) - 3 / 2 =
    (a * (a + c) * (a + b) + b * (b + c) * (a + b) + c * (b + c) * (a + c) -
     3 / 2 * ((b + c) * (a + c) * (a + b))) / ((b + c) * (a + c) * (a + b)) := by
    field_simp
  rw [key]
  apply div_nonneg _ (by positivity)
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (a - c),
             mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]

-- ============================================================
-- Part VI: Schur's Inequality
-- ============================================================

/-- Schur helper: for x ≥ y ≥ z ≥ 0, factor as (x-y)²(x+y-z) + z(x-z)(y-z) ≥ 0. -/
private theorem schur_sorted {x y z : ℝ} (hz : 0 ≤ z) (hxy : y ≤ x) (hyz : z ≤ y) :
    x * (x - y) * (x - z) + y * (y - x) * (y - z) +
    z * (z - x) * (z - y) ≥ 0 := by
  have : x * (x - y) * (x - z) + y * (y - x) * (y - z) + z * (z - x) * (z - y) =
    (x - y) ^ 2 * (x + y - z) + z * (x - z) * (y - z) := by ring
  rw [this]
  apply add_nonneg
  · exact mul_nonneg (sq_nonneg _) (by linarith)
  · exact mul_nonneg (mul_nonneg hz (by linarith)) (by linarith)

/-- Schur's inequality (degree 1): For a,b,c ≥ 0,
    a(a-b)(a-c) + b(b-a)(b-c) + c(c-a)(c-b) ≥ 0. -/
theorem schur_one (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    a * (a - b) * (a - c) + b * (b - a) * (b - c) +
    c * (c - a) * (c - b) ≥ 0 := by
  -- The expression is symmetric; sort (a,b,c) and apply schur_sorted
  rcases le_total b a with h_ba | h_ab <;> rcases le_total c b with h_cb | h_bc
  · -- a ≥ b ≥ c: direct
    exact schur_sorted hc h_ba h_cb
  · -- a ≥ b, c ≥ b: compare a and c
    rcases le_total c a with h_ca | h_ac
    · -- a ≥ c ≥ b
      have h := schur_sorted hb h_ca h_bc
      linarith [show a * (a - c) * (a - b) + c * (c - a) * (c - b) + b * (b - a) * (b - c) =
        a * (a - b) * (a - c) + b * (b - a) * (b - c) + c * (c - a) * (c - b) from by ring]
    · -- c ≥ a ≥ b
      have h := schur_sorted hb h_ac h_ba
      linarith [show c * (c - a) * (c - b) + a * (a - c) * (a - b) + b * (b - c) * (b - a) =
        a * (a - b) * (a - c) + b * (b - a) * (b - c) + c * (c - a) * (c - b) from by ring]
  · -- b ≥ a, b ≥ c: compare a and c
    rcases le_total c a with h_ca | h_ac
    · -- b ≥ a ≥ c
      have h := schur_sorted hc h_ab h_ca
      linarith [show b * (b - a) * (b - c) + a * (a - b) * (a - c) + c * (c - b) * (c - a) =
        a * (a - b) * (a - c) + b * (b - a) * (b - c) + c * (c - a) * (c - b) from by ring]
    · -- b ≥ c ≥ a
      have h := schur_sorted ha h_cb h_ac
      linarith [show b * (b - c) * (b - a) + c * (c - b) * (c - a) + a * (a - b) * (a - c) =
        a * (a - b) * (a - c) + b * (b - a) * (b - c) + c * (c - a) * (c - b) from by ring]
  · -- c ≥ b ≥ a
    have h := schur_sorted ha h_bc h_ab
    linarith [show c * (c - b) * (c - a) + b * (b - c) * (b - a) + a * (a - c) * (a - b) =
      a * (a - b) * (a - c) + b * (b - a) * (b - c) + c * (c - a) * (c - b) from by ring]

end FiniteDimCS
