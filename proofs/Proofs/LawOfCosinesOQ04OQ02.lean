import Mathlib
import Proofs.LawOfCosinesOQ04

/-
# Angle Bisector Length Formula from Stewart's Theorem

## Open Question: law-of-cosines-oq-04-oq-02

The parent `LawOfCosinesOQ04.lean` proves Stewart's theorem:
  b²m + c²n = a(d² + mn)
for a cevian of length d from A to BC, with BD = m, DC = n, m + n = a.

This file derives the **angle bisector length formula** as a corollary.

**Statement**: In triangle ABC with sides a = BC, b = CA, c = AB, if the
angle bisector from A has length t and meets BC at D with BD = m, DC = n,
then:
  t² · (b+c)² = bc · ((b+c)² - a²)

Equivalently (when b+c ≠ 0):
  t² = bc · ((b+c)² - a²) / (b+c)²

**Key ingredients**:
1. The **angle bisector theorem**: BD/DC = AB/AC = c/b, i.e., m·b = n·c.
2. **Stewart's theorem** (parent file): b²m + c²n = a(t² + mn).

**Proof sketch**: The angle bisector ratio gives m·(b+c) = a·c, n·(b+c) = a·b.
Multiplying Stewart's theorem by (b+c)² and simplifying using these ratios:
  a · b²c(b+c) + a · bc²(b+c) - a³bc = a · t²(b+c)²
  a · bc(b+c)² - a³bc = a · t²(b+c)²
  t²(b+c)² = bc((b+c)² - a²)

All proofs use `linear_combination` with polynomial witnesses — no case
splitting or numerical tricks. Zero axioms, zero sorries.

## Summary: 7 theorems/lemmas, 0 sorries, 0 axioms

Tags: geometry, law-of-cosines, stewarts-theorem, angle-bisector,
      cevian, triangle-geometry, algebraic-proof
-/

open StewartsTheorem

namespace AngleBisectorLength

-- ============================================================
-- Part I: Angle Bisector Ratio Lemmas
-- ============================================================

/-- The angle bisector from A meets BC at D with BD = m, DC = n such that
    m·b = n·c (angle bisector theorem: BD/DC = AB/AC = c/b).

    From this ratio and m + n = a, derive: m·(b+c) = a·c.

    Proof: m·(b+c) = m·b + m·c = n·c + m·c = c·(m+n) = c·a. -/
lemma bisector_ratio_m (a b c m n : ℝ) (ha : m + n = a) (hbis : m * b = n * c) :
    m * (b + c) = a * c := by
  linear_combination c * ha + hbis

/-- Similarly: n·(b+c) = a·b.

    Proof: n·(b+c) = n·b + n·c = n·b + m·b = b·(m+n) = b·a. -/
lemma bisector_ratio_n (a b c m n : ℝ) (ha : m + n = a) (hbis : m * b = n * c) :
    n * (b + c) = a * b := by
  linear_combination b * ha - hbis

/-- The product of the two segments: m·n·(b+c)² = a²·b·c.

    Proof: (m·(b+c))·(n·(b+c)) = (a·c)·(a·b) = a²·b·c. -/
lemma bisector_product (a b c m n : ℝ) (ha : m + n = a) (hbis : m * b = n * c) :
    m * n * (b + c) ^ 2 = a ^ 2 * b * c := by
  have hm := bisector_ratio_m a b c m n ha hbis
  have hn := bisector_ratio_n a b c m n ha hbis
  linear_combination n * (b + c) * hm + a * c * hn

-- ============================================================
-- Part II: Main Theorem (Cleared-Denominator Form)
-- ============================================================

/-- **Angle Bisector Length Formula** (cleared-denominator form):

    Given the angle bisector ratio (m·b = n·c) and Stewart's theorem
    conclusion, derive: t²·(b+c)² = bc·((b+c)² - a²).

    **Proof by linear_combination**: The polynomial witness
      -(b+c)² · hstewart + b²·(b+c)·hm + c²·(b+c)·hn - a·hmn
    produces a · (t²·(b+c)² - bc·((b+c)² - a²)).
    Canceling a (since a_pos) gives the result. -/
theorem angle_bisector_squared (a b c t m n : ℝ)
    (ha : m + n = a)
    (hbis : m * b = n * c)
    (ha_pos : 0 < a)
    (hstewart : b ^ 2 * m + c ^ 2 * n = a * (t ^ 2 + m * n)) :
    t ^ 2 * (b + c) ^ 2 = b * c * ((b + c) ^ 2 - a ^ 2) := by
  have hm := bisector_ratio_m a b c m n ha hbis
  have hn := bisector_ratio_n a b c m n ha hbis
  have hmn := bisector_product a b c m n ha hbis
  have ha_ne : a ≠ 0 := ne_of_gt ha_pos
  have hkey : a * (t ^ 2 * (b + c) ^ 2) = a * (b * c * ((b + c) ^ 2 - a ^ 2)) := by
    linear_combination
      -(b + c) ^ 2 * hstewart +
      b ^ 2 * (b + c) * hm +
      c ^ 2 * (b + c) * hn -
      a * hmn
  exact mul_left_cancel₀ ha_ne hkey

/-- **Angle Bisector Length Formula** (ratio form):

    When b + c > 0, the result gives: t² = bc·((b+c)² - a²) / (b+c)². -/
theorem angle_bisector_ratio (a b c t m n : ℝ)
    (ha : m + n = a)
    (hbis : m * b = n * c)
    (ha_pos : 0 < a)
    (hbc_pos : 0 < b + c)
    (hstewart : b ^ 2 * m + c ^ 2 * n = a * (t ^ 2 + m * n)) :
    t ^ 2 = b * c * ((b + c) ^ 2 - a ^ 2) / (b + c) ^ 2 := by
  have h := angle_bisector_squared a b c t m n ha hbis ha_pos hstewart
  have hbc2_ne : (b + c) ^ 2 ≠ 0 := by positivity
  field_simp [hbc2_ne]
  linarith

-- ============================================================
-- Part III: Full Geometric Version
-- ============================================================

/-- **Angle Bisector Length Formula** (full geometric, law-of-cosines setup):

    In triangle ABC with sides a = BC, b = CA, c = AB:
    the angle bisector from A has length t, meeting BC at D with BD = m,
    DC = n, m + n = a, satisfying the law of cosines in sub-triangles.
    The angle bisector theorem gives m·b = n·c.

    Conclusion: t²·(b+c)² = bc·((b+c)² - a²). -/
theorem angle_bisector_length (a b c t m n : ℝ)
    (ha : m + n = a)
    (hbis : m * b = n * c)
    (ha_pos : 0 < a)
    (hbc_pos : 0 < b + c)
    (u : ℝ)
    (h_ABD : c ^ 2 = t ^ 2 + m ^ 2 - 2 * t * m * u)
    (h_ACD : b ^ 2 = t ^ 2 + n ^ 2 + 2 * t * n * u) :
    t ^ 2 * (b + c) ^ 2 = b * c * ((b + c) ^ 2 - a ^ 2) := by
  have hstewart := stewarts_theorem a b c t m n ha u h_ABD h_ACD
  exact angle_bisector_squared a b c t m n ha hbis ha_pos hstewart

-- ============================================================
-- Part IV: Special Cases
-- ============================================================

/-- **Equilateral triangle**: all sides equal (a = b = c = s).
    The angle bisector from A: t²·(2s)² = s·s·(4s²-s²)
    So t²·4s² = 3s⁴, i.e., t² = (3/4)s². This matches h = (√3/2)s. -/
theorem angle_bisector_equilateral (s t : ℝ) (hs : 0 < s)
    (h : t ^ 2 * (s + s) ^ 2 = s * s * ((s + s) ^ 2 - s ^ 2)) :
    t ^ 2 = 3 / 4 * s ^ 2 := by
  have hs_ne : s ≠ 0 := ne_of_gt hs
  nlinarith [sq_nonneg s, sq_nonneg t]

/-- **Numerical check**: 3-4-5 right triangle.
    For b = 4, c = 3, a = 5: t²·7² = 12·(49-25) = 12·24 = 288.
    So t² = 288/49. -/
theorem angle_bisector_3_4_5 (t : ℝ)
    (h : t ^ 2 * (3 + 4) ^ 2 = 3 * 4 * ((3 + 4) ^ 2 - (5 : ℝ) ^ 2)) :
    t ^ 2 = 288 / 49 := by
  nlinarith

/-- **Isoceles triangle** (b = c): the formula gives t²·(2b)² = b²·(4b²-a²),
    equivalently t² = b² - a²/4 (matching the altitude/median formula). -/
theorem angle_bisector_isoceles (a b t : ℝ) (ha : 0 < a) (hb : 0 < b)
    (h : t ^ 2 * (b + b) ^ 2 = b * b * ((b + b) ^ 2 - a ^ 2)) :
    t ^ 2 * 4 = 4 * b ^ 2 - a ^ 2 := by
  nlinarith [sq_nonneg b, sq_nonneg a, sq_nonneg t]

end AngleBisectorLength
