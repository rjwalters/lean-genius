/-
  Newton's Inequality, First Rung (n = 3): S₂² ≥ S₁S₃

  Open Question (amgm-inequality-oq-02-oq-01-oq-05-oq-01):
  Prove the next Maclaurin/Newton rung after the base step S₁² ≥ S₂, namely
    S₂² ≥ S₁ S₃      (Newton's inequality at k = 2),
  the log-concavity of the elementary symmetric means.  This is the first rung
  that requires *genuinely more* than Cauchy–Schwarz.

  Here we resolve the concrete, self-contained case n = 3.  For reals a, b, c set
    e₁ = a + b + c,
    e₂ = ab + bc + ca,
    e₃ = abc,
  and the symmetric means
    S₁ = e₁ / C(3,1) = e₁ / 3,
    S₂ = e₂ / C(3,2) = e₂ / 3,
    S₃ = e₃ / C(3,3) = e₃ / 1 = e₃.
  Then S₂² ≥ S₁ S₃, equivalently (clearing the constant denominators) the
  cleared form
    e₂² ≥ 3 · e₁ · e₃.

  Key insight (why this is beyond Cauchy–Schwarz).
  The base rung S₁² ≥ S₂ collapses to the power-mean bound n·p₂ ≥ e₁² and carries
  no content beyond Cauchy–Schwarz.  The k = 2 rung instead rests on an explicit
  sum-of-squares certificate:

    e₂² − 3·e₁·e₃ = ½·[ (ab − bc)² + (bc − ca)² + (ca − ab)² ]  ≥  0.

  This certificate holds for ALL reals a, b, c — no nonnegativity is needed —
  because Newton's inequalities are sign-agnostic (the nonnegativity hypothesis
  of the Maclaurin chain only becomes essential at rungs where one extracts real
  roots).  Equality holds iff ab = bc = ca, i.e. (for nonzero variables) a = b = c.

  General n (documented; proved here only for n = 3).
  The general k = 2 Newton inequality, cleared of the binomial denominators, reads
    2(n − 2)·e₂² ≥ 3(n − 1)·e₁·e₃,
  which reduces to the above at n = 3.  Its general proof goes through Rolle's
  theorem on the real-rooted polynomial ∏(x − xᵢ) and its derivatives (the
  discriminant of a real-rooted quadratic is nonnegative); formalizing that is the
  forward open question.  The n = 3 case below needs none of that machinery.
-/
import Mathlib

namespace AmgmInequalityOQ02OQ01OQ05OQ01

variable (a b c : ℝ)

/-- First elementary symmetric polynomial e₁ = a + b + c. -/
def e1 : ℝ := a + b + c

/-- Second elementary symmetric polynomial e₂ = ab + bc + ca. -/
def e2 : ℝ := a * b + b * c + c * a

/-- Third elementary symmetric polynomial e₃ = abc. -/
def e3 : ℝ := a * b * c

-- ============================================================
-- The sum-of-squares certificate
-- ============================================================

/-- **Newton SOS identity (n = 3).**  The Newton defect `e₂² − 3 e₁ e₃` is exactly
    half the sum of the squared pairwise differences of the products `ab, bc, ca`:

      e₂² − 3 e₁ e₃ = ½[(ab − bc)² + (bc − ca)² + (ca − ab)²].

    A pure ring identity — it is the engine behind the inequality. -/
theorem newton_sos_identity :
    (e2 a b c) ^ 2 - 3 * (e1 a b c) * (e3 a b c)
      = ((a * b - b * c) ^ 2 + (b * c - c * a) ^ 2 + (c * a - a * b) ^ 2) / 2 := by
  simp only [e1, e2, e3]
  ring

-- ============================================================
-- Newton's inequality, cleared form: e₂² ≥ 3 e₁ e₃
-- ============================================================

/-- **Newton's inequality at k = 2, cleared form (n = 3).**
    For all reals `a, b, c`:  `e₂² ≥ 3 · e₁ · e₃`.
    No nonnegativity hypothesis is required — the inequality is sign-agnostic. -/
theorem newton_cleared :
    (e2 a b c) ^ 2 ≥ 3 * (e1 a b c) * (e3 a b c) := by
  have hsos := newton_sos_identity a b c
  nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a),
             sq_nonneg (c * a - a * b), hsos]

-- ============================================================
-- Newton's inequality, averaged (symmetric-means) form: S₂² ≥ S₁ S₃
-- ============================================================

/-- **Newton's inequality at k = 2, averaged form (n = 3).**
    With the symmetric means `S₁ = e₁/3`, `S₂ = e₂/3`, `S₃ = e₃/1`, we have
    `S₂² ≥ S₁ · S₃`.  The constant denominators need no positivity side-conditions,
    so this holds for all reals. -/
theorem newton_base_step :
    ((e2 a b c) / 3) ^ 2 ≥ ((e1 a b c) / 3) * ((e3 a b c) / 1) := by
  have h := newton_cleared a b c
  -- reduce the averaged defect to the cleared defect divided by the positive constant 9
  have key : ((e2 a b c) / 3) ^ 2 - ((e1 a b c) / 3) * ((e3 a b c) / 1)
      = ((e2 a b c) ^ 2 - 3 * (e1 a b c) * (e3 a b c)) / 9 := by ring
  have hnn : (0 : ℝ) ≤ ((e2 a b c) ^ 2 - 3 * (e1 a b c) * (e3 a b c)) / 9 := by
    apply div_nonneg
    · linarith [h]
    · norm_num
  rw [ge_iff_le]
  linarith [key, hnn]

-- ============================================================
-- Equality case
-- ============================================================

/-- **Equality direction (n = 3).**  If `a = b = c` then Newton's inequality is an
    equality: `e₂² = 3 e₁ e₃`.  (The SOS certificate vanishes since all three
    products `ab, bc, ca` coincide.) -/
theorem newton_eq_of_all_eq (h : a = b ∧ b = c) :
    (e2 a b c) ^ 2 = 3 * (e1 a b c) * (e3 a b c) := by
  obtain ⟨hab, hbc⟩ := h
  subst hab; subst hbc
  simp only [e1, e2, e3]
  ring

/-- **Equality forces the pairwise products to agree (n = 3).**  If Newton's
    inequality is an equality, `e₂² = 3 e₁ e₃`, then the SOS certificate vanishes,
    i.e. the three products `ab, bc, ca` all coincide.  Together with
    `newton_eq_of_all_eq` this characterizes the equality locus. -/
theorem newton_products_eq_of_eq
    (h : (e2 a b c) ^ 2 = 3 * (e1 a b c) * (e3 a b c)) :
    a * b = b * c ∧ b * c = c * a := by
  have hid := newton_sos_identity a b c
  have hzero : (e2 a b c) ^ 2 - 3 * (e1 a b c) * (e3 a b c) = 0 := by linarith [h]
  rw [hid] at hzero
  have hsum : (a * b - b * c) ^ 2 + (b * c - c * a) ^ 2 + (c * a - a * b) ^ 2 = 0 := by
    linarith [hzero]
  have n1 := sq_nonneg (a * b - b * c)
  have n2 := sq_nonneg (b * c - c * a)
  have n3 := sq_nonneg (c * a - a * b)
  have h1 : (a * b - b * c) ^ 2 = 0 := by linarith
  have h2 : (b * c - c * a) ^ 2 = 0 := by linarith
  have z1 : a * b - b * c = 0 := pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0) |>.mp h1
  have z2 : b * c - c * a = 0 := pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0) |>.mp h2
  exact ⟨by linarith [z1], by linarith [z2]⟩

end AmgmInequalityOQ02OQ01OQ05OQ01
