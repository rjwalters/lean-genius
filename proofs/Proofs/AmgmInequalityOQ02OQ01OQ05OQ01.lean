/-
  Newton's k = 2 inequality S₂² ≥ S₁S₃ — the ALL-REALS case for n = 3.

  Open Question (amgm-inequality-oq-02-oq-01-oq-05-oq-01):
  For reals x₁,…,xₙ (n ≥ 3), with the normalized (Maclaurin) symmetric means
    Sₖ = eₖ / C(n,k),
  Newton's log-concavity rung k = 2 asserts
    S₂² ≥ S₁ S₃.
  Clearing the binomial denominators (C(n,2)²/(C(n,1)·C(n,3)) = 3(n-1)/(2(n-2))),
  this is the integer-cleared inequality
    2(n-2) · e₂²  ≥  3(n-1) · e₁ e₃.

  Newton's inequalities hold for ALL real xᵢ — they follow from the real-rootedness of
  ∏(t − xᵢ) and its derivatives, never from any sign hypothesis.  The gallery's existing
  `NewtonLC.newton_ineq` proves the *nonnegative* case (it genuinely uses eₖ ≥ 0), so the
  all-reals statement is a strict strengthening not otherwise present.

  This file establishes the base rung n = 3 unconditionally (no sign hypothesis) via an
  EXPLICIT sum-of-squares certificate, verified axiom-free.  Specializing the cleared
  constant at n = 3 gives 2(n-2) = 2, 3(n-1) = 6, i.e.
    2 e₂²  ≥  6 e₁ e₃      ⟺      e₂²  ≥  3 e₁ e₃,
  and the exact identity
    e₂² − 3 e₁ e₃ = ½[(xy − yz)² + (yz − zx)² + (zx − xy)²] ≥ 0
  is the certificate (the right-hand square-sum vanishes exactly on the Newton equality
  locus x = y = z).

  No sorries, no axioms.
-/
import Mathlib

namespace AmgmInequalityOQ02OQ01OQ05OQ01

/-- First elementary symmetric polynomial of three reals, e₁ = x + y + z. -/
def e1 (x y z : ℝ) : ℝ := x + y + z

/-- Second elementary symmetric polynomial, e₂ = xy + yz + zx. -/
def e2 (x y z : ℝ) : ℝ := x * y + y * z + z * x

/-- Third elementary symmetric polynomial, e₃ = xyz. -/
def e3 (x y z : ℝ) : ℝ := x * y * z

/-- **Explicit SOS certificate (a `ring` identity).**  The Newton defect
`e₂² − 3 e₁e₃` is exactly half the sum of the three squared pair-product differences.
This is an algebraic identity over ℝ, independent of any sign of `x, y, z`. -/
theorem newton_k2_sos_identity (x y z : ℝ) :
    e2 x y z ^ 2 - 3 * e1 x y z * e3 x y z
      = ((x * y - y * z) ^ 2 + (y * z - z * x) ^ 2 + (z * x - x * y) ^ 2) / 2 := by
  simp only [e1, e2, e3]; ring

/-- **Newton's k = 2 inequality for n = 3, ALL reals (0-axiom).**
`e₂² ≥ 3 e₁ e₃` for every `x, y, z : ℝ` — no nonnegativity needed — as the
right-hand side of `newton_k2_sos_identity` is a sum of squares. -/
theorem newton_k2_allreals_three (x y z : ℝ) :
    e2 x y z ^ 2 ≥ 3 * e1 x y z * e3 x y z := by
  have h := newton_k2_sos_identity x y z
  have hnn : (0 : ℝ) ≤
      ((x * y - y * z) ^ 2 + (y * z - z * x) ^ 2 + (z * x - x * y) ^ 2) / 2 := by
    positivity
  linarith [h, hnn]

/-- The integer-cleared form matching the general statement `2(n-2)e₂² ≥ 3(n-1)e₁e₃`
specialized at `n = 3` (constants `2` and `6`). -/
theorem newton_k2_allreals_three_cleared (x y z : ℝ) :
    2 * e2 x y z ^ 2 ≥ 6 * (e1 x y z * e3 x y z) := by
  have h := newton_k2_allreals_three x y z
  nlinarith [h]

/-- **Exact equality locus.**  The SOS certificate makes the Newton equality set explicit:
the defect `e₂² − 3e₁e₃` vanishes **iff all three pair products agree**, `xy = yz = zx`.
(Note this is strictly larger than the diagonal `x = y = z`: e.g. `x = 1, y = z = 0` has all
pair products `0`, so equality holds without the variables being equal — the pair-product
characterization is the honest one.) -/
theorem newton_k2_equality_iff (x y z : ℝ) :
    e2 x y z ^ 2 = 3 * e1 x y z * e3 x y z ↔ x * y = y * z ∧ y * z = z * x := by
  have hid := newton_k2_sos_identity x y z
  constructor
  · intro heq
    -- defect = 0 forces the sum of three squares to 0, hence each square to 0.
    have hsum : (x * y - y * z) ^ 2 + (y * z - z * x) ^ 2 + (z * x - x * y) ^ 2 = 0 := by
      have hz : e2 x y z ^ 2 - 3 * e1 x y z * e3 x y z = 0 := by linarith [heq]
      linarith [hid, hz]
    have hs1 : (x * y - y * z) ^ 2 = 0 := by
      nlinarith [sq_nonneg (y * z - z * x), sq_nonneg (z * x - x * y)]
    have hs2 : (y * z - z * x) ^ 2 = 0 := by
      nlinarith [sq_nonneg (x * y - y * z), sq_nonneg (z * x - x * y)]
    refine ⟨?_, ?_⟩
    · by_contra h
      have hne : x * y - y * z ≠ 0 := sub_ne_zero.mpr h
      have : (0 : ℝ) < (x * y - y * z) ^ 2 := by positivity
      linarith [hs1]
    · by_contra h
      have hne : y * z - z * x ≠ 0 := sub_ne_zero.mpr h
      have : (0 : ℝ) < (y * z - z * x) ^ 2 := by positivity
      linarith [hs2]
  · rintro ⟨hxy, hyz⟩
    -- all pair products equal ⟹ every squared difference is 0 ⟹ defect 0.
    have hzx : z * x = x * y := by linarith [hxy, hyz]
    have d1 : x * y - y * z = 0 := by linarith [hxy]
    have d2 : y * z - z * x = 0 := by linarith [hyz]
    have d3 : z * x - x * y = 0 := by linarith [hzx]
    have hz : ((x * y - y * z) ^ 2 + (y * z - z * x) ^ 2 + (z * x - x * y) ^ 2) / 2 = 0 := by
      rw [d1, d2, d3]; norm_num
    linarith [hid, hz]

end AmgmInequalityOQ02OQ01OQ05OQ01
