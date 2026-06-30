/-
  Young's inequality and its equality case.

  For Hölder-conjugate exponents `p, q > 1` (i.e. `p⁻¹ + q⁻¹ = 1`) and
  nonnegative reals `a, b`, Young's inequality states

      a * b ≤ a ^ p / p + b ^ q / q.

  This is the conjugate-exponent root of Hölder's inequality.  Mathlib provides
  the inequality itself (`Real.young_inequality_of_nonneg`), but **not** the
  characterisation of its equality case.  The headline result of this file is

      a * b = a ^ p / p + b ^ q / q  ↔  a ^ p = b ^ q       (for `a, b > 0`),

  the sharp boundary of Young's inequality.  The interesting direction follows
  from the *strict* convexity of `exp`: writing `a*b` and the right-hand side as
  the two endpoints of a `(p⁻¹, q⁻¹)`-weighted combination of `exp` evaluated at
  `log (a^p)` and `log (b^q)`, equality in the convex estimate forces the two
  arguments to coincide, i.e. `a^p = b^q`.

  We also record the classical specialisation `p = q = 2`, namely
  `2 * a * b ≤ a^2 + b^2` with equality iff `a = b`.

  All exponents are real, so `^` denotes `Real.rpow` throughout.

  Verified: 0 sorries, 0 axioms.
-/
import Mathlib

open Real

namespace AmgmInequalityOQ05

/-- **Young's inequality** (nonnegative form): for Hölder-conjugate exponents
`p, q` and `a, b ≥ 0`, `a * b ≤ a ^ p / p + b ^ q / q`. -/
theorem young_inequality {a b p q : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hpq : p.HolderConjugate q) :
    a * b ≤ a ^ p / p + b ^ q / q :=
  Real.young_inequality_of_nonneg ha hb hpq

/-- A convenient factorisation used in both directions of the equality case:
for `a, b > 0`, `a * b = (a ^ p) ^ p⁻¹ * (b ^ q) ^ q⁻¹`. -/
private theorem mul_eq_rpow_inv_mul_rpow_inv {a b p q : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hpq : p.HolderConjugate q) :
    a * b = (a ^ p) ^ p⁻¹ * (b ^ q) ^ q⁻¹ := by
  have hp : (0 : ℝ) < p := hpq.pos
  have hq : (0 : ℝ) < q := hpq.symm.pos
  have hPA : (a ^ p) ^ p⁻¹ = a := by
    rw [← Real.rpow_mul ha.le, mul_inv_cancel₀ hp.ne', Real.rpow_one]
  have hQB : (b ^ q) ^ q⁻¹ = b := by
    rw [← Real.rpow_mul hb.le, mul_inv_cancel₀ hq.ne', Real.rpow_one]
  rw [hPA, hQB]

/-- **Equality case of Young's inequality.**  For `a, b > 0` and Hölder-conjugate
exponents `p, q`, equality `a * b = a ^ p / p + b ^ q / q` holds **iff**
`a ^ p = b ^ q`.  The forward direction uses strict convexity of `exp`. -/
theorem young_inequality_eq_iff {a b p q : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hpq : p.HolderConjugate q) :
    a * b = a ^ p / p + b ^ q / q ↔ a ^ p = b ^ q := by
  have hp : (0 : ℝ) < p := hpq.pos
  have hq : (0 : ℝ) < q := hpq.symm.pos
  have hxp : 0 < a ^ p := Real.rpow_pos_of_pos ha p
  have hyq : 0 < b ^ q := Real.rpow_pos_of_pos hb q
  have hinv : p⁻¹ + q⁻¹ = 1 := hpq.inv_add_inv_eq_one
  have hab_eq : a * b = (a ^ p) ^ p⁻¹ * (b ^ q) ^ q⁻¹ :=
    mul_eq_rpow_inv_mul_rpow_inv ha hb hpq
  constructor
  · -- forward direction: equality forces `a^p = b^q`, via strict convexity of exp
    intro h
    by_contra hne
    -- `log` is injective on positives, so the two arguments differ
    have hlog : Real.log (a ^ p) ≠ Real.log (b ^ q) := by
      intro hc
      apply hne
      rw [← Real.exp_log hxp, ← Real.exp_log hyq, hc]
    have hstrict :=
      strictConvexOn_exp.2 (Set.mem_univ (Real.log (a ^ p)))
        (Set.mem_univ (Real.log (b ^ q))) hlog hpq.inv_pos hpq.symm.inv_pos hinv
    -- rewrite both sides of the strict estimate into closed form
    have hab_exp :
        a * b = Real.exp (p⁻¹ * Real.log (a ^ p) + q⁻¹ * Real.log (b ^ q)) := by
      rw [Real.exp_add, mul_comm p⁻¹ (Real.log (a ^ p)),
        mul_comm q⁻¹ (Real.log (b ^ q)), ← Real.rpow_def_of_pos hxp,
        ← Real.rpow_def_of_pos hyq, ← hab_eq]
    rw [smul_eq_mul, smul_eq_mul, smul_eq_mul, Real.exp_log hxp, Real.exp_log hyq,
      ← hab_exp, h] at hstrict
    -- `hstrict : a^p/p + b^q/q < p⁻¹ * a^p + q⁻¹ * b^q`, but the two sides are equal
    rw [div_eq_mul_inv, div_eq_mul_inv, mul_comm (a ^ p) p⁻¹,
      mul_comm (b ^ q) q⁻¹] at hstrict
    exact lt_irrefl _ hstrict
  · -- reverse direction: if `a^p = b^q` both sides equal that common value
    intro h
    have hL : a * b = b ^ q := by
      rw [hab_eq, h, ← Real.rpow_add hyq, hinv, Real.rpow_one]
    have hR : a ^ p / p + b ^ q / q = b ^ q := by
      rw [h, div_eq_mul_inv, div_eq_mul_inv, ← mul_add, hinv, mul_one]
    rw [hL, hR]

/-- The classical `p = q = 2` specialisation: `2 * a * b ≤ a ^ 2 + b ^ 2`
(here `^` is the natural-number power), with equality iff `a = b`. -/
theorem two_mul_le_sq_add_sq (a b : ℝ) :
    2 * a * b ≤ a ^ 2 + b ^ 2 ∧ (2 * a * b = a ^ 2 + b ^ 2 ↔ a = b) := by
  refine ⟨by nlinarith [sq_nonneg (a - b)], ?_, ?_⟩
  · intro h
    have : (a - b) ^ 2 = 0 := by nlinarith [h]
    have : a - b = 0 := by
      exact pow_eq_zero_iff (by norm_num) |>.mp this
    linarith
  · rintro rfl; ring

end AmgmInequalityOQ05
