/-
# Law of Cosines OQ-08: The Triangle Inequality as a Corollary of the Law of Cosines

The parent entry (`LawOfCosines`, Wiedijk #94) proves the law of cosines in both its
classical scalar form `c² = a² + b² - 2ab·cos C` and its inner-product form
`‖v - w‖² = ‖v‖² + ‖w‖² - 2⟨v, w⟩`.  One of its open questions asks to *derive the
triangle inequality directly from the law of cosines*, using only the elementary fact
that a cosine never drops below `-1`.

This file does exactly that.  The single analytic input is `cos C ≥ -1`
(`Real.neg_one_le_cos`):

* **Scalar form.**  If `c² = a² + b² - 2ab·cos C` with `a, b, c ≥ 0` and `cos C ≥ -1`,
  then `c ≤ a + b`.  The proof is one line of algebra:
  `(a + b)² - c² = 2ab·(1 + cos C) ≥ 0`, and squares of non-negatives are monotone.

* **Equality / degeneracy.**  For a genuine triangle (`a, b > 0`) equality `c = a + b`
  holds **iff** `cos C = -1`, i.e. iff the angle `C = π` and the triangle is degenerate
  (the three vertices are collinear with `C` between the other two).  When `cos C > -1`
  the inequality is strict, `c < a + b`.

* **Coordinate-free form.**  In *any* real inner-product space, the law of cosines in
  vector-angle form (`InnerProductGeometry.norm_sub_sq_…_cos_angle`) together with
  `cos ≥ -1` yields `‖x - y‖ ≤ ‖x‖ + ‖y‖`, with equality iff the angle between `x` and
  `y` is `π`.  This recovers Mathlib's `norm_sub_le` via the law of cosines, exhibiting
  the triangle inequality as a metric shadow of the cosine rule.

Everything is reduced to the scalar lemma `triangle_ineq_of_law_cosines`, which is the
mathematical heart of the result.  All proofs are fully machine-checked, with no `sorry`
and no axioms beyond Lean/Mathlib's foundations.

(The parent `Proofs.LawOfCosines` is referenced conceptually but not imported: this file
is self-contained and obtains the cosine-rule identity directly from Mathlib's
`InnerProductGeometry`, so it stays valid independently of the parent file's build state.)
-/
import Mathlib

namespace LawOfCosinesOQ08

open InnerProductGeometry Real
open scoped RealInnerProductSpace

/-! ### Monotonicity of squaring on the non-negative reals

Two small bridges between `x ≤ y` and `x² ≤ y²` for non-negative `x, y`, obtained by
taking square roots.  They turn the algebraic squared inequalities below into the genuine
distance inequalities. -/

/-- For non-negative reals, `c ≤ d` follows from `c² ≤ d²`. -/
theorem le_of_sq_le_sq {c d : ℝ} (hc : 0 ≤ c) (hd : 0 ≤ d) (h : c ^ 2 ≤ d ^ 2) : c ≤ d := by
  have := Real.sqrt_le_sqrt h
  rwa [Real.sqrt_sq hc, Real.sqrt_sq hd] at this

/-- For non-negative reals, `c < d` follows from `c² < d²`. -/
theorem lt_of_sq_lt_sq {c d : ℝ} (hc : 0 ≤ c) (hd : 0 ≤ d) (h : c ^ 2 < d ^ 2) : c < d := by
  have := Real.sqrt_lt_sqrt (sq_nonneg c) h
  rwa [Real.sqrt_sq hc, Real.sqrt_sq hd] at this

/-! ### Scalar form: the triangle inequality from the cosine rule -/

/-- **Triangle inequality from the law of cosines (scalar form).**
If the side `c` opposite the angle `C` satisfies the law of cosines
`c² = a² + b² - 2ab·cos C`, with `a, b, c ≥ 0` and the only trigonometric input
`cos C ≥ -1`, then `c ≤ a + b`.

The whole content is `(a + b)² - c² = 2ab·(1 + cos C) ≥ 0`. -/
theorem triangle_ineq_of_law_cosines {a b c cosC : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hcos : -1 ≤ cosC)
    (hlc : c ^ 2 = a ^ 2 + b ^ 2 - 2 * a * b * cosC) :
    c ≤ a + b := by
  have hsq : c ^ 2 ≤ (a + b) ^ 2 := by
    nlinarith [mul_nonneg (mul_nonneg ha hb) (by linarith : (0 : ℝ) ≤ 1 + cosC)]
  exact le_of_sq_le_sq hc (by linarith) hsq

/-- **Strict triangle inequality from the law of cosines.**
For a non-degenerate angle (`cos C > -1`) and positive adjacent sides, the inequality is
strict: `c < a + b`. -/
theorem triangle_ineq_strict_of_law_cosines {a b c cosC : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 ≤ c) (hcos : -1 < cosC)
    (hlc : c ^ 2 = a ^ 2 + b ^ 2 - 2 * a * b * cosC) :
    c < a + b := by
  have hsq : c ^ 2 < (a + b) ^ 2 := by
    nlinarith [mul_pos (mul_pos ha hb) (by linarith : (0 : ℝ) < 1 + cosC)]
  exact lt_of_sq_lt_sq hc (by positivity) hsq

/-- **Equality holds iff the triangle is degenerate.**
For positive adjacent sides `a, b > 0`, the triangle inequality is an equality `c = a + b`
exactly when `cos C = -1`, i.e. when the angle `C = π` and the configuration collapses to a
straight segment. -/
theorem degenerate_iff_eq {a b c cosC : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 ≤ c)
    (hlc : c ^ 2 = a ^ 2 + b ^ 2 - 2 * a * b * cosC) :
    c = a + b ↔ cosC = -1 := by
  constructor
  · intro h
    have hcsq : c ^ 2 = (a + b) ^ 2 := by rw [h]
    -- `2ab·(1 + cos C) = 0`, and `2ab ≠ 0`, so `cos C = -1`.
    have key : 2 * a * b * (1 + cosC) = 0 := by linear_combination hlc - hcsq
    have hab : 2 * a * b ≠ 0 := by positivity
    rcases mul_eq_zero.mp key with h1 | h1
    · exact absurd h1 hab
    · linarith
  · intro h
    have hcsq : c ^ 2 = (a + b) ^ 2 := by rw [hlc, h]; ring
    have h1 : c ≤ a + b := le_of_sq_le_sq hc (by positivity) hcsq.le
    have h2 : a + b ≤ c := le_of_sq_le_sq (by positivity) hc hcsq.ge
    linarith

/-! ### Coordinate-free form in a real inner-product space

Specialising the scalar lemmas to `a = ‖x‖`, `b = ‖y‖`, `c = ‖x - y‖`, and
`cos C = cos (angle x y)`, fed by Mathlib's vector-angle law of cosines. -/

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- **The triangle inequality, derived from the law of cosines.**
In any real inner-product space, `‖x - y‖ ≤ ‖x‖ + ‖y‖`.  The proof feeds the vector-angle
form of the law of cosines into `triangle_ineq_of_law_cosines`; the only analytic input is
`cos (angle x y) ≥ -1`.  (This re-proves Mathlib's `norm_sub_le` through the cosine rule.) -/
theorem norm_sub_le_of_law_cosines (x y : V) : ‖x - y‖ ≤ ‖x‖ + ‖y‖ := by
  have hlc : ‖x - y‖ ^ 2 = ‖x‖ ^ 2 + ‖y‖ ^ 2 - 2 * ‖x‖ * ‖y‖ * Real.cos (angle x y) := by
    simpa only [sq] using
      norm_sub_sq_eq_norm_sq_add_norm_sq_sub_two_mul_norm_mul_norm_mul_cos_angle x y
  exact triangle_ineq_of_law_cosines (norm_nonneg x) (norm_nonneg y) (norm_nonneg _)
    (Real.neg_one_le_cos _) hlc

/-- **Equality in the triangle inequality is a degenerate (collinear) angle.**
For non-zero vectors, `‖x - y‖ = ‖x‖ + ‖y‖` holds iff the angle between `x` and `y` equals
`π` (equivalently `cos (angle x y) = -1`): `x` and `y` point in opposite directions. -/
theorem norm_sub_eq_iff_cos_angle {x y : V} (hx : x ≠ 0) (hy : y ≠ 0) :
    ‖x - y‖ = ‖x‖ + ‖y‖ ↔ Real.cos (angle x y) = -1 := by
  have hlc : ‖x - y‖ ^ 2 = ‖x‖ ^ 2 + ‖y‖ ^ 2 - 2 * ‖x‖ * ‖y‖ * Real.cos (angle x y) := by
    simpa only [sq] using
      norm_sub_sq_eq_norm_sq_add_norm_sq_sub_two_mul_norm_mul_norm_mul_cos_angle x y
  exact degenerate_iff_eq (norm_pos_iff.mpr hx) (norm_pos_iff.mpr hy) (norm_nonneg _) hlc

/-! ### Concrete instance in the Euclidean plane

Specialising the coordinate-free statement to the Euclidean plane `EuclideanSpace ℝ (Fin 2)`
recovers the familiar planar triangle inequality (the setting `Vec2` of the parent entry),
now obtained purely through the law of cosines. -/

/-- The triangle inequality in the Euclidean plane, a direct instance of the
law-of-cosines derivation. -/
theorem triangle_inequality_euclidean (v w : EuclideanSpace ℝ (Fin 2)) :
    ‖v - w‖ ≤ ‖v‖ + ‖w‖ :=
  norm_sub_le_of_law_cosines v w

end LawOfCosinesOQ08
