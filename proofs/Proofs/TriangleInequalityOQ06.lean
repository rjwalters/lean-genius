import Mathlib

/-
# The reverse triangle inequality family and 1-Lipschitz distance

The parent `triangle-inequality` proves the *forward* inequality
`d(x, z) ≤ d(x, y) + d(y, z)`.  This child collects its *reverse* companions into one
coherent verified narrative and — crucially — proves that the collected bounds are
**sharp**, which the parent lemmas alone do not record.

The bundle:

* **reverse (second) triangle inequality** `|d(x,z) - d(y,z)| ≤ d(x,y)`
  — the distance to a fixed point changes by at most the step you take;
* its **quadrilateral** strengthening `|d(x,y) - d(x',y')| ≤ d(x,x') + d(y,y')`
  — moving *both* endpoints;
* the **seminorm** version `| ‖a‖ - ‖b‖ | ≤ ‖a - b‖`;
* the consequence that `d(x, ·)` (and `d(·, y)`) is `1`-Lipschitz, hence uniformly
  continuous and continuous.

The atomic inequalities discharge by the Mathlib lemmas `abs_dist_sub_le`,
`dist_dist_dist_le`, `abs_norm_sub_norm_le`, `LipschitzWith.dist_right/left`.  The
genuinely new content of this file is the **sharpness layer**:

* `reverse_triangle_eq_of_between` : for collinear reals `a ≤ b ≤ c` the reverse
  inequality is an *equality* `|d(a,c) - d(b,c)| = d(a,b)` — so the bound `≤ d(x,y)` is
  attained and cannot be improved;
* `quadrilateral_sharp` : an explicit real configuration attaining the quadrilateral
  bound with both endpoints moved;
* `dist_lipschitz_optimal` : the Lipschitz constant `1` is *optimal* — no `c < 1`
  makes `dist x` a `c`-Lipschitz map.

Everything is `0`-axiom.  This is distinct from the strict-convexity equality case
(gallery `triangle-inequality-oq-05`), which characterises equality in the *forward*
`‖x + y‖ = ‖x‖ + ‖y‖`; here we treat the *reverse* family and its attainment.
-/

namespace TriangleInequalityOQ06

open scoped NNReal

/-! ## The reverse triangle inequality family (pseudometric spaces) -/

variable {α : Type*} [PseudoMetricSpace α]

/-- Reverse (second) triangle inequality: the distance to a fixed point `z` changes by
at most the distance between the two moving points. -/
theorem reverse_triangle (x y z : α) : |dist x z - dist y z| ≤ dist x y :=
  abs_dist_sub_le x y z

/-- One-sided form (without the absolute value). -/
theorem dist_sub_dist_le (x y z : α) : dist x z - dist y z ≤ dist x y :=
  (abs_le.1 (abs_dist_sub_le x y z)).2

/-- Quadrilateral reverse inequality: move *both* endpoints.  On `ℝ`,
`dist (dist x y) (dist x' y')` unfolds to `|dist x y - dist x' y'|`. -/
theorem reverse_triangle_quad (x y x' y' : α) :
    |dist x y - dist x' y'| ≤ dist x x' + dist y y' := by
  simpa [Real.dist_eq] using dist_dist_dist_le x y x' y'

/-! ## The 1-Lipschitz / continuity package -/

/-- The distance from a fixed left point is `1`-Lipschitz in its right argument. -/
theorem dist_lipschitz_right (x : α) : LipschitzWith 1 (dist x) :=
  LipschitzWith.dist_right x

/-- The distance to a fixed right point is `1`-Lipschitz in its left argument. -/
theorem dist_lipschitz_left (y : α) : LipschitzWith 1 (fun x => dist x y) :=
  LipschitzWith.dist_left y

/-- Consequently `d(x, ·)` is uniformly continuous. -/
theorem dist_uniformContinuous_right (x : α) : UniformContinuous (dist x) :=
  (dist_lipschitz_right x).uniformContinuous

/-- … and continuous. -/
theorem dist_continuous_right (x : α) : Continuous (dist x) :=
  (dist_lipschitz_right x).continuous

/-! ## The seminorm reverse triangle inequality -/

/-- Norm reverse triangle inequality. -/
theorem reverse_triangle_norm {E : Type*} [SeminormedAddGroup E] (a b : E) :
    |‖a‖ - ‖b‖| ≤ ‖a - b‖ :=
  abs_norm_sub_norm_le a b

/-- One-sided seminorm form. -/
theorem norm_sub_norm_le' {E : Type*} [SeminormedAddGroup E] (a b : E) :
    ‖a‖ - ‖b‖ ≤ ‖a - b‖ :=
  norm_sub_norm_le a b

/-! ## Sharpness layer — the new content

The bundle above only re-packages Mathlib lemmas.  The results below certify that the
inequalities are *tight*: each bound is attained, so no constant can be improved.
-/

/-- **Sharpness of the reverse inequality.**  For collinear reals `a ≤ b ≤ c` the reverse
triangle inequality holds with *equality*: `|d(a,c) - d(b,c)| = d(a,b)`.  In particular
the bound `|d(x,z) - d(y,z)| ≤ d(x,y)` is attained, hence optimal. -/
theorem reverse_triangle_eq_of_between {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c) :
    |dist a c - dist b c| = dist a b := by
  have hac : a ≤ c := le_trans hab hbc
  rw [Real.dist_eq, Real.dist_eq, Real.dist_eq,
    abs_of_nonpos (by linarith : a - c ≤ 0),
    abs_of_nonpos (by linarith : b - c ≤ 0),
    abs_of_nonpos (by linarith : a - b ≤ 0)]
  rw [show -(a - c) - -(b - c) = -(a - b) by ring, abs_neg, abs_of_nonpos (by linarith : a - b ≤ 0)]

/-- Concrete witness of the reverse-inequality equality: `|d(0,2) - d(1,2)| = d(0,1) = 1`. -/
example : |dist (0 : ℝ) 2 - dist (1 : ℝ) 2| = dist (0 : ℝ) 1 :=
  reverse_triangle_eq_of_between (by norm_num) (by norm_num)

/-- **Sharpness of the quadrilateral inequality.**  Moving the two endpoints of a
degenerate pair in opposite directions attains the bound:
`|d(0,0) - d(-1,1)| = 2 = d(0,-1) + d(0,1)`. -/
theorem quadrilateral_sharp :
    |dist (0 : ℝ) 0 - dist (-1 : ℝ) 1| = dist (0 : ℝ) (-1) + dist (0 : ℝ) 1 := by
  simp [Real.dist_eq]
  norm_num

/-- **Optimality of the Lipschitz constant.**  No constant `c < 1` makes `dist x`
Lipschitz: testing the two points `0` and `1` forces `1 ≤ c`.  Hence the `1` in
`dist_lipschitz_right` is best possible. -/
theorem dist_lipschitz_optimal {c : ℝ≥0} (h : LipschitzWith c (dist (0 : ℝ))) : 1 ≤ c := by
  have key := h.dist_le_mul 0 1
  simp only [Real.dist_eq] at key
  norm_num at key
  exact_mod_cast key

/-! ## Worked real-line examples -/

/-- The reverse inequality on `ℝ` in its familiar absolute-value shape. -/
example (x y : ℝ) : |(|x| - |y|)| ≤ |x - y| := by
  simpa [Real.norm_eq_abs] using reverse_triangle_norm x y

/-- The metric on `ℝ` is continuous in each argument. -/
example (x : ℝ) : Continuous (fun y => dist x y) := dist_continuous_right x

end TriangleInequalityOQ06
