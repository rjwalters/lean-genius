import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# The Triangle Inequality

## What This Proves
The Triangle Inequality is a fundamental result stating that for any triangle with sides a, b, c,
the length of any side is at most the sum of the other two. This is Wiedijk's 100 Theorems #91.

For real numbers:
$$|x + y| \leq |x| + |y|$$

For normed spaces:
$$\|x + y\| \leq \|x\| + \|y\|$$

For metric spaces with distance d:
$$d(x, z) \leq d(x, y) + d(y, z)$$

## Approach
- **Absolute Value Form:** Uses Mathlib's `abs_add` for real numbers.
- **Normed Space Form:** Uses Mathlib's `norm_add_le` for general normed spaces.
- **Metric Space Form:** Uses Mathlib's `dist_triangle` for metric spaces.
- **Reverse Triangle Inequality:** Proven as a corollary: ||a| - |b|| ≤ |a - b|.

## Status
- [x] Complete proof
- [x] Real number absolute value version
- [x] Normed space version
- [x] Metric space formulation
- [x] Reverse triangle inequality
- [x] Pedagogical examples
- [ ] Incomplete (has sorries)

## Mathlib Dependencies
- `abs_add` : |x + y| ≤ |x| + |y| for real/complex numbers
- `norm_add_le` : ‖x + y‖ ≤ ‖x‖ + ‖y‖ for normed spaces
- `dist_triangle` : dist x z ≤ dist x y + dist y z for metric spaces
- `abs_sub_abs_le_abs_sub` : | |x| - |y| | ≤ |x - y| (reverse triangle inequality)

## Historical Note
The triangle inequality is one of the most fundamental results in mathematics, appearing in
Euclid's Elements (Book I, Proposition 20). It states that the shortest path between two points
is a straight line, which is the geometric interpretation. The generalization to metric spaces
by Fréchet (1906) and normed spaces by Banach (1920s) laid the foundations for functional analysis.

## Geometric Intuition
In a triangle with vertices A, B, C:
- Going directly from A to C is shorter than going A → B → C
- This is because "the straight line is the shortest distance between two points"
- The inequality becomes equality when the points are collinear (degenerate triangle)

## Wiedijk's 100 Theorems: #91
-/

namespace TriangleInequality

/-! ## Absolute Value Form (Real Numbers)

The most elementary form of the triangle inequality for real numbers.
-/

/-- **Triangle Inequality for Real Numbers (Wiedijk #91)**

For any real numbers x and y:
  |x + y| ≤ |x| + |y|

This is the fundamental form of the inequality for ℝ. -/
theorem abs_triangle (x y : ℝ) : |x + y| ≤ |x| + |y| :=
  abs_add x y

/-! ## Reverse Triangle Inequality

The reverse triangle inequality provides a lower bound: the absolute value of
the difference of absolute values is bounded by the absolute value of the difference.
-/

/-- **Reverse Triangle Inequality**

For any real numbers x and y:
  | |x| - |y| | ≤ |x - y|

This follows from applying the triangle inequality twice. -/
theorem reverse_triangle (x y : ℝ) : abs (|x| - |y|) ≤ |x - y| :=
  abs_abs_sub_abs_le_abs_sub x y

/-- Reverse triangle inequality, alternate form: |x| - |y| ≤ |x - y| -/
theorem abs_sub_le_abs_diff (x y : ℝ) : |x| - |y| ≤ |x - y| :=
  (le_abs_self _).trans (reverse_triangle x y)

/-- The other direction: |y| - |x| ≤ |x - y| -/
theorem abs_sub_le_abs_diff' (x y : ℝ) : |y| - |x| ≤ |x - y| := by
  rw [abs_sub_comm]
  exact abs_sub_le_abs_diff y x

/-- Alternative statement using subtraction: |x - y| ≤ |x| + |y| -/
theorem abs_sub_triangle (x y : ℝ) : |x - y| ≤ |x| + |y| := by
  calc |x - y| = |x + (-y)| := by ring_nf
    _ ≤ |x| + |-y| := abs_add x (-y)
    _ = |x| + |y| := by rw [abs_neg]

/-! ## Normed Space Form

The triangle inequality for general normed vector spaces.
-/

/-- **Triangle Inequality for Normed Spaces**

For any elements x, y in a normed additive group:
  ‖x + y‖ ≤ ‖x‖ + ‖y‖

This generalizes the absolute value form to arbitrary normed spaces. -/
theorem norm_triangle {E : Type*} [SeminormedAddCommGroup E] (x y : E) :
    ‖x + y‖ ≤ ‖x‖ + ‖y‖ :=
  norm_add_le x y

/-- **Reverse Triangle Inequality for Normed Spaces**

For any elements x, y in a normed additive group:
  | ‖x‖ - ‖y‖ | ≤ ‖x - y‖ -/
theorem norm_reverse_triangle {E : Type*} [SeminormedAddCommGroup E] (x y : E) :
    abs (‖x‖ - ‖y‖) ≤ ‖x - y‖ :=
  abs_norm_sub_norm_le x y

/-- Triangle inequality for sums: ‖x + y + z‖ ≤ ‖x‖ + ‖y‖ + ‖z‖ -/
theorem norm_triangle_three {E : Type*} [SeminormedAddCommGroup E] (x y z : E) :
    ‖x + y + z‖ ≤ ‖x‖ + ‖y‖ + ‖z‖ := by
  calc ‖x + y + z‖ ≤ ‖x + y‖ + ‖z‖ := norm_add_le _ _
    _ ≤ ‖x‖ + ‖y‖ + ‖z‖ := by linarith [norm_add_le x y]

/-! ## Metric Space Form

The most general form, for arbitrary metric spaces.
-/

/-- **Triangle Inequality for Metric Spaces**

For any points x, y, z in a metric space:
  dist(x, z) ≤ dist(x, y) + dist(y, z)

This is the axiom that defines what it means to be a metric. -/
theorem dist_triangle_ineq {X : Type*} [PseudoMetricSpace X] (x y z : X) :
    dist x z ≤ dist x y + dist y z :=
  dist_triangle x y z

/-- Four-point triangle inequality: d(x, w) ≤ d(x, y) + d(y, z) + d(z, w) -/
theorem dist_triangle_four {X : Type*} [PseudoMetricSpace X] (x y z w : X) :
    dist x w ≤ dist x y + dist y z + dist z w := by
  calc dist x w ≤ dist x z + dist z w := dist_triangle x z w
    _ ≤ (dist x y + dist y z) + dist z w := by linarith [dist_triangle x y z]

/-- Reverse triangle inequality for metric spaces: |d(x,z) - d(y,z)| ≤ d(x,y) -/
theorem dist_reverse_triangle {X : Type*} [PseudoMetricSpace X] (x y z : X) :
    abs (dist x z - dist y z) ≤ dist x y :=
  abs_dist_sub_le x y z

/-! ## Geometric Interpretation

The triangle inequality has a beautiful geometric meaning: the direct path
between two points is never longer than any indirect path through a third point.
-/

/-- In a triangle with sides a, b, c, each side is at most the sum of the other two. -/
theorem triangle_sides (a b c : ℝ) (_ha : 0 ≤ a) (_hb : 0 ≤ b) (_hc : 0 ≤ c)
    (hab : a ≤ b + c) (hbc : b ≤ a + c) (hca : c ≤ a + b) :
    -- The triangle inequality is satisfied
    a ≤ b + c ∧ b ≤ a + c ∧ c ≤ a + b :=
  ⟨hab, hbc, hca⟩

/-- The strict triangle inequality: |x + y| < |x| + |y| when x and y have opposite signs
    and are both nonzero. -/
theorem strict_triangle (x y : ℝ) (hx : x ≠ 0) (hy : y ≠ 0) (h : x * y < 0) :
    |x + y| < |x| + |y| := by
  rcases (lt_or_gt_of_ne hx) with hx_neg | hx_pos
  · -- x < 0
    have hy_pos : 0 < y := by nlinarith
    rw [abs_of_neg hx_neg, abs_of_pos hy_pos]
    rcases lt_trichotomy (x + y) 0 with hsum_neg | hsum_zero | hsum_pos
    · rw [abs_of_neg hsum_neg]; linarith
    · rw [hsum_zero, abs_zero]; linarith [abs_pos.mpr hx, abs_pos.mpr hy]
    · rw [abs_of_pos hsum_pos]; linarith
  · -- x > 0
    have hy_neg : y < 0 := by nlinarith
    rw [abs_of_pos hx_pos, abs_of_neg hy_neg]
    rcases lt_trichotomy (x + y) 0 with hsum_neg | hsum_zero | hsum_pos
    · rw [abs_of_neg hsum_neg]; linarith
    · rw [hsum_zero, abs_zero]; linarith [abs_pos.mpr hx, abs_pos.mpr hy]
    · rw [abs_of_pos hsum_pos]; linarith

/-! ## Examples and Verification -/

/-- Example: |3 + 4| = 7 ≤ |3| + |4| = 7 (equality when same sign) -/
example : |3 + 4| ≤ |(3 : ℝ)| + |4| := by norm_num

/-- Example: |3 + (-5)| = 2 < |3| + |-5| = 8 (strict when opposite signs) -/
example : |3 + (-5)| < |(3 : ℝ)| + |-5| := by norm_num

/-- Example: |5 - 3| = 2 and | |5| - |3| | = 2, so equality in reverse triangle -/
example : abs (|(5 : ℝ)| - |3|) = |5 - 3| := by norm_num

/-! ## Applications -/

/-- **Continuity of Absolute Value**

The absolute value function is Lipschitz continuous with constant 1:
  | |x| - |y| | ≤ |x - y|

This is precisely the reverse triangle inequality. -/
theorem abs_lipschitz (x y : ℝ) : abs (|x| - |y|) ≤ |x - y| :=
  reverse_triangle x y

/-- **Norm is Continuous**

In a normed space, the norm function is Lipschitz continuous with constant 1. -/
theorem norm_lipschitz {E : Type*} [SeminormedAddCommGroup E] (x y : E) :
    abs (‖x‖ - ‖y‖) ≤ ‖x - y‖ :=
  norm_reverse_triangle x y

/-- **ε-δ Continuity of Norm**

For any ε > 0, if ‖x - y‖ < ε, then | ‖x‖ - ‖y‖ | < ε. -/
theorem norm_continuous_at {E : Type*} [SeminormedAddCommGroup E]
    (x y : E) (ε : ℝ) (_hε : 0 < ε) (h : ‖x - y‖ < ε) :
    abs (‖x‖ - ‖y‖) < ε :=
  (norm_lipschitz x y).trans_lt h

/-! ## Iterated Triangle Inequality -/

/-- Triangle inequality for finite sums: ‖∑ xᵢ‖ ≤ ∑ ‖xᵢ‖ -/
theorem norm_finset_sum_le {E : Type*} [SeminormedAddCommGroup E] {ι : Type*}
    (s : Finset ι) (f : ι → E) :
    ‖∑ i ∈ s, f i‖ ≤ ∑ i ∈ s, ‖f i‖ :=
  norm_sum_le s f

#check abs_triangle
#check reverse_triangle
#check norm_triangle
#check dist_triangle_ineq
#check strict_triangle

end TriangleInequality
