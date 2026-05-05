import Mathlib

/-!
# Cauchy-Crofton Formula for Arbitrary Measures on Hyperplanes in ℝⁿ (OQ-03)

## What This Proves

This file formalizes the abstract **Cauchy-Crofton formula**, generalizing the
Buffon noodle theorem to any measure satisfying a single-segment calibration axiom.

The central result: for any measure μ satisfying the Cauchy-Crofton property,
the expected crossing count for a polygonal path P depends only on total arc length:

  E_μ[crossings(P)] = c_μ × length(P)

## Connection to Prior Work

- `BuffonsNeedle.lean`: 2D needle, P = 2ℓ/(πd) — kinematic constant c₂ = 2/π
- `BuffonsNeedleOQ02.lean`: 3D formula E = L/(2d) — kinematic constant c₃ = 1/2
- `BuffonsNeedleOQ02OQ01.lean`: n-dimensional crossing factor αₙ via recurrence
- `BuffonsNeedleOQ02OQ02.lean`: 3D smooth curve extension (axiomatized)
- **This file**: Abstract Cauchy-Crofton for polygonal paths, shape independence,
  and dimension comparisons for the kinematic crossing constants.

## Mathematical Background

The Cauchy-Crofton formula (Crofton 1868, Cauchy 1850) states: for a rectifiable
curve C in ℝⁿ and the kinematic measure on affine hyperplanes:

  E[#(C ∩ H)] = αₙ · length(C)

where αₙ = crossingFactor n is the n-dimensional crossing factor. The abstract
version derives from the single-segment formula by linearity of expectation.

## Novel Contributions

1. Abstract Cauchy-Crofton derived from single-segment linearity of expectation
2. Shape independence: two paths of equal length have equal expected crossings
3. Crossing constant values: c₂ = 2/π, c₃ = 1/2, c₄ = 4/(3π), c₅ = 3/8
4. Dimension comparison: cₙ strictly decreasing; higher dimensions are "sparser"
5. Additive decomposition: expected crossings additive under path concatenation
-/

namespace BuffonsNeedleOQ02OQ03

open Real MeasureTheory BigOperators

-- ============================================================
-- Part I: Geometric Definitions
-- ============================================================

/-- An affine hyperplane in ℝⁿ: pair (normal vector ν, offset c).
    The hyperplane is {x : ⟪x, ν⟫ = c}. -/
abbrev AffineHyperplane (n : ℕ) := EuclideanSpace ℝ (Fin n) × ℝ

/-- A line segment in ℝⁿ: a pair of endpoints. -/
abbrev LineSegment (n : ℕ) := EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)

/-- The Euclidean length of a line segment. -/
noncomputable def LineSegment.length (s : LineSegment n) : ℝ := dist s.1 s.2

/-- The crossing indicator of segment [p, q] with hyperplane (ν, c):
    equals 1 if the endpoints are on opposite sides (signed distance product < 0). -/
noncomputable def LineSegment.crossing (s : LineSegment n) (H : AffineHyperplane n) : ℝ :=
  if (⟪s.1, H.1⟫_ℝ - H.2) * (⟪s.2, H.1⟫_ℝ - H.2) < 0 then 1 else 0

theorem crossing_nonneg (s : LineSegment n) (H : AffineHyperplane n) :
    0 ≤ s.crossing H := by unfold LineSegment.crossing; split_ifs <;> norm_num

theorem crossing_le_one (s : LineSegment n) (H : AffineHyperplane n) :
    s.crossing H ≤ 1 := by unfold LineSegment.crossing; split_ifs <;> norm_num

-- ============================================================
-- Part II: The Kinematic Measure and Cauchy-Crofton Constant
-- ============================================================

/-- The n-dimensional Cauchy-Crofton constant αₙ.
    Defined by: α_{n+4} = ((n+2)/(n+3)) · α_{n+2}, with
    α₂ = 2/π  (2D Buffon, BuffonsNeedle.lean) and
    α₃ = 1/2  (3D Buffon, BuffonsNeedleOQ02.lean). -/
noncomputable def crossingFactor : ℕ → ℝ
  | 0 => 1
  | 1 => 1
  | 2 => 2 / π
  | 3 => 1 / 2
  | (n + 4) => ((n + 2 : ℝ) / (n + 3)) * crossingFactor (n + 2)

@[simp] lemma crossingFactor_zero  : crossingFactor 0 = 1     := rfl
@[simp] lemma crossingFactor_one   : crossingFactor 1 = 1     := rfl
@[simp] lemma crossingFactor_two   : crossingFactor 2 = 2 / π := rfl
@[simp] lemma crossingFactor_three : crossingFactor 3 = 1 / 2 := rfl
@[simp] lemma crossingFactor_rec (n : ℕ) :
    crossingFactor (n + 4) = ((n + 2 : ℝ) / (n + 3)) * crossingFactor (n + 2) := rfl

/-- The standard kinematic measure on AffineHyperplane n:
    the rotation- and translation-invariant measure on the space of affine hyperplanes. -/
axiom kinematicMeasure (n : ℕ) : Measure (AffineHyperplane n)

/-- Cauchy-Crofton axiom: the expected crossing count for a single segment equals
    α_n times the segment's length. Encodes rotation invariance of the kinematic
    measure: every segment of length L contributes αₙ · L expected crossings. -/
axiom cauchy_crofton_segment (n : ℕ) (s : LineSegment n) :
    ∫ H : AffineHyperplane n, s.crossing H ∂kinematicMeasure n =
    crossingFactor n * s.length

/-- Integrability: the crossing indicator is integrable with respect to the kinematic
    measure (bounded indicator + σ-finite measure). -/
axiom crossing_integrable (n : ℕ) (s : LineSegment n) :
    Integrable (fun H : AffineHyperplane n => s.crossing H) (kinematicMeasure n)

-- ============================================================
-- Part III: Polygonal Cauchy-Crofton Formula
-- ============================================================

/-- Total crossing count of a list of segments with a hyperplane H. -/
noncomputable def totalCrossings (n : ℕ) (segs : List (LineSegment n))
    (H : AffineHyperplane n) : ℝ :=
  (segs.map (fun s => s.crossing H)).sum

/-- Total length of a list of segments. -/
noncomputable def totalLength (n : ℕ) (segs : List (LineSegment n)) : ℝ :=
  (segs.map LineSegment.length).sum

@[simp] lemma totalCrossings_nil (n : ℕ) (H : AffineHyperplane n) :
    totalCrossings n [] H = 0 := by simp [totalCrossings]

@[simp] lemma totalCrossings_cons (n : ℕ) (s : LineSegment n)
    (rest : List (LineSegment n)) (H : AffineHyperplane n) :
    totalCrossings n (s :: rest) H = s.crossing H + totalCrossings n rest H := by
  simp [totalCrossings]

@[simp] lemma totalLength_nil (n : ℕ) : totalLength n [] = 0 := by simp [totalLength]

@[simp] lemma totalLength_cons (n : ℕ) (s : LineSegment n) (rest : List (LineSegment n)) :
    totalLength n (s :: rest) = s.length + totalLength n rest := by simp [totalLength]

/-- The total crossing count is integrable for any finite list of segments. -/
lemma integrable_totalCrossings (n : ℕ) (segs : List (LineSegment n)) :
    Integrable (totalCrossings n segs) (kinematicMeasure n) := by
  induction segs with
  | nil => simp only [totalCrossings_nil]; exact integrable_zero _ _ _
  | cons s rest ih =>
    simp_rw [totalCrossings_cons]
    exact (crossing_integrable n s).add ih

/-- **Main Theorem — Cauchy-Crofton Formula for Polygonal Paths**

    The expected crossing count for any polygonal path equals α_n × total arc length.

    Proof: induction on segments. Nil case trivial. Cons case: linearity of
    expectation (integral_add) decomposes the integral; the single-segment axiom
    and induction hypothesis complete the proof. -/
theorem cauchy_crofton_polygonal (n : ℕ) (segs : List (LineSegment n)) :
    ∫ H : AffineHyperplane n, totalCrossings n segs H ∂kinematicMeasure n =
    crossingFactor n * totalLength n segs := by
  induction segs with
  | nil => simp
  | cons s rest ih =>
    simp_rw [totalCrossings_cons]
    rw [integral_add (crossing_integrable n s) (integrable_totalCrossings n rest),
        cauchy_crofton_segment, ih, totalLength_cons, mul_add]

-- ============================================================
-- Part IV: Shape Independence and Key Consequences
-- ============================================================

/-- **Shape Independence**: Two polygonal paths with equal arc length have the
    same expected crossing count. The formula reads only arc length, not shape. -/
theorem crofton_shape_independence (n : ℕ) (P Q : List (LineSegment n))
    (hlen : totalLength n P = totalLength n Q) :
    ∫ H : AffineHyperplane n, totalCrossings n P H ∂kinematicMeasure n =
    ∫ H : AffineHyperplane n, totalCrossings n Q H ∂kinematicMeasure n := by
  rw [cauchy_crofton_polygonal, cauchy_crofton_polygonal, hlen]

/-- A zero-length path has zero expected crossings. -/
theorem crofton_zero_length (n : ℕ) (segs : List (LineSegment n))
    (h : totalLength n segs = 0) :
    ∫ H : AffineHyperplane n, totalCrossings n segs H ∂kinematicMeasure n = 0 := by
  rw [cauchy_crofton_polygonal, h, mul_zero]

/-- Single segment is a special case of the polygonal formula. -/
theorem crofton_singleton (n : ℕ) (s : LineSegment n) :
    ∫ H : AffineHyperplane n, totalCrossings n [s] H ∂kinematicMeasure n =
    crossingFactor n * s.length := by
  rw [cauchy_crofton_polygonal]; simp

/-- Two segments of equal length have equal expected crossings. -/
theorem crofton_equal_segments (n : ℕ) (s t : LineSegment n)
    (h : s.length = t.length) :
    ∫ H : AffineHyperplane n, s.crossing H ∂kinematicMeasure n =
    ∫ H : AffineHyperplane n, t.crossing H ∂kinematicMeasure n := by
  rw [cauchy_crofton_segment, cauchy_crofton_segment, h]

/-- **Path Decomposition**: Expected crossings is additive under path concatenation. -/
theorem crofton_append (n : ℕ) (P Q : List (LineSegment n)) :
    ∫ H : AffineHyperplane n, totalCrossings n (P ++ Q) H ∂kinematicMeasure n =
    (∫ H : AffineHyperplane n, totalCrossings n P H ∂kinematicMeasure n) +
    (∫ H : AffineHyperplane n, totalCrossings n Q H ∂kinematicMeasure n) := by
  rw [cauchy_crofton_polygonal, cauchy_crofton_polygonal, cauchy_crofton_polygonal]
  simp [totalLength, List.map_append, List.sum_append, mul_add]

-- ============================================================
-- Part V: Crossing Factor Values and Dimension Comparison
-- ============================================================

/-- α₄ = 4/(3π). -/
theorem crossingFactor_four : crossingFactor 4 = 4 / (3 * π) := by
  simp only [show (4 : ℕ) = 0 + 4 from rfl, crossingFactor_rec, crossingFactor_two]
  field_simp [pi_ne_zero]; ring

/-- α₅ = 3/8. -/
theorem crossingFactor_five : crossingFactor 5 = 3 / 8 := by
  simp only [show (5 : ℕ) = 1 + 4 from rfl, crossingFactor_rec, crossingFactor_three]; norm_num

/-- The crossing factor is strictly positive for n ≥ 2. -/
theorem crossingFactor_pos : ∀ n : ℕ, 2 ≤ n → 0 < crossingFactor n
  | 0, h => absurd h (by omega)
  | 1, h => absurd h (by omega)
  | 2, _ => by simp; exact div_pos two_pos pi_pos
  | 3, _ => by simp; norm_num
  | (n + 4), _ => by
      simp only [crossingFactor_rec]
      exact mul_pos (div_pos (by positivity) (by positivity))
                    (crossingFactor_pos (n + 2) (by omega))

/-- The **step-2 recurrence**: α_{n+2} = (n/(n+1)) · αₙ for n ≥ 1.
    Follows from the step-4 recurrence by reindexing; verified directly for n = 1. -/
lemma crossingFactor_step2 : ∀ n : ℕ, 1 ≤ n →
    crossingFactor (n + 2) = ((n : ℝ) / (n + 1)) * crossingFactor n
  | 0, h => absurd h (by omega)
  | 1, _ => by
      simp only [show (1 : ℕ) + 2 = 3 from rfl, crossingFactor_three, crossingFactor_one]
      norm_num
  | (k + 2), _ => by
      have h : k + 2 + 2 = k + 4 := by omega
      simp only [h, crossingFactor_rec]
      push_cast; ring

/-- **Step-2 dimension decrease**: α_{n+2} < α_n for n ≥ 1.
    The crossing factor strictly decreases every two dimensions. -/
theorem crossingFactor_succ_succ_lt (n : ℕ) (hn : 1 ≤ n) :
    crossingFactor (n + 2) < crossingFactor n := by
  rw [crossingFactor_step2 n hn]
  have hpos : 0 < crossingFactor n := by
    rcases Nat.lt_or_ge n 2 with h | h
    · -- n = 1 (since hn : 1 ≤ n and h : n < 2)
      have : n = 1 := by omega
      subst this; simp; norm_num
    · exact crossingFactor_pos n h
  have hlt : (n : ℝ) / (n + 1) < 1 :=
    div_lt_one_of_lt (by exact_mod_cast Nat.lt_succ_self n) (by positivity)
  linarith [mul_lt_mul_of_pos_right hlt hpos]

/-- **Dimension comparison 2D vs 3D**: α₂ = 2/π > 1/2 = α₃. -/
theorem crossingFactor_three_lt_two : crossingFactor 3 < crossingFactor 2 := by
  simp only [crossingFactor_two, crossingFactor_three]
  rw [div_lt_div_iff (by norm_num : (0:ℝ) < 2) pi_pos]
  linarith [pi_lt_four]

/-- **Dimension comparison 3D vs 4D**: α₃ = 1/2 > 4/(3π) = α₄.
    Proof: 1/2 > 4/(3π) ↔ 3π > 8, which holds since π > 3. -/
theorem crossingFactor_four_lt_three : crossingFactor 4 < crossingFactor 3 := by
  rw [crossingFactor_four, crossingFactor_three]
  rw [div_lt_div_iff (mul_pos (by norm_num : (0:ℝ) < 3) pi_pos) (by norm_num : (0:ℝ) < 2)]
  linarith [pi_gt_three]

/-- **Dimension comparison 4D vs 5D**: α₄ = 4/(3π) > 3/8 = α₅.
    Proof: 4/(3π) > 3/8 ↔ 32 > 9π, which holds since π < 3.15. -/
theorem crossingFactor_five_lt_four : crossingFactor 5 < crossingFactor 4 := by
  rw [crossingFactor_five, crossingFactor_four]
  rw [div_lt_div_iff (by norm_num : (0:ℝ) < 8) (mul_pos (by norm_num : (0:ℝ) < 3) pi_pos)]
  -- Need: 3 * (3 * π) < 4 * 8, i.e., 9π < 32. Since π < 3.15: 9 * 3.15 = 28.35 < 32.
  nlinarith [Real.pi_lt_315]

/-- **Information bound**: For paths of the same positive length, the 2D kinematic
    measure gives strictly more expected crossings than the 3D measure. -/
theorem kinematic_two_more_informative (L : ℝ) (hL : 0 < L)
    (segs2 : List (LineSegment 2)) (segs3 : List (LineSegment 3))
    (h2 : totalLength 2 segs2 = L) (h3 : totalLength 3 segs3 = L) :
    (∫ H : AffineHyperplane 3, totalCrossings 3 segs3 H ∂kinematicMeasure 3) <
    (∫ H : AffineHyperplane 2, totalCrossings 2 segs2 H ∂kinematicMeasure 2) := by
  rw [cauchy_crofton_polygonal, cauchy_crofton_polygonal, h2, h3]
  exact mul_lt_mul_of_pos_right crossingFactor_three_lt_two hL

end BuffonsNeedleOQ02OQ03
