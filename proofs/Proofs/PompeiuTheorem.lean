import Mathlib

/-
# Pompeiu's Theorem (inequality form): the complex-number proof

## What This Proves
Pompeiu's theorem states that for an equilateral triangle `ABC` and any point `P`
in the plane, the three distances `PA`, `PB`, `PC` satisfy the triangle inequality
— i.e. they are the side lengths of a (possibly degenerate) triangle, called the
*Pompeiu triangle*. The triangle is degenerate exactly when `P` lies on the
circumcircle of `ABC`.

We give the classical complex-number proof of the inequality direction.

## Setup
Model the plane as `ℂ`. Fix a primitive cube root of unity `ω` (`ω² + ω + 1 = 0`).
An equilateral triangle with vertices `a, b, c : ℂ` of one orientation satisfies
the rotation identity
  `a + ω·b + ω²·c = 0`.
(This is one factor of the symmetric equilateral condition
`a² + b² + c² = ab + bc + ca = (a + ω b + ω² c)(a + ω² b + ω c)`.)
The hypotheses are non-vacuous: the cube roots of unity `(a,b,c) = (1, ω, ω²)`
with `ω = e^{2πi/3}` form a genuine equilateral triangle satisfying
`1 + ω·ω + ω²·ω² = 1 + ω² + ω⁴ = 1 + ω² + ω = 0`.

## Key idea
For any point `z` and the equilateral condition above,
  `(z - a) + ω·(z - b) + ω²·(z - c) = z·(1 + ω + ω²) − (a + ω b + ω² c) = 0`,
because both `1 + ω + ω² = 0` and `a + ω b + ω² c = 0`. Hence the three vectors
`z - a`, `ω(z - b)`, `ω²(z - c)` sum to zero, so they close up into a triangle.
Since `‖ω‖ = ‖ω²‖ = 1`, taking norms and applying the triangle inequality
`‖x + y‖ ≤ ‖x‖ + ‖y‖` yields `PA ≤ PB + PC`. Cyclically rotating the identity
(multiplying by `ω`, `ω²`) gives the other two inequalities.

## Status
- [x] `‖ω‖ = 1` derived from `ω² + ω + 1 = 0` (no extra hypothesis needed)
- [x] The structural identity `(z-a) + ω(z-b) + ω²(z-c) = 0`
- [x] All three Pompeiu inequalities (norm form and `dist` form)
- Complete — 0 sorries, 0 axioms

## Mathlib Dependencies
- `norm_mul`, `norm_pow` : multiplicativity of the norm on the normed field `ℂ`
- `norm_add_le` : triangle inequality for norms
- `norm_neg`, `norm_one`, `norm_nonneg`
- `dist_eq_norm`
-/

set_option linter.unusedVariables false

namespace PompeiuTheorem

-- ============================================================
-- PART 1: A primitive cube root of unity has norm one
-- ============================================================

/-- A root of `x² + x + 1` is a primitive cube root of unity, hence has norm `1`.
This frees the main theorem from carrying `‖ω‖ = 1` as a separate hypothesis. -/
theorem norm_eq_one_of_cube_root {ω : ℂ} (hω : ω ^ 2 + ω + 1 = 0) : ‖ω‖ = 1 := by
  have hcube : ω ^ 3 = 1 := by linear_combination (ω - 1) * hω
  have hn : ‖ω‖ ^ 3 = 1 := by rw [← norm_pow, hcube, norm_one]
  have hfac : (‖ω‖ - 1) * (‖ω‖ ^ 2 + ‖ω‖ + 1) = 0 := by linear_combination hn
  have hpos : 0 < ‖ω‖ ^ 2 + ‖ω‖ + 1 := by
    nlinarith [norm_nonneg ω, sq_nonneg ‖ω‖]
  rcases mul_eq_zero.mp hfac with h | h
  · linarith
  · linarith

-- ============================================================
-- PART 2: The rotation lemma
-- ============================================================

/-- If three complex numbers `u, v, w` satisfy `u + ω·v + ω²·w = 0` with `‖ω‖ = 1`,
then `‖u‖ ≤ ‖v‖ + ‖w‖`. This is the engine of Pompeiu's inequality: each Pompeiu
distance is bounded by the sum of the other two. -/
theorem norm_le_of_rot {ω u v w : ℂ} (hnorm : ‖ω‖ = 1)
    (h : u + ω * v + ω ^ 2 * w = 0) : ‖u‖ ≤ ‖v‖ + ‖w‖ := by
  have hu : u = -(ω * v + ω ^ 2 * w) := by linear_combination h
  have hω2 : ‖ω ^ 2‖ = 1 := by rw [norm_pow, hnorm, one_pow]
  calc ‖u‖ = ‖ω * v + ω ^ 2 * w‖ := by rw [hu, norm_neg]
    _ ≤ ‖ω * v‖ + ‖ω ^ 2 * w‖ := norm_add_le _ _
    _ = ‖v‖ + ‖w‖ := by rw [norm_mul, norm_mul, hnorm, hω2, one_mul, one_mul]

-- ============================================================
-- PART 3: The structural identity
-- ============================================================

/-- The structural identity at the heart of Pompeiu's theorem: for an equilateral
triangle `a + ω b + ω² c = 0` and any point `z`, the displacement vectors close up:
`(z - a) + ω·(z - b) + ω²·(z - c) = 0`. -/
theorem rotation_identity {ω a b c z : ℂ} (hω : ω ^ 2 + ω + 1 = 0)
    (heq : a + ω * b + ω ^ 2 * c = 0) :
    (z - a) + ω * (z - b) + ω ^ 2 * (z - c) = 0 := by
  linear_combination z * hω - heq

-- ============================================================
-- PART 4: Pompeiu's inequality (norm form)
-- ============================================================

/-- **Pompeiu's theorem (inequality form).**

For an equilateral triangle with vertices `a, b, c` (encoded by the rotation
identity `a + ω b + ω² c = 0`, where `ω² + ω + 1 = 0`) and any point `z`, the three
distances `‖z - a‖`, `‖z - b‖`, `‖z - c‖` satisfy all three triangle inequalities.
In other words they are the side lengths of a (possibly degenerate) triangle. -/
theorem pompeiu_norm {ω a b c z : ℂ} (hω : ω ^ 2 + ω + 1 = 0)
    (heq : a + ω * b + ω ^ 2 * c = 0) :
    ‖z - a‖ ≤ ‖z - b‖ + ‖z - c‖ ∧
    ‖z - b‖ ≤ ‖z - c‖ + ‖z - a‖ ∧
    ‖z - c‖ ≤ ‖z - a‖ + ‖z - b‖ := by
  have hnorm : ‖ω‖ = 1 := norm_eq_one_of_cube_root hω
  have hcube : ω ^ 3 = 1 := by linear_combination (ω - 1) * hω
  refine ⟨?_, ?_, ?_⟩
  · -- ‖z-a‖ ≤ ‖z-b‖ + ‖z-c‖  from  (z-a) + ω(z-b) + ω²(z-c) = 0
    exact norm_le_of_rot hnorm (by linear_combination z * hω - heq)
  · -- ‖z-b‖ ≤ ‖z-c‖ + ‖z-a‖  from  (z-b) + ω(z-c) + ω²(z-a) = 0
    exact norm_le_of_rot hnorm
      (by linear_combination z * hω - ω ^ 2 * heq + (b + c * ω) * hcube)
  · -- ‖z-c‖ ≤ ‖z-a‖ + ‖z-b‖  from  (z-c) + ω(z-a) + ω²(z-b) = 0
    exact norm_le_of_rot hnorm (by linear_combination z * hω - ω * heq + c * hcube)

-- ============================================================
-- PART 5: Pompeiu's inequality (distance form)
-- ============================================================

/-- Pompeiu's theorem stated with the metric `dist`, matching the classical
geometric phrasing `PA ≤ PB + PC` (and cyclically). -/
theorem pompeiu_dist {ω a b c z : ℂ} (hω : ω ^ 2 + ω + 1 = 0)
    (heq : a + ω * b + ω ^ 2 * c = 0) :
    dist z a ≤ dist z b + dist z c ∧
    dist z b ≤ dist z c + dist z a ∧
    dist z c ≤ dist z a + dist z b := by
  simpa only [dist_eq_norm] using pompeiu_norm (ω := ω) (z := z) hω heq

end PompeiuTheorem
