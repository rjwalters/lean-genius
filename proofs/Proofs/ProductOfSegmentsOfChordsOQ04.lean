import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic

/-!
# Radical Axis and Radical Center (OQ-04)

This file answers `product-of-segments-of-chords-oq-04`:

> "What is the connection [of the power of a point] to algebraic geometry: the
> power function defines a quadratic form, and the radical axis is the linear
> locus where two quadratic forms agree?"

The **power of a point** `P` with respect to a circle/sphere of centre `O` and
radius `r` is `pow(P) = ‖P − O‖² − r²` (the signed quantity from the parent
*Product of Segments of Chords* entry, generalised to any dimension).

Although `pow` is a *quadratic* function of `P`, the **difference** of the power
functions of two circles is **affine-linear** — the purely quadratic term
`‖P‖²` cancels. Consequently the locus where two circles have equal power (the
**radical axis**) is a hyperplane, and it is **perpendicular to the line of
centres**. For three circles with non-collinear centres the three radical axes
meet in a single point, the **radical centre**.

## Main results

* `power_expand` — the quadratic-form expansion `pow(P) = ‖P‖² − 2⟪P,O⟫ + ‖O‖² − r²`.
* `radical_axis_linear` — equal power ⇔ a single affine-linear equation in `P`
  (the radical-axis equation). This is the precise statement that the radical
  axis is "the linear locus where two quadratic forms agree".
* `radical_axis_perp` — the radical axis is orthogonal to the line of centres.
* `radical_axis_affine` — the radical axis is closed under taking the line
  through any two of its points (it is an affine subspace).
* `equal_power_linear` — coordinate form of `radical_axis_linear` in `ℝ²`.
* `radical_center_unique` / `radical_center_exists` / `radical_center_existsUnique`
  — three circles with non-collinear centres have a **unique** radical centre.

All results are dimension-independent except the radical-centre statements,
which are specific to the plane (`EuclideanSpace ℝ (Fin 2)`).

0 axioms, 0 sorries.
-/

set_option linter.unusedVariables false

open scoped RealInnerProductSpace

namespace ProductOfSegmentsOfChordsOQ04

/-! ## Part 1: Power of a point, in any real inner product space -/

section General

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The **power of the point** `P` with respect to the sphere of centre `O` and
radius `r`: the signed quantity `‖P − O‖² − r²`. It is negative inside the
sphere, zero on it, and positive outside. -/
def power (O : E) (r : ℝ) (P : E) : ℝ := ‖P - O‖ ^ 2 - r ^ 2

/-- **Quadratic-form expansion of the power function.**
`pow(P) = ‖P‖² − 2⟪P, O⟫ + ‖O‖² − r²`. The leading term `‖P‖²` is the same for
every sphere — this is the key fact that linearises the radical axis. -/
theorem power_expand (O : E) (r : ℝ) (P : E) :
    power O r P = ‖P‖ ^ 2 - 2 * ⟪P, O⟫ + ‖O‖ ^ 2 - r ^ 2 := by
  unfold power
  rw [norm_sub_sq_real]

/-- **The radical axis is an affine hyperplane.**
Two spheres `(O₁, r₁)` and `(O₂, r₂)` have equal power at `P` **iff** `P`
satisfies the single affine-linear equation
`2⟪P, O₂ − O₁⟫ = (‖O₂‖² − ‖O₁‖²) − (r₂² − r₁²)`.

The quadratic term `‖P‖²` present in each power function cancels, leaving a
linear equation whose normal vector `O₂ − O₁` points along the line of centres.
This is exactly the sense in which "the radical axis is the linear locus where
two quadratic forms agree." -/
theorem radical_axis_linear (O₁ O₂ : E) (r₁ r₂ : ℝ) (P : E) :
    power O₁ r₁ P = power O₂ r₂ P ↔
      2 * ⟪P, O₂ - O₁⟫ = (‖O₂‖ ^ 2 - ‖O₁‖ ^ 2) - (r₂ ^ 2 - r₁ ^ 2) := by
  rw [power_expand, power_expand, inner_sub_right]
  constructor <;> intro h <;> linarith

/-- **The radical axis is perpendicular to the line of centres.**
If `P` and `Q` both lie on the radical axis of two spheres with centres
`O₁ ≠ O₂`, then `Q − P` is orthogonal to `O₂ − O₁`. -/
theorem radical_axis_perp (O₁ O₂ : E) (r₁ r₂ : ℝ) (P Q : E)
    (hP : power O₁ r₁ P = power O₂ r₂ P)
    (hQ : power O₁ r₁ Q = power O₂ r₂ Q) :
    ⟪Q - P, O₂ - O₁⟫ = 0 := by
  rw [radical_axis_linear] at hP hQ
  rw [inner_sub_left]
  linarith

/-- **The radical axis is an affine subspace.**
If `P` and `Q` lie on the radical axis, so does every point `P + t • (Q − P)` of
the line through them. -/
theorem radical_axis_affine (O₁ O₂ : E) (r₁ r₂ : ℝ) (P Q : E) (t : ℝ)
    (hP : power O₁ r₁ P = power O₂ r₂ P)
    (hQ : power O₁ r₁ Q = power O₂ r₂ Q) :
    power O₁ r₁ (P + t • (Q - P)) = power O₂ r₂ (P + t • (Q - P)) := by
  rw [radical_axis_linear] at hP hQ ⊢
  rw [inner_add_left, real_inner_smul_left, inner_sub_left]
  have hd : ⟪Q, O₂ - O₁⟫ - ⟪P, O₂ - O₁⟫ = 0 := by linarith
  rw [hd, mul_zero, add_zero]
  exact hP

end General

/-! ## Part 2: Coordinate form and the radical centre in the plane -/

/-- 2D Euclidean point type, matching the parent file's convention. -/
abbrev Vec2 := EuclideanSpace ℝ (Fin 2)

/-- For `Vec2`, the squared norm of a difference expands to the sum of squared
coordinate differences. (Same helper as `ProductOfSegmentsOfChordsOQ03`.) -/
lemma normSq_coord (X Y : Vec2) :
    ‖X - Y‖ ^ 2 = (X 0 - Y 0) ^ 2 + (X 1 - Y 1) ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, PiLp.inner_apply, Fin.sum_univ_two]
  simp [pow_two]

/-- Coordinate expansion of the power function in the plane. -/
lemma power_coord (O P : Vec2) (r : ℝ) :
    power O r P = (P 0 - O 0) ^ 2 + (P 1 - O 1) ^ 2 - r ^ 2 := by
  unfold power
  rw [normSq_coord]

/-- **Radical-axis equation, coordinate form.**
The locus of equal power between the two planar circles `(Oa, ra)` and
`(Ob, rb)` is the line
`2[(Ob₀ − Oa₀)·P₀ + (Ob₁ − Oa₁)·P₁] = (Ob₀² + Ob₁² − rb²) − (Oa₀² + Oa₁² − ra²)`. -/
lemma equal_power_linear (Oa Ob P : Vec2) (ra rb : ℝ) :
    power Oa ra P = power Ob rb P ↔
      2 * ((Ob 0 - Oa 0) * P 0 + (Ob 1 - Oa 1) * P 1)
        = (Ob 0 ^ 2 + Ob 1 ^ 2 - rb ^ 2) - (Oa 0 ^ 2 + Oa 1 ^ 2 - ra ^ 2) := by
  rw [power_coord, power_coord]
  constructor <;> intro h <;> linear_combination h

/-- **Uniqueness of the radical centre.**
If two points `P, P'` both have equal power to all three circles `(Oᵢ, rᵢ)`
and the centres are non-collinear (the centre determinant is nonzero), then
`P = P'`. -/
theorem radical_center_unique
    (O₁ O₂ O₃ : Vec2) (r₁ r₂ r₃ : ℝ) (P P' : Vec2)
    (hdet : (O₂ 0 - O₁ 0) * (O₃ 1 - O₁ 1) - (O₂ 1 - O₁ 1) * (O₃ 0 - O₁ 0) ≠ 0)
    (hP12 : power O₁ r₁ P = power O₂ r₂ P)
    (hP13 : power O₁ r₁ P = power O₃ r₃ P)
    (hP'12 : power O₁ r₁ P' = power O₂ r₂ P')
    (hP'13 : power O₁ r₁ P' = power O₃ r₃ P') :
    P = P' := by
  rw [equal_power_linear] at hP12 hP13 hP'12 hP'13
  -- Subtract the `P` and `P'` equations: the constant right-hand sides cancel,
  -- giving a homogeneous linear system in the coordinate differences.
  have e1 : (O₂ 0 - O₁ 0) * (P 0 - P' 0) + (O₂ 1 - O₁ 1) * (P 1 - P' 1) = 0 := by
    linear_combination (hP12 - hP'12) / 2
  have e2 : (O₃ 0 - O₁ 0) * (P 0 - P' 0) + (O₃ 1 - O₁ 1) * (P 1 - P' 1) = 0 := by
    linear_combination (hP13 - hP'13) / 2
  -- Cramer elimination against the nonzero centre determinant forces both
  -- coordinate differences to vanish.
  have hx : ((O₂ 0 - O₁ 0) * (O₃ 1 - O₁ 1) - (O₂ 1 - O₁ 1) * (O₃ 0 - O₁ 0))
      * (P 0 - P' 0) = 0 := by
    linear_combination (O₃ 1 - O₁ 1) * e1 - (O₂ 1 - O₁ 1) * e2
  have hy : ((O₂ 0 - O₁ 0) * (O₃ 1 - O₁ 1) - (O₂ 1 - O₁ 1) * (O₃ 0 - O₁ 0))
      * (P 1 - P' 1) = 0 := by
    linear_combination (O₂ 0 - O₁ 0) * e2 - (O₃ 0 - O₁ 0) * e1
  have hP0 : P 0 = P' 0 := by
    rcases mul_eq_zero.mp hx with h | h
    · exact absurd h hdet
    · linarith
  have hP1 : P 1 = P' 1 := by
    rcases mul_eq_zero.mp hy with h | h
    · exact absurd h hdet
    · linarith
  ext i
  fin_cases i
  · exact hP0
  · exact hP1

/-- **Existence of the radical centre.**
Three planar circles with non-collinear centres admit a point of equal power to
all three: the explicit Cramer solution of the two radical-axis equations. -/
theorem radical_center_exists
    (O₁ O₂ O₃ : Vec2) (r₁ r₂ r₃ : ℝ)
    (hdet : (O₂ 0 - O₁ 0) * (O₃ 1 - O₁ 1) - (O₂ 1 - O₁ 1) * (O₃ 0 - O₁ 0) ≠ 0) :
    ∃ P : Vec2, power O₁ r₁ P = power O₂ r₂ P ∧ power O₁ r₁ P = power O₃ r₃ P := by
  -- The radical-axis equations form the 2×2 linear system
  --   2[(O₂₀−O₁₀)x + (O₂₁−O₁₁)y] = K₁₂,   2[(O₃₀−O₁₀)x + (O₃₁−O₁₁)y] = K₁₃
  -- with `Kᵢⱼ = (Oⱼ₀²+Oⱼ₁²−rⱼ²) − (Oᵢ₀²+Oᵢ₁²−rᵢ²)`. Cramer's rule solves it.
  have hden : (2 : ℝ) *
      ((O₂ 0 - O₁ 0) * (O₃ 1 - O₁ 1) - (O₂ 1 - O₁ 1) * (O₃ 0 - O₁ 0)) ≠ 0 := by
    intro h; exact hdet (by linarith)
  refine ⟨!₂[
      (((O₂ 0 ^ 2 + O₂ 1 ^ 2 - r₂ ^ 2) - (O₁ 0 ^ 2 + O₁ 1 ^ 2 - r₁ ^ 2)) * (O₃ 1 - O₁ 1)
        - ((O₃ 0 ^ 2 + O₃ 1 ^ 2 - r₃ ^ 2) - (O₁ 0 ^ 2 + O₁ 1 ^ 2 - r₁ ^ 2)) * (O₂ 1 - O₁ 1))
        / (2 * ((O₂ 0 - O₁ 0) * (O₃ 1 - O₁ 1) - (O₂ 1 - O₁ 1) * (O₃ 0 - O₁ 0))),
      ((O₂ 0 - O₁ 0) * ((O₃ 0 ^ 2 + O₃ 1 ^ 2 - r₃ ^ 2) - (O₁ 0 ^ 2 + O₁ 1 ^ 2 - r₁ ^ 2))
        - (O₃ 0 - O₁ 0) * ((O₂ 0 ^ 2 + O₂ 1 ^ 2 - r₂ ^ 2) - (O₁ 0 ^ 2 + O₁ 1 ^ 2 - r₁ ^ 2)))
        / (2 * ((O₂ 0 - O₁ 0) * (O₃ 1 - O₁ 1) - (O₂ 1 - O₁ 1) * (O₃ 0 - O₁ 0)))], ?_, ?_⟩
  · rw [equal_power_linear]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [mul_div_assoc', mul_div_assoc', ← add_div, mul_div_assoc', div_eq_iff hden]
    ring
  · rw [equal_power_linear]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [mul_div_assoc', mul_div_assoc', ← add_div, mul_div_assoc', div_eq_iff hden]
    ring

/-- **The radical centre exists and is unique** for three circles with
non-collinear centres. -/
theorem radical_center_existsUnique
    (O₁ O₂ O₃ : Vec2) (r₁ r₂ r₃ : ℝ)
    (hdet : (O₂ 0 - O₁ 0) * (O₃ 1 - O₁ 1) - (O₂ 1 - O₁ 1) * (O₃ 0 - O₁ 0) ≠ 0) :
    ∃! P : Vec2, power O₁ r₁ P = power O₂ r₂ P ∧ power O₁ r₁ P = power O₃ r₃ P := by
  obtain ⟨P, hP12, hP13⟩ := radical_center_exists O₁ O₂ O₃ r₁ r₂ r₃ hdet
  refine ⟨P, ⟨hP12, hP13⟩, ?_⟩
  rintro P' ⟨hP'12, hP'13⟩
  exact radical_center_unique O₁ O₂ O₃ r₁ r₂ r₃ P' P hdet hP'12 hP'13 hP12 hP13

end ProductOfSegmentsOfChordsOQ04
