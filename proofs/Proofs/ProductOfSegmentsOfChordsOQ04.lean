import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic

/-!
# Power of a Point via Vieta, and the Radical Axis (OQ-04)

This file answers `product-of-segments-of-chords-oq-04`:

> "Power of a Point via Vieta: Direction-Independence of the Line–Circle
> Intersection Product."

The parent *Product of Segments of Chords* entry proves the classical fact that
for two chords `AB`, `CD` of a circle meeting at an interior point `P` one has
`PA · PB = PC · PD`. Here we explain **why** the product is the same for every
chord through `P`, by reducing it to **Vieta's formula** for a quadratic, and we
push the same algebra to its natural conclusion — the **radical axis** and
**radical centre**.

## The Vieta mechanism (Part 1)

Fix a sphere of centre `O` and radius `r`, and a base point `P`. A line through
`P` in **unit** direction `d` meets the sphere where the parameter `t` (the
*signed* distance from `P`, since `‖d‖ = 1`) satisfies the monic quadratic

`t² + 2⟪P − O, d⟫·t + (‖P − O‖² − r²) = 0`.

The **constant coefficient** is `‖P − O‖² − r²` — the **power of the point** `P`,
which does **not depend on the direction** `d`. By Vieta's formula the product of
the two intersection parameters equals that constant coefficient. Hence the
signed product `t₁ · t₂` is the power of `P` for **every** line through `P`,
which is exactly the direction-independence the chord theorem observes.

* `power_along_line` — the quadratic in `t` obtained by restricting `power` to a line.
* `chord_product_eq_power` — Vieta: the two intersection parameters multiply to
  the power of the point.
* `chord_product_direction_independent` — the headline: the product is the same
  for two different directions through `P`.
* `chord_sum_eq` / `chord_product_sign` — the companion sum formula and the
  inside/outside sign of the product.

## The radical axis as a linear locus (Part 2)

Although `power` is a *quadratic* function of `P`, the **difference** of the
power functions of two spheres is **affine-linear** — the quadratic term `‖P‖²`
cancels. So the locus where two spheres have equal power (the **radical axis**)
is a hyperplane perpendicular to the line of centres, and three spheres with
non-collinear centres have a unique common point (the **radical centre**).

* `power_expand`, `radical_axis_linear`, `radical_axis_perp`, `radical_axis_affine`.
* `equal_power_linear`, `radical_center_unique`, `radical_center_exists`,
  `radical_center_existsUnique` (planar, `EuclideanSpace ℝ (Fin 2)`).

0 axioms, 0 sorries.
-/

set_option linter.unusedVariables false

open scoped RealInnerProductSpace

namespace ProductOfSegmentsOfChordsOQ04

/-! ## Power of a point, in any real inner product space -/

section General

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The **power of the point** `P` with respect to the sphere of centre `O` and
radius `r`: the signed quantity `‖P − O‖² − r²`. It is negative inside the
sphere, zero on it, and positive outside. -/
def power (O : E) (r : ℝ) (P : E) : ℝ := ‖P - O‖ ^ 2 - r ^ 2

/-! ### Part 1 — Vieta and direction-independence -/

/-- **The power function restricted to a line is a quadratic in the parameter.**
Along the line `t ↦ P + t • d` the power is
`‖d‖²·t² + 2⟪P − O, d⟫·t + power O r P`.

The constant term is `power O r P` — independent of the direction `d`. -/
theorem power_along_line (O P d : E) (r t : ℝ) :
    power O r (P + t • d)
      = ‖d‖ ^ 2 * t ^ 2 + 2 * ⟪P - O, d⟫ * t + power O r P := by
  unfold power
  have hPt : P + t • d - O = (P - O) + t • d := by abel
  rw [hPt, norm_add_sq_real, real_inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs,
    sq_abs]
  ring

/-- For a **unit** direction the restriction is *monic*:
`t² + 2⟪P − O, d⟫·t + power O r P`. -/
theorem power_along_unit_line (O P d : E) (r t : ℝ) (hd : ‖d‖ = 1) :
    power O r (P + t • d) = t ^ 2 + 2 * ⟪P - O, d⟫ * t + power O r P := by
  rw [power_along_line, hd]; ring

/-- **Vieta's formula for the chord parameters.**
If a line through `P` in unit direction `d` meets the sphere at the two distinct
parameters `t₁ ≠ t₂` (i.e. `P + tᵢ • d` lies on the sphere), then the product of
the parameters is exactly the **power of the point** `P`:
`t₁ · t₂ = power O r P`.

Because the right-hand side has no dependence on `d`, this is the
direction-independence of the line–circle intersection product. -/
theorem chord_product_eq_power (O P d : E) (r t₁ t₂ : ℝ) (hd : ‖d‖ = 1)
    (hne : t₁ ≠ t₂)
    (h₁ : power O r (P + t₁ • d) = 0) (h₂ : power O r (P + t₂ • d) = 0) :
    t₁ * t₂ = power O r P := by
  rw [power_along_unit_line _ _ _ _ _ hd] at h₁ h₂
  -- `t₂·(quad at t₁) − t₁·(quad at t₂) = (t₁ − t₂)·(t₁·t₂ − power)`.
  have key : (t₁ - t₂) * (t₁ * t₂ - power O r P) = 0 := by
    linear_combination t₂ * h₁ - t₁ * h₂
  rcases mul_eq_zero.mp key with h | h
  · exact absurd (sub_eq_zero.mp h) hne
  · linarith [sub_eq_zero.mp h]

/-- **The companion sum formula.** Under the same hypotheses the two chord
parameters sum to `-2⟪P − O, d⟫`. -/
theorem chord_sum_eq (O P d : E) (r t₁ t₂ : ℝ) (hd : ‖d‖ = 1) (hne : t₁ ≠ t₂)
    (h₁ : power O r (P + t₁ • d) = 0) (h₂ : power O r (P + t₂ • d) = 0) :
    t₁ + t₂ = -(2 * ⟪P - O, d⟫) := by
  rw [power_along_unit_line _ _ _ _ _ hd] at h₁ h₂
  have key : (t₁ - t₂) * (t₁ + t₂ + 2 * ⟪P - O, d⟫) = 0 := by
    linear_combination h₁ - h₂
  rcases mul_eq_zero.mp key with h | h
  · exact absurd (sub_eq_zero.mp h) hne
  · linarith

/-- **Direction-independence of the chord product.**
Two lines through `P`, in unit directions `d` and `d'`, each meeting the sphere
at two distinct parameters, produce the **same** signed product:
`t₁ · t₂ = s₁ · s₂`. Both equal the power of the point `P`. -/
theorem chord_product_direction_independent (O P d d' : E) (r t₁ t₂ s₁ s₂ : ℝ)
    (hd : ‖d‖ = 1) (hd' : ‖d'‖ = 1) (hne : t₁ ≠ t₂) (hne' : s₁ ≠ s₂)
    (h₁ : power O r (P + t₁ • d) = 0) (h₂ : power O r (P + t₂ • d) = 0)
    (g₁ : power O r (P + s₁ • d') = 0) (g₂ : power O r (P + s₂ • d') = 0) :
    t₁ * t₂ = s₁ * s₂ := by
  rw [chord_product_eq_power O P d r t₁ t₂ hd hne h₁ h₂,
    chord_product_eq_power O P d' r s₁ s₂ hd' hne' g₁ g₂]

/-- **Sign of the chord product.** With a nonnegative radius the signed product
`t₁ · t₂` is negative exactly when `P` is strictly inside the sphere
(`‖P − O‖ < r`) and positive exactly when `P` is strictly outside
(`r < ‖P − O‖`) — the intersecting-chords vs. secant–secant dichotomy. -/
theorem chord_product_sign (O P d : E) (r t₁ t₂ : ℝ) (hr : 0 ≤ r) (hd : ‖d‖ = 1)
    (hne : t₁ ≠ t₂)
    (h₁ : power O r (P + t₁ • d) = 0) (h₂ : power O r (P + t₂ • d) = 0) :
    (t₁ * t₂ < 0 ↔ ‖P - O‖ < r) ∧ (0 < t₁ * t₂ ↔ r < ‖P - O‖) := by
  have hprod : t₁ * t₂ = ‖P - O‖ ^ 2 - r ^ 2 :=
    chord_product_eq_power O P d r t₁ t₂ hd hne h₁ h₂
  have hn : (0 : ℝ) ≤ ‖P - O‖ := norm_nonneg _
  rw [hprod]
  refine ⟨⟨fun h => ?_, fun h => ?_⟩, ⟨fun h => ?_, fun h => ?_⟩⟩
  · nlinarith
  · nlinarith
  · nlinarith
  · nlinarith

/-! ### Part 2 — The radical axis as a linear locus -/

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

/-! ## The radical centre in the plane -/

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
  -- The common denominator `2·det` is nonzero; supply it explicitly so the
  -- denominator-clearing step matches `hdet`'s un-expanded determinant.
  have hden : (2 : ℝ) * ((O₂ 0 - O₁ 0) * (O₃ 1 - O₁ 1) - (O₂ 1 - O₁ 1) * (O₃ 0 - O₁ 0)) ≠ 0 :=
    mul_ne_zero two_ne_zero hdet
  refine ⟨!₂[
      (((O₂ 0 ^ 2 + O₂ 1 ^ 2 - r₂ ^ 2) - (O₁ 0 ^ 2 + O₁ 1 ^ 2 - r₁ ^ 2)) * (O₃ 1 - O₁ 1)
        - ((O₃ 0 ^ 2 + O₃ 1 ^ 2 - r₃ ^ 2) - (O₁ 0 ^ 2 + O₁ 1 ^ 2 - r₁ ^ 2)) * (O₂ 1 - O₁ 1))
        / (2 * ((O₂ 0 - O₁ 0) * (O₃ 1 - O₁ 1) - (O₂ 1 - O₁ 1) * (O₃ 0 - O₁ 0))),
      ((O₂ 0 - O₁ 0) * ((O₃ 0 ^ 2 + O₃ 1 ^ 2 - r₃ ^ 2) - (O₁ 0 ^ 2 + O₁ 1 ^ 2 - r₁ ^ 2))
        - (O₃ 0 - O₁ 0) * ((O₂ 0 ^ 2 + O₂ 1 ^ 2 - r₂ ^ 2) - (O₁ 0 ^ 2 + O₁ 1 ^ 2 - r₁ ^ 2)))
        / (2 * ((O₂ 0 - O₁ 0) * (O₃ 1 - O₁ 1) - (O₂ 1 - O₁ 1) * (O₃ 0 - O₁ 0)))], ?_, ?_⟩
  · rw [equal_power_linear]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [← mul_div_assoc, ← mul_div_assoc, ← add_div, ← mul_div_assoc,
      div_eq_iff hden]
    ring
  · rw [equal_power_linear]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [← mul_div_assoc, ← mul_div_assoc, ← add_div, ← mul_div_assoc,
      div_eq_iff hden]
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
