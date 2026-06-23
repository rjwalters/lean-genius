import Mathlib

/-!
# Descartes Circle Theorem (curvature relation and Soddy circles)

For four mutually tangent circles with signed curvatures `k₁, k₂, k₃, k₄`
(curvature `= ±1/radius`, negative for a circle internally enclosing the others),
the **Descartes Circle Theorem** asserts

  `(k₁ + k₂ + k₃ + k₄)² = 2·(k₁² + k₂² + k₃² + k₄²)`.

This file formalizes the algebraic core of that relation. Viewing the relation as
a quadratic in `k₄` and solving it yields the two **Soddy circles**

  `k₄ = (k₁ + k₂ + k₃) ± 2·√(k₁k₂ + k₂k₃ + k₃k₁)`.

We prove the relation is *equivalent* to this pair of solutions (given the symmetric
product is nonnegative, which is automatic when the relation holds), and record the
Vieta relations satisfied by the two Soddy curvatures.

This is the curvature-arithmetic content of the theorem; it does not derive the
relation from the planar tangency geometry. It is distinct from Mathlib's
`Descartes' Rule of Signs` (a polynomial-roots result).
-/

namespace DescartesCircleTheorem

/-- The Descartes Circle relation among four signed curvatures. -/
def descartesRel (k₁ k₂ k₃ k₄ : ℝ) : Prop :=
  (k₁ + k₂ + k₃ + k₄) ^ 2 = 2 * (k₁ ^ 2 + k₂ ^ 2 + k₃ ^ 2 + k₄ ^ 2)

/-- The Descartes relation is equivalent to a perfect-square condition on `k₄`:
the deviation of `k₄` from the outer-curvature sum squares to `4` times the
symmetric product. This is the quadratic-in-`k₄` rewriting of the relation. -/
theorem descartesRel_iff_sq (k₁ k₂ k₃ k₄ : ℝ) :
    descartesRel k₁ k₂ k₃ k₄ ↔
      (k₄ - (k₁ + k₂ + k₃)) ^ 2 = 4 * (k₁ * k₂ + k₂ * k₃ + k₃ * k₁) := by
  unfold descartesRel
  constructor <;> intro h <;> linear_combination -h

/-- When the Descartes relation holds, the symmetric product is nonnegative
(it equals a square divided by `4`), so the Soddy square root is well defined. -/
theorem descartes_symmProd_nonneg {k₁ k₂ k₃ k₄ : ℝ} (h : descartesRel k₁ k₂ k₃ k₄) :
    0 ≤ k₁ * k₂ + k₂ * k₃ + k₃ * k₁ := by
  have hsq := (descartesRel_iff_sq k₁ k₂ k₃ k₄).mp h
  nlinarith [sq_nonneg (k₄ - (k₁ + k₂ + k₃))]

/-- **Soddy solutions (forward).** If four curvatures satisfy the Descartes relation,
then the fourth is one of the two Soddy values. -/
theorem descartes_soddy_forward {k₁ k₂ k₃ k₄ : ℝ} (h : descartesRel k₁ k₂ k₃ k₄) :
    k₄ = (k₁ + k₂ + k₃) + 2 * Real.sqrt (k₁ * k₂ + k₂ * k₃ + k₃ * k₁) ∨
    k₄ = (k₁ + k₂ + k₃) - 2 * Real.sqrt (k₁ * k₂ + k₂ * k₃ + k₃ * k₁) := by
  have hsq := (descartesRel_iff_sq k₁ k₂ k₃ k₄).mp h
  have hD := descartes_symmProd_nonneg h
  have hs : Real.sqrt (k₁ * k₂ + k₂ * k₃ + k₃ * k₁) ^ 2 = k₁ * k₂ + k₂ * k₃ + k₃ * k₁ :=
    Real.sq_sqrt hD
  have hfac :
      (k₄ - (k₁ + k₂ + k₃) - 2 * Real.sqrt (k₁ * k₂ + k₂ * k₃ + k₃ * k₁)) *
        (k₄ - (k₁ + k₂ + k₃) + 2 * Real.sqrt (k₁ * k₂ + k₂ * k₃ + k₃ * k₁)) = 0 := by
    linear_combination hsq - 4 * hs
  rcases mul_eq_zero.mp hfac with h' | h'
  · left; linarith
  · right; linarith

/-- **Soddy solutions (backward).** Each Soddy value (with the symmetric product
nonnegative) satisfies the Descartes relation. -/
theorem descartes_soddy_backward {k₁ k₂ k₃ k₄ : ℝ}
    (hD : 0 ≤ k₁ * k₂ + k₂ * k₃ + k₃ * k₁)
    (h : k₄ = (k₁ + k₂ + k₃) + 2 * Real.sqrt (k₁ * k₂ + k₂ * k₃ + k₃ * k₁) ∨
         k₄ = (k₁ + k₂ + k₃) - 2 * Real.sqrt (k₁ * k₂ + k₂ * k₃ + k₃ * k₁)) :
    descartesRel k₁ k₂ k₃ k₄ := by
  rw [descartesRel_iff_sq]
  have hs : Real.sqrt (k₁ * k₂ + k₂ * k₃ + k₃ * k₁) ^ 2 = k₁ * k₂ + k₂ * k₃ + k₃ * k₁ :=
    Real.sq_sqrt hD
  rcases h with h | h <;> subst h <;> linear_combination 4 * hs

/-- **Descartes Circle Theorem (headline).** The Descartes relation holds iff the
symmetric product is nonnegative and `k₄` is one of the two Soddy curvatures. -/
theorem descartes_circle {k₁ k₂ k₃ k₄ : ℝ} :
    descartesRel k₁ k₂ k₃ k₄ ↔
      0 ≤ k₁ * k₂ + k₂ * k₃ + k₃ * k₁ ∧
        (k₄ = (k₁ + k₂ + k₃) + 2 * Real.sqrt (k₁ * k₂ + k₂ * k₃ + k₃ * k₁) ∨
         k₄ = (k₁ + k₂ + k₃) - 2 * Real.sqrt (k₁ * k₂ + k₂ * k₃ + k₃ * k₁)) := by
  constructor
  · intro h; exact ⟨descartes_symmProd_nonneg h, descartes_soddy_forward h⟩
  · rintro ⟨hD, h⟩; exact descartes_soddy_backward hD h

/-- **Vieta (sum).** The two Soddy curvatures sum to twice the outer-curvature sum. -/
theorem soddy_sum (k₁ k₂ k₃ : ℝ) :
    ((k₁ + k₂ + k₃) + 2 * Real.sqrt (k₁ * k₂ + k₂ * k₃ + k₃ * k₁)) +
        ((k₁ + k₂ + k₃) - 2 * Real.sqrt (k₁ * k₂ + k₂ * k₃ + k₃ * k₁)) =
      2 * (k₁ + k₂ + k₃) := by
  ring

/-- **Vieta (product).** The product of the two Soddy curvatures. -/
theorem soddy_prod {k₁ k₂ k₃ : ℝ} (hD : 0 ≤ k₁ * k₂ + k₂ * k₃ + k₃ * k₁) :
    ((k₁ + k₂ + k₃) + 2 * Real.sqrt (k₁ * k₂ + k₂ * k₃ + k₃ * k₁)) *
        ((k₁ + k₂ + k₃) - 2 * Real.sqrt (k₁ * k₂ + k₂ * k₃ + k₃ * k₁)) =
      (k₁ + k₂ + k₃) ^ 2 - 4 * (k₁ * k₂ + k₂ * k₃ + k₃ * k₁) := by
  have hs : Real.sqrt (k₁ * k₂ + k₂ * k₃ + k₃ * k₁) ^ 2 = k₁ * k₂ + k₂ * k₃ + k₃ * k₁ :=
    Real.sq_sqrt hD
  linear_combination -4 * hs

end DescartesCircleTheorem
