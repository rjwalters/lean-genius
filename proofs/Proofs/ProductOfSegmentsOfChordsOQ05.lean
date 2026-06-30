import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic

/-!
# Power of a Point via Vieta: Direction-Independence (OQ-05)

This file answers `product-of-segments-of-chords-oq-05`:

> "Power of a Point via Vieta: Direction-Independence of the Line–Circle
> Intersection Product."

The parent *Product of Segments of Chords* entry proves the classical fact that
for two chords `AB`, `CD` of a circle meeting at a point `P` one has
`PA · PB = PC · PD`. Here we explain **why** the product is the same for every
chord through `P`, by reducing it to **Vieta's formula** for a monic quadratic.

## The mechanism

Fix a sphere of centre `O` and radius `r`, and a base point `P`. A line through
`P` in **unit** direction `d` meets the sphere where the parameter `t` (the
*signed* distance from `P`, since `‖d‖ = 1`) satisfies the monic quadratic

`t² + 2⟪P − O, d⟫·t + (‖P − O‖² − r²) = 0`.

The **constant coefficient** is `‖P − O‖² − r²`, the **power of the point** `P`,
which does **not depend** on the direction `d`. By Vieta's formula the product of
the two intersection parameters equals that constant coefficient. Hence the
signed product `t₁ · t₂` is the power of `P` for **every** line through `P` —
exactly the direction-independence the chord theorem observes.

## Main results

* `power_along_line` — the power restricted to a line is the quadratic
  `‖d‖²·t² + 2⟪P − O, d⟫·t + power O r P`.
* `power_along_unit_line` — for a unit direction this is *monic*.
* `chord_product_eq_power` — **Vieta**: the two intersection parameters multiply
  to the power of the point.
* `chord_sum_eq` — the companion sum formula `t₁ + t₂ = −2⟪P − O, d⟫`.
* `chord_product_direction_independent` — the **headline**: two secant lines
  through `P` in different directions give the same signed product.
* `chord_product_sign` — with a nonnegative radius the product is negative inside
  the sphere and positive outside (intersecting-chords vs. secant–secant).

All results hold in an arbitrary real inner product space (any dimension,
including infinite-dimensional Hilbert spaces). The radical-axis / radical-centre
companion to these facts is developed separately in
`ProductOfSegmentsOfChordsOQ04`.

0 axioms, 0 sorries.
-/

set_option linter.unusedVariables false

open scoped RealInnerProductSpace

namespace ProductOfSegmentsOfChordsOQ05

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The **power of the point** `P` with respect to the sphere of centre `O` and
radius `r`: the signed quantity `‖P − O‖² − r²`. It is negative inside the
sphere, zero on it, and positive outside. -/
def power (O : E) (r : ℝ) (P : E) : ℝ := ‖P - O‖ ^ 2 - r ^ 2

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

end ProductOfSegmentsOfChordsOQ05
