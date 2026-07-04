import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic

/-
# The Neumann Series for a Perturbed Unit `x − t` (geometric-series-oq-02-oq-03-oq-01-oq-03)

The Neumann series `(1 − t)⁻¹ = ∑' n, tⁿ` (see `GeometricSeriesOQ02OQ03OQ01`)
inverts a small perturbation of the *identity*.  This file answers the open
question of generalizing it to a perturbation of an *arbitrary unit* `x`:

    if `x` is a unit and `‖x⁻¹ t‖ < 1`, then `x − t` is a unit and

        (x − t)⁻¹ = (∑' n, (x⁻¹ t)ⁿ) · x⁻¹.

The whole result rests on the factorization

        x − t = x · (1 − x⁻¹ t),

which reduces the perturbed inverse to the ordinary Neumann series applied to
`s := x⁻¹ t`.  The hypothesis `‖x⁻¹ t‖ < 1` is the sharp Neumann condition: it is
exactly what makes `1 − x⁻¹ t` a unit, and it is implied by (but weaker, in a
noncommutative ring, than) Mathlib's `‖t‖ < ‖x⁻¹‖⁻¹` used in `Units.add` /
`NormedRing.inverse_add`.

Contents:

  * `factor_sub` — the algebraic identity `x − t = x · (1 − x⁻¹ t)`;
  * `isUnit_sub` — `x − t` is a unit;
  * `neumann_series_sub` — `(x − t)⁻¹ = (∑' n, (x⁻¹ t)ⁿ) · x⁻¹`;
  * `hasSum_neumann_series_sub` — the `HasSum` form;
  * `neumann_sub_mul_left` / `neumann_sub_mul_right` — genuine two-sided inverse;
  * `neumann_sub_partial_remainder` — finite truncation with explicit remainder;
  * `inverse_sub_continuousAt` — local continuity of `t ↦ (x − t)⁻¹`, the first
    step toward the local analyticity of inversion.

Each result is derived from the identity above and Mathlib's normed-ring API; the
contribution is the packaged, named Neumann-series API for a perturbed unit.

Status: 0 axioms, 0 sorries
-/

namespace GeometricSeriesOQ02OQ03OQ01OQ03

open scoped Topology
open Finset

variable {R : Type*} [NormedRing R] [HasSummableGeomSeries R]

-- ============================================================================
-- Part I: The factorization `x − t = x · (1 − x⁻¹ t)`
-- ============================================================================

/-- **Factoring out the unit.** For a unit `x` and any `t`,
`x − t = x · (1 − x⁻¹ t)`.  This is the algebraic engine of the whole file: it
turns a perturbation of `x` into a perturbation of `1`, ready for the Neumann
series. -/
theorem factor_sub (x : Rˣ) (t : R) :
    (x : R) - t = ↑x * (1 - (↑x⁻¹ : R) * t) := by
  rw [mul_sub, mul_one, ← mul_assoc, Units.mul_inv, one_mul]

-- ============================================================================
-- Part II: Invertibility of `x − t`
-- ============================================================================

/-- **A perturbation of a unit stays a unit.** If `‖x⁻¹ t‖ < 1` then `x − t` is a
unit — the qualitative core of the perturbed Neumann series. -/
theorem isUnit_sub (x : Rˣ) (t : R) (h : ‖(↑x⁻¹ : R) * t‖ < 1) :
    IsUnit ((x : R) - t) := by
  rw [factor_sub x t]
  exact x.isUnit.mul (isUnit_one_sub_of_norm_lt_one h)

-- ============================================================================
-- Part III: The perturbed Neumann series
-- ============================================================================

/-- **Neumann series for a perturbed unit.** If `x` is a unit and `‖x⁻¹ t‖ < 1`
then

    (x − t)⁻¹ = (∑' n, (x⁻¹ t)ⁿ) · x⁻¹.

Setting `x = 1` recovers the ordinary Neumann series `(1 − t)⁻¹ = ∑' n, tⁿ`. -/
theorem neumann_series_sub (x : Rˣ) (t : R) (h : ‖(↑x⁻¹ : R) * t‖ < 1) :
    Ring.inverse ((x : R) - t) = (∑' n : ℕ, ((↑x⁻¹ : R) * t) ^ n) * ↑x⁻¹ := by
  set s : R := (↑x⁻¹ : R) * t with hs
  set u : Rˣ := Units.oneSub s h with hu
  have hfac : (↑x : R) - t = ↑(x * u) := by
    rw [Units.val_mul, hu, Units.val_oneSub, factor_sub x t, hs]
  rw [hfac, Ring.inverse_unit, mul_inv_rev, Units.val_mul]
  congr 1
  rw [← Ring.inverse_unit u, hu, Units.val_oneSub, ← geom_series_eq_inverse s h]

/-- The `HasSum` form of the perturbed Neumann series: the partial sums
`∑_{i<N} (x⁻¹ t)ⁱ · x⁻¹` converge to `(x − t)⁻¹`. -/
theorem hasSum_neumann_series_sub (x : Rˣ) (t : R) (h : ‖(↑x⁻¹ : R) * t‖ < 1) :
    HasSum (fun n : ℕ => ((↑x⁻¹ : R) * t) ^ n * ↑x⁻¹) (Ring.inverse ((x : R) - t)) := by
  rw [neumann_series_sub x t h]
  exact ((summable_geometric_of_norm_lt_one h).hasSum).mul_right _

-- ============================================================================
-- Part IV: Two-sided inverse
-- ============================================================================

/-- The perturbed Neumann series is a genuine **left** inverse of `x − t`. -/
theorem neumann_sub_mul_left (x : Rˣ) (t : R) (h : ‖(↑x⁻¹ : R) * t‖ < 1) :
    ((∑' n : ℕ, ((↑x⁻¹ : R) * t) ^ n) * ↑x⁻¹) * ((x : R) - t) = 1 := by
  rw [← neumann_series_sub x t h]
  exact Ring.inverse_mul_cancel _ (isUnit_sub x t h)

/-- The perturbed Neumann series is a genuine **right** inverse of `x − t`. -/
theorem neumann_sub_mul_right (x : Rˣ) (t : R) (h : ‖(↑x⁻¹ : R) * t‖ < 1) :
    ((x : R) - t) * ((∑' n : ℕ, ((↑x⁻¹ : R) * t) ^ n) * ↑x⁻¹) = 1 := by
  rw [← neumann_series_sub x t h]
  exact Ring.mul_inverse_cancel _ (isUnit_sub x t h)

-- ============================================================================
-- Part V: Finite truncation with remainder
-- ============================================================================

/-- **Partial-sum remainder.** Truncating the perturbed Neumann series after `N`
terms leaves the explicit remainder `(x⁻¹ t)ᴺ · (x − t)⁻¹`:

    (x − t)⁻¹ = (∑_{i<N} (x⁻¹ t)ⁱ) · x⁻¹ + (x⁻¹ t)ᴺ · (x − t)⁻¹.

Since `‖(x⁻¹ t)ᴺ‖ → 0`, the truncation approximates the inverse to any accuracy —
the basis of preconditioned iterative inversion. -/
theorem neumann_sub_partial_remainder (x : Rˣ) (N : ℕ) (t : R)
    (h : ‖(↑x⁻¹ : R) * t‖ < 1) :
    Ring.inverse ((x : R) - t)
      = (∑ i ∈ range N, ((↑x⁻¹ : R) * t) ^ i) * ↑x⁻¹
        + ((↑x⁻¹ : R) * t) ^ N * Ring.inverse ((x : R) - t) := by
  have key : Ring.inverse ((x : R) - t)
      = Ring.inverse (1 - (↑x⁻¹ : R) * t) * ↑x⁻¹ := by
    rw [neumann_series_sub x t h, geom_series_eq_inverse _ h]
  conv_lhs =>
    rw [key, NormedRing.inverse_one_sub_nth_order' N h, add_mul, mul_assoc, ← key]

-- ============================================================================
-- Part VI: Local continuity of inversion
-- ============================================================================

/-- **Local continuity of the perturbed inverse.** For a unit `x` and any base
point `t₀` with `‖x⁻¹ t₀‖ < 1`, the map `t ↦ (x − t)⁻¹` is continuous at `t₀`.
This is the first quantitative step toward the local analyticity of inversion on
the (open) unit group. -/
theorem inverse_sub_continuousAt (x : Rˣ) (t₀ : R) (h : ‖(↑x⁻¹ : R) * t₀‖ < 1) :
    ContinuousAt (fun t : R => Ring.inverse ((x : R) - t)) t₀ := by
  obtain ⟨v, hv⟩ := isUnit_sub x t₀ h
  have hcont : ContinuousAt Ring.inverse ((x : R) - t₀) :=
    hv ▸ NormedRing.inverse_continuousAt v
  exact hcont.comp (continuousAt_const.sub continuousAt_id)

-- ============================================================================
-- Part VII: Summary
-- ============================================================================

/-
## Summary

| Result | Statement | Backing |
|--------|-----------|---------|
| `factor_sub` | x − t = x · (1 − x⁻¹ t) | ring + `Units.mul_inv` |
| `isUnit_sub` | x − t is a unit | `isUnit_one_sub_of_norm_lt_one` |
| `neumann_series_sub` | (x − t)⁻¹ = (∑' (x⁻¹ t)ⁿ) x⁻¹ | `geom_series_eq_inverse` |
| `hasSum_neumann_series_sub` | partial sums → (x − t)⁻¹ | `HasSum.mul_right` |
| `neumann_sub_mul_left/right` | two-sided inverse | `Ring.(inverse_)mul_cancel` |
| `neumann_sub_partial_remainder` | truncation + (x⁻¹ t)ᴺ·(x − t)⁻¹ | `inverse_one_sub_nth_order'` |
| `inverse_sub_continuousAt` | t ↦ (x − t)⁻¹ continuous | `inverse_continuousAt` |

Taking `x = 1` collapses every statement to the corresponding result of the
parent file `GeometricSeriesOQ02OQ03OQ01`.  The sharp hypothesis `‖x⁻¹ t‖ < 1`
(rather than Mathlib's `‖t‖ < ‖x⁻¹‖⁻¹`) means the series converges precisely on
the largest ball guaranteeing `1 − x⁻¹ t` invertible, and `inverse_sub_continuousAt`
is the local step behind the openness of the unit group and the holomorphy of the
resolvent `(λ − T)⁻¹` in spectral theory.
-/

end GeometricSeriesOQ02OQ03OQ01OQ03

#check @GeometricSeriesOQ02OQ03OQ01OQ03.neumann_series_sub
#check @GeometricSeriesOQ02OQ03OQ01OQ03.isUnit_sub
#check @GeometricSeriesOQ02OQ03OQ01OQ03.hasSum_neumann_series_sub
#check @GeometricSeriesOQ02OQ03OQ01OQ03.neumann_sub_partial_remainder
#check @GeometricSeriesOQ02OQ03OQ01OQ03.inverse_sub_continuousAt
