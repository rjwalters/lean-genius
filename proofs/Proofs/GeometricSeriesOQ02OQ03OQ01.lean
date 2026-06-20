import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic

/-
# The Neumann Series for the Inverse of 1 − t (geometric-series-oq-02-oq-03-oq-01)

The geometric series ∑ rⁿ = 1/(1 − r) for |r| < 1 has a sweeping operator-theoretic
generalization.  In any Banach algebra (a complete normed ring), if ‖t‖ < 1 then
1 − t is invertible and its inverse is given by the convergent series

    (1 − t)⁻¹ = ∑' n, tⁿ      (the **Neumann series**).

This is the cornerstone of perturbation theory: a small perturbation of the
identity stays invertible, with an inverse computable to any order by truncating
the series.  It underlies the openness of the unit group, the holomorphy of the
resolvent, and the convergence of iterative solvers (Jacobi / Gauss–Seidel).

This file packages the Neumann series over a normed ring with summable geometric
series (`HasSummableGeomSeries`, which holds for every complete normed ring /
Banach algebra):

  * `neumann_series` — `Ring.inverse (1 - t) = ∑' n, tⁿ`;
  * `hasSum_neumann_series` — the `HasSum` form;
  * `isUnit_one_sub` — `1 − t` is a unit;
  * `neumann_mul_left` / `neumann_mul_right` — the series is a genuine two-sided
    inverse of `1 − t`;
  * `neumann_partial_remainder` — the finite truncation with explicit remainder.

Each result is a thin wrapper around Mathlib's `geom_series_eq_inverse`,
`hasSum_geom_series_inverse`, and `NormedRing.inverse_one_sub_nth_order'`; the
contribution is the packaged, named Neumann-series API.

Status: 0 axioms, 0 sorries
-/

namespace GeometricSeriesOQ02OQ03OQ01

open scoped Topology
open Finset

variable {R : Type*} [NormedRing R] [HasSummableGeomSeries R]

-- ============================================================================
-- Part I: The Neumann series identity
-- ============================================================================

/-- **Neumann series.** In a normed ring with summable geometric series (e.g. any
Banach algebra), if `‖t‖ < 1` then the inverse of `1 − t` is the convergent
series `∑' n, tⁿ`. -/
theorem neumann_series (t : R) (h : ‖t‖ < 1) :
    Ring.inverse (1 - t) = ∑' n : ℕ, t ^ n :=
  (geom_series_eq_inverse t h).symm

/-- The `HasSum` form of the Neumann series: the partial sums `∑_{i<N} tⁱ`
converge to `(1 − t)⁻¹`. -/
theorem hasSum_neumann_series (t : R) (h : ‖t‖ < 1) :
    HasSum (fun n : ℕ => t ^ n) (Ring.inverse (1 - t)) :=
  hasSum_geom_series_inverse t h

/-- The geometric series `∑' n, tⁿ` is summable when `‖t‖ < 1`. -/
theorem summable_neumann_series (t : R) (h : ‖t‖ < 1) :
    Summable (fun n : ℕ => t ^ n) :=
  summable_geometric_of_norm_lt_one h

-- ============================================================================
-- Part II: Invertibility of 1 − t
-- ============================================================================

/-- A small perturbation of the identity stays invertible: `‖t‖ < 1 ⟹ 1 − t` is a
unit. This is the qualitative heart of the Neumann series. -/
theorem isUnit_one_sub (t : R) (h : ‖t‖ < 1) : IsUnit (1 - t) :=
  isUnit_one_sub_of_norm_lt_one h

/-- The Neumann series is a genuine **left** inverse: `(∑' n, tⁿ) · (1 − t) = 1`. -/
theorem neumann_mul_left (t : R) (h : ‖t‖ < 1) :
    (∑' n : ℕ, t ^ n) * (1 - t) = 1 := by
  rw [← neumann_series t h]
  exact Ring.inverse_mul_cancel _ (isUnit_one_sub t h)

/-- The Neumann series is a genuine **right** inverse: `(1 − t) · (∑' n, tⁿ) = 1`. -/
theorem neumann_mul_right (t : R) (h : ‖t‖ < 1) :
    (1 - t) * (∑' n : ℕ, t ^ n) = 1 := by
  rw [← neumann_series t h]
  exact Ring.mul_inverse_cancel _ (isUnit_one_sub t h)

-- ============================================================================
-- Part III: Finite truncation with remainder
-- ============================================================================

/-- **Partial-sum remainder.** Truncating the Neumann series after `N` terms
leaves the explicit remainder `tᴺ · (1 − t)⁻¹`:

    (1 − t)⁻¹ = (∑_{i<N} tⁱ) + tᴺ · (1 − t)⁻¹.

Since `‖tᴺ‖ → 0`, the truncation `∑_{i<N} tⁱ` approximates the inverse to any
desired accuracy — the basis of iterative inversion. -/
theorem neumann_partial_remainder (N : ℕ) (t : R) (h : ‖t‖ < 1) :
    Ring.inverse (1 - t) = (∑ i ∈ range N, t ^ i) + t ^ N * Ring.inverse (1 - t) :=
  NormedRing.inverse_one_sub_nth_order' N h

-- ============================================================================
-- Part IV: Summary
-- ============================================================================

/-
## Summary

| Result | Statement | Backing |
|--------|-----------|---------|
| `neumann_series` | (1 − t)⁻¹ = ∑' n, tⁿ | `geom_series_eq_inverse` |
| `hasSum_neumann_series` | partial sums → (1 − t)⁻¹ | `hasSum_geom_series_inverse` |
| `isUnit_one_sub` | 1 − t is a unit | `isUnit_one_sub_of_norm_lt_one` |
| `neumann_mul_left/right` | two-sided inverse | `Ring.inverse_mul_cancel` |
| `neumann_partial_remainder` | truncation + tᴺ·(1−t)⁻¹ | `inverse_one_sub_nth_order'` |

The scalar geometric series ∑ rⁿ = 1/(1 − r) is the case `R = ℝ` (or ℂ).  Over a
Banach algebra the same series inverts `1 − t` for any `t` in the open unit ball,
making the unit group open and the map `t ↦ (1 − t)⁻¹` analytic.  Specializing to
bounded operators on a Banach space recovers the operator Neumann series used in
the theory of integral equations and the resolvent `(λ − T)⁻¹` of spectral theory.
-/

end GeometricSeriesOQ02OQ03OQ01

#check @GeometricSeriesOQ02OQ03OQ01.neumann_series
#check @GeometricSeriesOQ02OQ03OQ01.hasSum_neumann_series
#check @GeometricSeriesOQ02OQ03OQ01.neumann_mul_left
#check @GeometricSeriesOQ02OQ03OQ01.neumann_partial_remainder
