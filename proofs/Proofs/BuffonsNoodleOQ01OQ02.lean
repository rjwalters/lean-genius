/-
  # Buffon–Laplace for `k` Non-Parallel Line Families (Cauchy–Crofton Discretization)

  The parent leaf (`BuffonsNoodleOQ01`) proves the **two-family** Buffon–Laplace grid
  theorem: a polygonal noodle `N` of total length `L` dropped on a grid of two
  perpendicular line families with spacings `dh, dv` crosses, in expectation,

  `E[crossings] = 2L/(π·dh) + 2L/(π·dv)`,

  obtained by additivity of expectation from the single-family polygonal Buffon
  theorem `buffon_noodle_polygon : N.expectedCrossings d = 2L/(π·d)`.

  This file answers `buffons-noodle-oq-01-oq-02`:

  > Extend the Buffon grid identity to `k` non-parallel families at angles
  > `θ₁, …, θ_k`, with expected crossings `(2L/π)·Σ_j 1/d_j`
  > (general Buffon–Laplace / Cauchy–Crofton discretization).

  ## What is proved

  * **`expectedMultiCrossings`** — the expected total number of crossings of `N`
    against `k` line families with spacings `d : Fin k → ℝ`, defined (by additivity
    of expectation) as `∑ j, N.expectedCrossings (d j)`.

  * **`buffon_noodle_multi_family`** (headline) — for positive spacings,
    `E[crossings] = (2L/π)·Σ_j (d_j)⁻¹`. Each family contributes `2L/(π·d_j)` by the
    parent's single-family theorem, and the total is their sum by linearity.

  * **Specializations and structure.** Recovery of the two-family grid as the
    `k = 2` case (`expectedGridCrossings_eq_multi`), the equal-spacing count
    `2kL/(π·d)` (`buffon_noodle_multi_family_const`), additivity (`…_eq_sum`),
    nonnegativity, and monotonicity in the number of families.

  ## Why the angles `θ_j` do not appear

  The candidate speaks of families "at angles `θ₁, …, θ_k`", yet the formula has no
  angle dependence. This is the crux of Buffon–Laplace, not an omission. The noodle is
  dropped at a uniformly random *position and orientation*, so the expected number of
  crossings with a *single* family depends only on the noodle's length and the family
  spacing — never on the family's orientation (this is exactly the content of the
  parent's `buffon_noodle_polygon`, whose statement carries no angle). By linearity of
  expectation, `E[Σ_j crossings_j] = Σ_j E[crossings_j] = Σ_j 2L/(π·d_j)`, regardless
  of how the `k` families are angled relative to one another. The orientation-free
  formula `(2L/π)·Σ_j 1/d_j` is therefore the honest and complete answer; modelling the
  families by their spacings `d : Fin k → ℝ` loses no information.

  Tags: buffon-laplace, cauchy-crofton, geometric-probability, expectation-linearity,
        integral-geometry
-/
import Proofs.BuffonsNoodleOQ01
import Mathlib.Tactic

open Real Finset BigOperators BuffonsNoodle BuffonsNoodleOQ01

/- ============================================================
   § 1 : Expected crossings against `k` line families
   ============================================================ -/

namespace BuffonsNoodle

/-- The expected total number of crossings of a polygonal noodle `N` with `k` families
    of parallel lines, the `j`-th family having spacing `d j`. By additivity of
    expectation it is the sum of the single-family expected crossings against each
    family. The families' *orientations* do not enter: each single-family term is the
    orientation-free quantity `N.expectedCrossings (d j)` (see the module docstring).

    Declared in the `BuffonsNoodle` namespace (alongside the parent's
    `expectedGridCrossings`) so that dot-notation `N.expectedMultiCrossings` resolves. -/
noncomputable def PolygonalNoodle.expectedMultiCrossings {n k : ℕ}
    (N : PolygonalNoodle n) (d : Fin k → ℝ) : ℝ :=
  ∑ j, N.expectedCrossings (d j)

end BuffonsNoodle

namespace BuffonsNoodleOQ01OQ02

/-- Additivity of expectation across families, made definitionally explicit
    (the `k`-family analogue of the parent's `buffon_noodle_grid_eq_sum`). -/
theorem expectedMultiCrossings_eq_sum {n k : ℕ} (N : PolygonalNoodle n) (d : Fin k → ℝ) :
    N.expectedMultiCrossings d = ∑ j, N.expectedCrossings (d j) := rfl

/- ============================================================
   § 2 : The general Buffon–Laplace formula
   ============================================================ -/

/-- **General Buffon–Laplace theorem (`k` families).**

For a polygonal noodle `N` of total length `L` and `k` families of parallel lines with
positive spacings `d₁, …, d_k`, the expected total number of crossings is

`E[crossings] = (2L/π) · Σ_j 1/d_j`,

depending only on the total length and the spacings — not on the noodle's shape, nor on
the families' orientations. The proof rewrites each family's contribution with the
parent single-family theorem `buffon_noodle_polygon` and sums by linearity. -/
theorem buffon_noodle_multi_family {n k : ℕ} (N : PolygonalNoodle n) (d : Fin k → ℝ)
    (hd : ∀ j, 0 < d j) :
    N.expectedMultiCrossings d = 2 * N.totalLength / π * ∑ j, (d j)⁻¹ := by
  rw [PolygonalNoodle.expectedMultiCrossings, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [buffon_noodle_polygon N (d j) (hd j)]
  have hdj : d j ≠ 0 := (hd j).ne'
  have hpi : π ≠ 0 := Real.pi_ne_zero
  field_simp

/- ============================================================
   § 3 : Specializations and structural properties
   ============================================================ -/

/-- **Recovery of the two-family grid.** The parent's perpendicular grid expectation is
    the `k = 2` case of the multi-family count, with spacings `![dh, dv]`. -/
theorem expectedGridCrossings_eq_multi {n : ℕ} (N : PolygonalNoodle n) (dh dv : ℝ) :
    N.expectedGridCrossings dh dv = N.expectedMultiCrossings ![dh, dv] := by
  simp [PolygonalNoodle.expectedGridCrossings, PolygonalNoodle.expectedMultiCrossings,
    Fin.sum_univ_two]

/-- **Equal spacings.** For `k` families all of spacing `d`, the expected crossings are
    `2kL/(π·d)` — the count scales linearly in the number of families. -/
theorem buffon_noodle_multi_family_const {n k : ℕ} (N : PolygonalNoodle n) (d : ℝ)
    (hd : 0 < d) :
    N.expectedMultiCrossings (fun _ : Fin k => d) = 2 * k * N.totalLength / (π * d) := by
  rw [buffon_noodle_multi_family N _ (fun _ => hd)]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hd' : d ≠ 0 := hd.ne'
  have hpi : π ≠ 0 := Real.pi_ne_zero
  field_simp

/-- The multi-family expected-crossing count is nonnegative. -/
theorem buffon_noodle_multi_family_nonneg {n k : ℕ} (N : PolygonalNoodle n)
    (d : Fin k → ℝ) (hd : ∀ j, 0 < d j) :
    0 ≤ N.expectedMultiCrossings d := by
  rw [buffon_noodle_multi_family N d hd]
  apply mul_nonneg
  · exact div_nonneg (by have := N.totalLength_nonneg; linarith) (le_of_lt Real.pi_pos)
  · exact Finset.sum_nonneg fun j _ => le_of_lt (inv_pos.mpr (hd j))

/-- **Monotonicity in the family set.** Adding more families (over a larger index set
    via an injection) can only increase the expected number of crossings, since every
    single-family term is nonnegative. Stated for the canonical inclusion
    `Fin k ↪ Fin (k + m)` of the first `k` families. -/
theorem buffon_noodle_multi_family_mono {n k m : ℕ} (N : PolygonalNoodle n)
    (d : Fin (k + m) → ℝ) (hd : ∀ j, 0 < d j) :
    N.expectedMultiCrossings (fun j : Fin k => d (Fin.castAdd m j))
      ≤ N.expectedMultiCrossings d := by
  rw [buffon_noodle_multi_family N _ (fun j => hd (Fin.castAdd m j)),
      buffon_noodle_multi_family N d hd]
  have hbase : 0 ≤ 2 * N.totalLength / π :=
    div_nonneg (by have := N.totalLength_nonneg; linarith) (le_of_lt Real.pi_pos)
  apply mul_le_mul_of_nonneg_left _ hbase
  -- `Σ_{j : Fin k} 1/d(castAdd j) ≤ Σ_{j : Fin (k+m)} 1/d j`: a subsum of nonneg terms
  rw [Fin.sum_univ_add]
  have : 0 ≤ ∑ j : Fin m, (d (Fin.natAdd k j))⁻¹ :=
    Finset.sum_nonneg fun j _ => le_of_lt (inv_pos.mpr (hd _))
  linarith

/- ============================================================
   § 4 : Worked instances
   ============================================================ -/

section Examples

variable {n : ℕ} (N : PolygonalNoodle n)

/-- Three families with spacings `1, 2, 3`: expected crossings `(2L/π)(1 + 1/2 + 1/3)`. -/
example :
    N.expectedMultiCrossings ![(1 : ℝ), 2, 3]
      = 2 * N.totalLength / π * (1 + 2⁻¹ + 3⁻¹) := by
  rw [buffon_noodle_multi_family N _ (by
    intro j; fin_cases j <;> norm_num)]
  simp [Fin.sum_univ_three]

/-- A square grid (`k = 2`, equal spacing `d`) gives `4L/(πd)`, matching the parent. -/
example (d : ℝ) (hd : 0 < d) :
    N.expectedMultiCrossings (fun _ : Fin 2 => d) = 4 * N.totalLength / (π * d) := by
  rw [buffon_noodle_multi_family_const (k := 2) N d hd]; push_cast; ring

end Examples

end BuffonsNoodleOQ01OQ02
