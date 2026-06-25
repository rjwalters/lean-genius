import Proofs.BuffonsNoodleOQ01
import Mathlib.Tactic

/-!
# Buffon–Laplace for the Smooth/C¹ Noodle (Doubly-Ruled Grid)

## What This Proves

This is the **smooth/C¹ generalization** of the Buffon–Laplace grid identity. The
sibling file `Proofs/BuffonsNoodleOQ01.lean` proves the grid law for *polygonal*
noodles,

$$\mathbb{E}[\text{crossings}] = \frac{2L}{\pi d_h} + \frac{2L}{\pi d_v},$$

as a corollary of the proved polygonal single-family theorem `buffon_noodle_polygon`.
Here we establish the *same* identity for an arbitrary `C¹` planar curve `γ` dropped on
a grid of two perpendicular line families with spacings `dₕ` and `dᵥ`, with `L` now the
**arc length** `planarCurveArcLength γ a b`.

## How It Relates to the Parent Axioms

The smooth single-family theory is the *kinematic-measure* layer of the parent file
`Proofs/BuffonsNoodle.lean`. There the primitive

```
noncomputable axiom smoothExpectedCrossings (γ : ℝ → ℝ × ℝ) (a b d : ℝ) : ℝ
```

and the **Buffon–Barbier** law

```
axiom buffon_noodle_smooth_eq … : smoothExpectedCrossings γ a b d
                                    = 2 * planarCurveArcLength γ a b / (π * d)
```

are *assumed* (their honest proof needs the Cauchy–Crofton formula and a kinematic
measure on the space of lines — substantial integral-geometry infrastructure not yet in
Mathlib). **This file introduces no new axioms.** Every result below is derived purely
from those two parent axioms by the *additivity of expectation across families*:

$$\text{(grid crossings)} = \text{(crossings vs.\ horizontal)} + \text{(crossings vs.\ vertical)},$$

an identity that needs no independence — the two tallies come from the *same* drop of the
*same* curve and are highly correlated, yet `𝔼[X+Y] = 𝔼[X] + 𝔼[Y]` regardless. So the
smooth grid expectation is the sum of two copies of the smooth Barbier law, one per
spacing. This is exactly the smooth analogue of the polygonal `buffon_noodle_grid`,
showing the kinematic-measure functional **composes across line families** in the same way
the elementary `expectedCrossings` does.

## Status

Conditional on the parent's kinematic-measure axioms `smoothExpectedCrossings` and
`buffon_noodle_smooth_eq`. No new axioms, **0 sorries**; every theorem is a corollary of
the assumed smooth single-family law.
-/

namespace BuffonsNoodle

open Real

/-- The expected total number of crossings of a smooth `C¹` curve `γ` on `[a,b]` with a
doubly-ruled grid: two perpendicular families of parallel lines with horizontal spacing
`dh` and vertical spacing `dv`. By additivity of expectation it is the sum of the
single-family smooth expected crossings against each family. -/
noncomputable def smoothExpectedGridCrossings (γ : ℝ → ℝ × ℝ) (a b dh dv : ℝ) : ℝ :=
  smoothExpectedCrossings γ a b dh + smoothExpectedCrossings γ a b dv

end BuffonsNoodle

namespace BuffonsNoodleOQ01OQ01

open Real BuffonsNoodle

/-! ## Part I: The Smooth Buffon–Laplace Grid Theorem -/

/-- **Buffon–Laplace Theorem (Smooth/C¹ Case).**

For a `C¹` curve `γ` on `[a,b]` of arc length `L = planarCurveArcLength γ a b`, the
expected total number of crossings with a grid of two perpendicular line families
(spacings `dh`, `dv`) is

`E[crossings] = 2L/(π·dh) + 2L/(π·dv)`,

depending only on the arc length, not on the curve's shape.

**Proof**: unfold the smooth grid expectation into its two single-family terms and apply
the parent smooth Barbier law `buffon_noodle_smooth_eq` once per family. -/
theorem buffon_noodle_smooth_grid (γ : ℝ → ℝ × ℝ) (a b dh dv : ℝ)
    (hdh : 0 < dh) (hdv : 0 < dv) (hab : a ≤ b) (hC1 : ContDiff ℝ 1 γ) :
    smoothExpectedGridCrossings γ a b dh dv
      = 2 * planarCurveArcLength γ a b / (π * dh)
        + 2 * planarCurveArcLength γ a b / (π * dv) := by
  unfold smoothExpectedGridCrossings
  rw [buffon_noodle_smooth_eq γ a b dh hdh hab hC1,
      buffon_noodle_smooth_eq γ a b dv hdv hab hC1]

/-- The smooth grid expectation is, by definition, the sum of the two single-family
smooth expectations — making the "additivity of expectation across families" structure
explicit, with no independence assumed. -/
theorem buffon_noodle_smooth_grid_eq_sum (γ : ℝ → ℝ × ℝ) (a b dh dv : ℝ) :
    smoothExpectedGridCrossings γ a b dh dv
      = smoothExpectedCrossings γ a b dh + smoothExpectedCrossings γ a b dv :=
  rfl

/-- **Square-grid specialization.** When both families share the spacing `d`, the smooth
expected total crossings are `4L/(πd)` — exactly double the single-family count. -/
theorem buffon_noodle_smooth_square_grid (γ : ℝ → ℝ × ℝ) (a b d : ℝ)
    (hd : 0 < d) (hab : a ≤ b) (hC1 : ContDiff ℝ 1 γ) :
    smoothExpectedGridCrossings γ a b d d
      = 4 * planarCurveArcLength γ a b / (π * d) := by
  rw [buffon_noodle_smooth_grid γ a b d d hd hd hab hC1]; ring

/-- On a square grid the smooth expected crossings are exactly twice the single-family
expectation, for any `C¹` curve — this needs neither `hC1` nor positivity since it is the
definitional sum collapsed at `dh = dv`. -/
theorem buffon_noodle_smooth_grid_eq_two_mul_single (γ : ℝ → ℝ × ℝ) (a b d : ℝ) :
    smoothExpectedGridCrossings γ a b d d = 2 * smoothExpectedCrossings γ a b d := by
  unfold smoothExpectedGridCrossings; ring

/-! ## Part II: Structural Properties -/

/-- **Shape independence for the smooth grid.** Two `C¹` curves of equal arc length have
identical expected grid crossings, whatever their shapes. -/
theorem buffon_noodle_smooth_grid_shape_independence
    (γ₁ γ₂ : ℝ → ℝ × ℝ) (a₁ b₁ a₂ b₂ dh dv : ℝ)
    (hdh : 0 < dh) (hdv : 0 < dv) (h1 : a₁ ≤ b₁) (h2 : a₂ ≤ b₂)
    (hC1₁ : ContDiff ℝ 1 γ₁) (hC1₂ : ContDiff ℝ 1 γ₂)
    (hSameLen : planarCurveArcLength γ₁ a₁ b₁ = planarCurveArcLength γ₂ a₂ b₂) :
    smoothExpectedGridCrossings γ₁ a₁ b₁ dh dv
      = smoothExpectedGridCrossings γ₂ a₂ b₂ dh dv := by
  rw [buffon_noodle_smooth_grid γ₁ a₁ b₁ dh dv hdh hdv h1 hC1₁,
      buffon_noodle_smooth_grid γ₂ a₂ b₂ dh dv hdh hdv h2 hC1₂, hSameLen]

/-- The smooth grid expected-crossing count is nonneg for any `C¹` curve and positive
spacings. -/
theorem buffon_noodle_smooth_grid_nonneg (γ : ℝ → ℝ × ℝ) (a b dh dv : ℝ)
    (hdh : 0 < dh) (hdv : 0 < dv) (hab : a ≤ b) (hC1 : ContDiff ℝ 1 γ) :
    0 ≤ smoothExpectedGridCrossings γ a b dh dv := by
  rw [buffon_noodle_smooth_grid γ a b dh dv hdh hdv hab hC1]
  have hL : 0 ≤ planarCurveArcLength γ a b := planarCurveArcLength_nonneg γ a b hab
  have h1 : 0 ≤ 2 * planarCurveArcLength γ a b / (π * dh) := by
    apply div_nonneg (by linarith); positivity
  have h2 : 0 ≤ 2 * planarCurveArcLength γ a b / (π * dv) := by
    apply div_nonneg (by linarith); positivity
  linarith

/-- **Monotonicity in arc length.** A longer `C¹` curve has at least as many expected grid
crossings. -/
theorem buffon_noodle_smooth_grid_mono
    (γ₁ γ₂ : ℝ → ℝ × ℝ) (a₁ b₁ a₂ b₂ dh dv : ℝ)
    (hdh : 0 < dh) (hdv : 0 < dv) (h1 : a₁ ≤ b₁) (h2 : a₂ ≤ b₂)
    (hC1₁ : ContDiff ℝ 1 γ₁) (hC1₂ : ContDiff ℝ 1 γ₂)
    (hlen : planarCurveArcLength γ₁ a₁ b₁ ≤ planarCurveArcLength γ₂ a₂ b₂) :
    smoothExpectedGridCrossings γ₁ a₁ b₁ dh dv
      ≤ smoothExpectedGridCrossings γ₂ a₂ b₂ dh dv := by
  rw [buffon_noodle_smooth_grid γ₁ a₁ b₁ dh dv hdh hdv h1 hC1₁,
      buffon_noodle_smooth_grid γ₂ a₂ b₂ dh dv hdh hdv h2 hC1₂]
  have hπh : (0:ℝ) < π * dh := mul_pos pi_pos hdh
  have hπv : (0:ℝ) < π * dv := mul_pos pi_pos hdv
  have t1 : 2 * planarCurveArcLength γ₁ a₁ b₁ / (π * dh)
              ≤ 2 * planarCurveArcLength γ₂ a₂ b₂ / (π * dh) := by gcongr
  have t2 : 2 * planarCurveArcLength γ₁ a₁ b₁ / (π * dv)
              ≤ 2 * planarCurveArcLength γ₂ a₂ b₂ / (π * dv) := by gcongr
  linarith

/-! ## Part III: The Monte-Carlo π Estimator (Smooth Variance-Reduced Form)

Solving the smooth square-grid identity `E = 4L/(πd)` for `π` gives `π = 4L/(d·E)`. The
clean multiplicative form below avoids any nondegeneracy hypothesis on `E`. Dropping a
`C¹` curve on a *grid* gives two crossing tallies per trial, the smooth analogue of the
variance-reduced Buffon–Laplace estimator. -/

/-- **π from a smooth square-grid drop.** On a square grid of spacing `d`, the expected
crossings `E` of a `C¹` curve of arc length `L` satisfy `π · d · E = 4L`, i.e.
`π = 4L/(d·E)` whenever the curve has positive length. -/
theorem pi_times_spacing_mul_smooth_grid_crossings (γ : ℝ → ℝ × ℝ) (a b d : ℝ)
    (hd : 0 < d) (hab : a ≤ b) (hC1 : ContDiff ℝ 1 γ) :
    π * d * smoothExpectedGridCrossings γ a b d d
      = 4 * planarCurveArcLength γ a b := by
  rw [buffon_noodle_smooth_square_grid γ a b d hd hab hC1]
  have hπ : π ≠ 0 := pi_ne_zero
  have hd' : d ≠ 0 := hd.ne'
  field_simp

/-! ## Part IV: Consistency with the Polygonal Grid Law

The smooth grid law degenerates to the polygonal one in the precise sense that *both* are
the sum, over the two families, of a single-family `2L/(πd)` term. The following identity
makes the shared algebraic skeleton explicit: a smooth curve and a polygonal noodle with
the **same total length** have equal grid expectations. -/

/-- **Smooth/polygonal agreement at equal length.** A `C¹` curve `γ` of arc length `L` and
a polygonal noodle `N` of the same total length `L` have identical expected grid
crossings. This bridges the kinematic-measure (smooth) layer and the elementary
(polygonal) layer of the theory: both equal `2L/(π·dh) + 2L/(π·dv)`. -/
theorem buffon_noodle_smooth_eq_polygonal_grid {n : ℕ}
    (γ : ℝ → ℝ × ℝ) (a b : ℝ) (N : BuffonsNoodle.PolygonalNoodle n) (dh dv : ℝ)
    (hdh : 0 < dh) (hdv : 0 < dv) (hab : a ≤ b) (hC1 : ContDiff ℝ 1 γ)
    (hLen : planarCurveArcLength γ a b = N.totalLength) :
    smoothExpectedGridCrossings γ a b dh dv = N.expectedGridCrossings dh dv := by
  rw [buffon_noodle_smooth_grid γ a b dh dv hdh hdv hab hC1,
      BuffonsNoodleOQ01.buffon_noodle_grid N dh dv hdh hdv, hLen]

end BuffonsNoodleOQ01OQ01
