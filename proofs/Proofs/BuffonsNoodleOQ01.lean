import Proofs.BuffonsNoodle
import Mathlib.Tactic

/-!
# Buffon–Laplace for the Polygonal Noodle (Doubly-Ruled Grid)

## What This Proves

This is the **Buffon–Laplace** extension of Buffon's Noodle theorem from a single
family of parallel lines to a *grid* formed by two perpendicular families.

The parent file `Proofs/BuffonsNoodle.lean` proves that a polygonal noodle of total
arc length `L`, dropped on one family of parallel lines with spacing `d`, crosses
them on average

$$\mathbb{E}[\text{crossings}] = \frac{2L}{\pi d}.$$

Here we drop the *same* noodle on a grid of two perpendicular families with spacings
`dₕ` (horizontal) and `dᵥ` (vertical) and count the expected total number of
crossings against **both** families at once:

$$\mathbb{E}[\text{crossings}] = \frac{2L}{\pi d_h} + \frac{2L}{\pi d_v}.$$

In the square-grid case `dₕ = dᵥ = d` this collapses to `4L/(πd)`.

## The Key Insight: Additivity of Expectation Across Families

Total crossings against the grid = (crossings against the horizontal family) +
(crossings against the vertical family). Expectation is **additive** regardless of
dependence — the two crossing counts are highly correlated (they are produced by the
same drop of the same noodle), but $\mathbb{E}[X + Y] = \mathbb{E}[X] + \mathbb{E}[Y]$
needs no independence. So the grid expectation is just the sum of two copies of the
single-family theorem, one per spacing. No new probabilistic content is required;
the result demonstrates that the gallery's `expectedCrossings` /
linearity-of-expectation machinery **composes across independent line families**.

## Why This Matters

Buffon–Laplace is the classical bridge from the one-dimensional needle/noodle
estimate to genuine two-dimensional integral geometry, and is the standard route to
Monte-Carlo estimators of `π` with *reduced variance*: dropping on a grid yields two
crossing tallies per trial rather than one. Solving the square-grid identity for `π`
gives `π = 4L/(d · E)`, formalized below as `pi_times_spacing_mul_grid_crossings`.

## Scope

Polygonal noodles only, reusing `buffon_noodle_polygon` once per family. The
smooth/`C¹` generalization depends on the still-axiomatized kinematic-measure
infrastructure (`smoothExpectedCrossings`) and is out of scope here; this file adds
**no axioms** and has **0 sorries** — every theorem is a corollary of the proved
polygonal theorem in the parent.
-/

namespace BuffonsNoodle

open Real Finset BigOperators

/-- The expected total number of crossings of a polygonal noodle `N` with a
doubly-ruled grid: two perpendicular families of parallel lines with horizontal
spacing `dh` and vertical spacing `dv`. By additivity of expectation it is the sum
of the single-family expected crossings against each family. -/
noncomputable def PolygonalNoodle.expectedGridCrossings {n : ℕ}
    (N : PolygonalNoodle n) (dh dv : ℝ) : ℝ :=
  N.expectedCrossings dh + N.expectedCrossings dv

end BuffonsNoodle

namespace BuffonsNoodleOQ01

open Real Finset BigOperators BuffonsNoodle

/-! ## Part I: The Buffon–Laplace Grid Theorem -/

/-- **Buffon–Laplace Theorem (Polygonal Case).**

For a polygonal noodle `N` of total length `L`, the expected total number of
crossings with a grid of two perpendicular line families (spacings `dh`, `dv`) is

`E[crossings] = 2L/(π·dh) + 2L/(π·dv)`,

depending only on the total length, not on the noodle's shape.

**Proof**: unfold the grid expectation into its two single-family terms and apply the
parent polygonal theorem `buffon_noodle_polygon` once per family. -/
theorem buffon_noodle_grid {n : ℕ} (N : PolygonalNoodle n) (dh dv : ℝ)
    (hdh : 0 < dh) (hdv : 0 < dv) :
    N.expectedGridCrossings dh dv
      = 2 * N.totalLength / (π * dh) + 2 * N.totalLength / (π * dv) := by
  unfold PolygonalNoodle.expectedGridCrossings
  rw [buffon_noodle_polygon N dh hdh, buffon_noodle_polygon N dv hdv]

/-- The grid expectation is, by definition, the sum of the two single-family
expectations — making the "additivity of expectation across families" structure
explicit. -/
theorem buffon_noodle_grid_eq_sum {n : ℕ} (N : PolygonalNoodle n) (dh dv : ℝ) :
    N.expectedGridCrossings dh dv = N.expectedCrossings dh + N.expectedCrossings dv :=
  rfl

/-- **Square-grid specialization.** When both families share the spacing `d`, the
expected total crossings are `4L/(πd)` — exactly double the single-family count. -/
theorem buffon_noodle_square_grid {n : ℕ} (N : PolygonalNoodle n) (d : ℝ)
    (hd : 0 < d) :
    N.expectedGridCrossings d d = 4 * N.totalLength / (π * d) := by
  rw [buffon_noodle_grid N d d hd hd]; ring

/-- On a square grid the expected crossings are exactly twice the single-family
expectation, for any noodle. -/
theorem buffon_noodle_grid_eq_two_mul_single {n : ℕ} (N : PolygonalNoodle n)
    (d : ℝ) :
    N.expectedGridCrossings d d = 2 * N.expectedCrossings d := by
  unfold PolygonalNoodle.expectedGridCrossings; ring

/-! ## Part II: Structural Properties -/

/-- **Shape independence for the grid.** Two polygonal noodles of equal total length
have identical expected grid crossings, whatever their shapes. -/
theorem buffon_noodle_grid_shape_independence {m n : ℕ}
    (N₁ : PolygonalNoodle m) (N₂ : PolygonalNoodle n) (dh dv : ℝ)
    (hdh : 0 < dh) (hdv : 0 < dv)
    (hSameLength : N₁.totalLength = N₂.totalLength) :
    N₁.expectedGridCrossings dh dv = N₂.expectedGridCrossings dh dv := by
  rw [buffon_noodle_grid N₁ dh dv hdh hdv, buffon_noodle_grid N₂ dh dv hdh hdv,
      hSameLength]

/-- The grid expected-crossing count is nonneg for any noodle and positive
spacings. -/
theorem buffon_noodle_grid_nonneg {n : ℕ} (N : PolygonalNoodle n) (dh dv : ℝ)
    (hdh : 0 < dh) (hdv : 0 < dv) :
    0 ≤ N.expectedGridCrossings dh dv := by
  rw [buffon_noodle_grid N dh dv hdh hdv]
  have hL : 0 ≤ N.totalLength := N.totalLength_nonneg
  have h1 : 0 ≤ 2 * N.totalLength / (π * dh) := by
    apply div_nonneg (by linarith); positivity
  have h2 : 0 ≤ 2 * N.totalLength / (π * dv) := by
    apply div_nonneg (by linarith); positivity
  linarith

/-- **Monotonicity in length.** A longer noodle has at least as many expected grid
crossings. -/
theorem buffon_noodle_grid_mono {m n : ℕ}
    (N₁ : PolygonalNoodle m) (N₂ : PolygonalNoodle n) (dh dv : ℝ)
    (hdh : 0 < dh) (hdv : 0 < dv)
    (hlen : N₁.totalLength ≤ N₂.totalLength) :
    N₁.expectedGridCrossings dh dv ≤ N₂.expectedGridCrossings dh dv := by
  rw [buffon_noodle_grid N₁ dh dv hdh hdv, buffon_noodle_grid N₂ dh dv hdh hdv]
  have hdh0 : (0 : ℝ) < π * dh := by positivity
  have hdv0 : (0 : ℝ) < π * dv := by positivity
  have t1 : 2 * N₁.totalLength / (π * dh) ≤ 2 * N₂.totalLength / (π * dh) := by
    rw [div_le_div_right hdh0]; linarith
  have t2 : 2 * N₁.totalLength / (π * dv) ≤ 2 * N₂.totalLength / (π * dv) := by
    rw [div_le_div_right hdv0]; linarith
  linarith

/-! ## Part III: The Monte-Carlo π Estimator

Solving the square-grid identity `E = 4L/(πd)` for `π` gives `π = 4L/(d·E)`. The
clean multiplicative form below avoids any nondegeneracy hypothesis on `E`. -/

/-- **π from a square-grid noodle drop.** On a square grid of spacing `d`, the
expected crossings `E` satisfy `π · d · E = 4L`, i.e. `π = 4L/(d·E)` whenever the
noodle has positive length. This is the variance-reduced Buffon–Laplace estimator of
`π`. -/
theorem pi_times_spacing_mul_grid_crossings {n : ℕ} (N : PolygonalNoodle n) (d : ℝ)
    (hd : 0 < d) :
    π * d * N.expectedGridCrossings d d = 4 * N.totalLength := by
  rw [buffon_noodle_square_grid N d hd]
  have hπ : π ≠ 0 := pi_ne_zero
  have hd' : d ≠ 0 := hd.ne'
  field_simp
  ring

/-! ## Part IV: Numerical Examples -/

/-- A circle of circumference `2πr` (modelled as a one-segment noodle) on a square
grid of spacing `d` has expected crossings `8r/d` — *independent of `π`*, exactly
double the single-family value `4r/d`. A clean sanity check of the `2L/(πd)` law. -/
theorem circle_grid_crossings (r d : ℝ) (hr : 0 < r) (hd : 0 < d) :
    let circ : PolygonalNoodle 1 :=
      { segLen := fun _ => 2 * π * r
        nonneg := fun _ => by positivity }
    circ.expectedGridCrossings d d = 8 * r / d := by
  simp only [PolygonalNoodle.expectedGridCrossings, PolygonalNoodle.expectedCrossings,
             segmentCrossingProb, Fin.sum_univ_one]
  have hπ : π ≠ 0 := pi_ne_zero
  have hd' : d ≠ 0 := hd.ne'
  field_simp
  ring

/-- A square of side `s` (perimeter `4s`, a four-segment noodle) on a square grid of
spacing `d` has expected crossings `16s/(πd)` — twice the single-family `8s/(πd)`. -/
theorem square_grid_crossings (s d : ℝ) (hs : 0 < s) (hd : 0 < d) :
    let sq : PolygonalNoodle 4 :=
      { segLen := fun _ => s
        nonneg := fun _ => hs.le }
    sq.expectedGridCrossings d d = 16 * s / (π * d) := by
  simp only [PolygonalNoodle.expectedGridCrossings, PolygonalNoodle.expectedCrossings,
             segmentCrossingProb, Fin.sum_univ_four]
  ring

/-- A rectangular grid with `dh ≠ dv` genuinely distinguishes the two families: the
circle's expected crossings are `4r·(1/dh + 1/dv)`, recovering `8r/d` only when the
grid is square. -/
theorem circle_rect_grid_crossings (r dh dv : ℝ) (hr : 0 < r) (hdh : 0 < dh)
    (hdv : 0 < dv) :
    let circ : PolygonalNoodle 1 :=
      { segLen := fun _ => 2 * π * r
        nonneg := fun _ => by positivity }
    circ.expectedGridCrossings dh dv = 4 * r / dh + 4 * r / dv := by
  simp only [PolygonalNoodle.expectedGridCrossings, PolygonalNoodle.expectedCrossings,
             segmentCrossingProb, Fin.sum_univ_one]
  have hπ : π ≠ 0 := pi_ne_zero
  have hdh' : dh ≠ 0 := hdh.ne'
  have hdv' : dv ≠ 0 := hdv.ne'
  field_simp
  ring

end BuffonsNoodleOQ01
