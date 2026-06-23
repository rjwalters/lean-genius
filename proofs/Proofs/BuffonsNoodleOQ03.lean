import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Tactic

/-!
# Buffon's Noodle in Higher Dimensions (oq-03)

## What This Proves

The parent entry `BuffonsNoodle.lean` proves the **planar** Buffon–Barbier noodle
theorem: a rectifiable curve of total length `L` dropped on a floor ruled with
parallel lines spaced `d` apart has expected crossing count `2L/(πd)`, depending
only on the length and not on the shape.

This file generalises the *shape-independence / linearity* phenomenon to **all
dimensions**. In `ℝⁿ`, drop the curve at a uniformly random orientation and count
crossings with a family of parallel **hyperplanes** spaced `d` apart. The expected
number of crossings is

$$E[\text{crossings}] = \frac{\alpha_n \, L}{d},$$

where `L` is the total length and

$$\alpha_n = \mathbb{E}_{u \sim S^{n-1}}\,|u_1|$$

is the **dimension's crossing factor** — the mean absolute value of one coordinate
of a uniformly random unit vector. Concretely `α₂ = 2/π` (recovering the planar
formula `2L/(πd)`) and `α₃ = 1/2`, with the spherical recurrence
`α_{n+2} = (n/(n+1))·α_n`.

## Why this is the right generalisation

For a single straight segment of length `ℓ` with direction `u ∈ S^{n-1}`, its extent
along the axis perpendicular to the hyperplanes is `ℓ·|u₁|`. Against hyperplanes
spaced `d` apart with a uniform random offset, the conditional expected number of
crossings is `ℓ·|u₁|/d`; averaging over the orientation gives `ℓ·α_n/d`. Linearity
of expectation then sums over the segments of a polygonal noodle, so the total
depends only on the total length — *in every dimension*. This file makes that
algebraic backbone precise and 0-axiom: the per-segment crossing factor `α` is
carried as a parameter, and every structural law (shape independence, additivity,
scaling, monotonicity, Lipschitz continuity, approximation limit, the dimensional
recurrence transfer, and concrete planar/spatial circle values) is derived from it.

The crossing factor `α_n` itself is the expectation of a spherical integral, whose
evaluation belongs to the needle-side files (`BuffonsNeedleOQ02OQ02OQ01` and
relatives); here we treat it as a nonnegative real parameter, which is exactly the
honest separation of concerns: *given* the dimension's crossing factor, the noodle
law is a theorem.

## Status

- [x] Higher-dimensional noodle theorem (`E = α·L/d`), parametric in the crossing factor
- [x] Shape independence in every dimension
- [x] Additivity / scaling / monotonicity / strict monotonicity / Lipschitz bound
- [x] Approximation limit (polygonal → smooth) in every dimension
- [x] Dimensional recurrence transfer `α_{n+2} = (n/(n+1))α_n ⟹ E_{n+2} = (n/(n+1))E_n`
- [x] Planar recovery `α=2/π ⟹ 2L/(πd)` and spatial circle `α=1/2`
- [x] 3D-to-2D crossing ratio `= π/4`, independent of the noodle
-/

namespace BuffonsNoodleHighDim

open Real Finset BigOperators

/-! ## Part I: The per-segment crossing count in dimension `n`

For a straight segment of length `ℓ` dropped at uniform orientation in `ℝⁿ`, the
expected number of crossings with hyperplanes spaced `d` apart is `α·ℓ/d`, where
`α = α_n = E_{S^{n-1}}|u₁|` is the dimension's crossing factor. We carry `α` as a
parameter. -/

/-- Expected crossings of a single segment of length `ℓ` in a dimension whose
    crossing factor is `α`, against hyperplanes spaced `d` apart: `α·ℓ/d`. -/
noncomputable def segmentCrossings (α ℓ d : ℝ) : ℝ := α * ℓ / d

/-- The per-segment crossing count scales linearly in the segment length. -/
theorem segmentCrossings_linear (α ℓ d c : ℝ) :
    segmentCrossings α (c * ℓ) d = c * segmentCrossings α ℓ d := by
  simp only [segmentCrossings]; ring

/-- A zero-length segment never crosses. -/
theorem segmentCrossings_zero (α d : ℝ) : segmentCrossings α 0 d = 0 := by
  simp [segmentCrossings]

/-- The per-segment crossing count is nonnegative for a nonnegative crossing
    factor, nonnegative length, and positive spacing. -/
theorem segmentCrossings_nonneg (α ℓ d : ℝ) (hα : 0 ≤ α) (hℓ : 0 ≤ ℓ) (hd : 0 < d) :
    0 ≤ segmentCrossings α ℓ d := by
  unfold segmentCrossings
  exact div_nonneg (mul_nonneg hα hℓ) hd.le

/-! ## Part II: Polygonal noodles in dimension `n`

A polygonal noodle is a finite sequence of straight segments with given lengths.
Exactly as in the planar parent, the structure records only the lengths — the
orientations are integrated out into the crossing factor `α`. -/

/-- A polygonal noodle with `n` segments, recorded by their lengths. -/
structure Noodle (n : ℕ) where
  /-- Length of each segment. -/
  segLen : Fin n → ℝ
  /-- All segment lengths are nonnegative. -/
  nonneg : ∀ i, 0 ≤ segLen i

/-- Total length of a noodle. -/
noncomputable def Noodle.totalLength {n : ℕ} (N : Noodle n) : ℝ :=
  ∑ i : Fin n, N.segLen i

/-- The total length is nonnegative. -/
theorem Noodle.totalLength_nonneg {n : ℕ} (N : Noodle n) : 0 ≤ N.totalLength :=
  Finset.sum_nonneg fun i _ => N.nonneg i

/-- Expected total crossings of a noodle in a dimension with crossing factor `α`. -/
noncomputable def Noodle.expectedCrossings {n : ℕ} (N : Noodle n) (α d : ℝ) : ℝ :=
  ∑ i : Fin n, segmentCrossings α (N.segLen i) d

/-! ## Part III: The higher-dimensional noodle theorem

The expected number of crossings equals `α·L/d`, where `L` is the total length:
it depends only on the length and the dimension's crossing factor, not on the
arrangement of the segments. The proof is the same linearity argument as the
planar case, now with a general `α`. -/

/-- **Buffon's Noodle Theorem (higher-dimensional, polygonal case).**

For a noodle `N` of total length `L = L₁ + ⋯ + Lₙ` dropped at uniform orientation
in a dimension whose crossing factor is `α`, the expected number of crossings with
parallel hyperplanes spaced `d` apart is `α·L/d`. -/
theorem noodle_highdim {n : ℕ} (N : Noodle n) (α d : ℝ) :
    N.expectedCrossings α d = α * N.totalLength / d := by
  simp only [Noodle.expectedCrossings, Noodle.totalLength, segmentCrossings]
  have hrw : ∀ i : Fin n, α * N.segLen i / d = α / d * N.segLen i := fun i => by ring
  simp_rw [hrw, ← Finset.mul_sum]
  ring

/-! ## Part IV: Shape independence and structural laws -/

/-- **Shape independence (any dimension).** Two noodles of equal total length have
    equal expected crossings, regardless of shape — in every dimension. -/
theorem shape_independence {m n : ℕ} (N₁ : Noodle m) (N₂ : Noodle n) (α d : ℝ)
    (hSameLength : N₁.totalLength = N₂.totalLength) :
    N₁.expectedCrossings α d = N₂.expectedCrossings α d := by
  rw [noodle_highdim, noodle_highdim, hSameLength]

/-- **Additivity.** A noodle of total length `L₁ + L₂` has expected crossings equal
    to the sum of the expected crossings of its two parts (linearity of expectation). -/
theorem additive {m n : ℕ} (N₁ : Noodle m) (N₂ : Noodle n) (α d : ℝ) :
    α * (N₁.totalLength + N₂.totalLength) / d =
      N₁.expectedCrossings α d + N₂.expectedCrossings α d := by
  rw [noodle_highdim, noodle_highdim]; ring

/-- **Scaling.** Scaling every segment length by `c ≥ 0` scales the expected
    crossings by `c`. -/
theorem scaling {n : ℕ} (N : Noodle n) (α d c : ℝ) (hc : 0 ≤ c) :
    let scaled : Noodle n :=
      { segLen := fun i => c * N.segLen i
        nonneg := fun i => mul_nonneg hc (N.nonneg i) }
    scaled.expectedCrossings α d = c * N.expectedCrossings α d := by
  simp only [Noodle.expectedCrossings, segmentCrossings, Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro i _
  ring

/-- The expected crossing count is nonnegative for a nonnegative crossing factor
    and positive spacing. -/
theorem expectedCrossings_nonneg {n : ℕ} (N : Noodle n) (α d : ℝ)
    (hα : 0 ≤ α) (hd : 0 < d) : 0 ≤ N.expectedCrossings α d := by
  rw [noodle_highdim]
  exact div_nonneg (mul_nonneg hα N.totalLength_nonneg) hd.le

/-- **Monotonicity.** A longer noodle has at least as many expected crossings
    (`α ≥ 0`, `d > 0`). -/
theorem expectedCrossings_mono {m n : ℕ} (N₁ : Noodle m) (N₂ : Noodle n) (α d : ℝ)
    (hα : 0 ≤ α) (hd : 0 < d) (hlen : N₁.totalLength ≤ N₂.totalLength) :
    N₁.expectedCrossings α d ≤ N₂.expectedCrossings α d := by
  rw [noodle_highdim, noodle_highdim]
  gcongr

/-- **Strict monotonicity.** A strictly longer noodle has strictly more expected
    crossings (`α > 0`, `d > 0`). -/
theorem expectedCrossings_strictMono {m n : ℕ} (N₁ : Noodle m) (N₂ : Noodle n)
    (α d : ℝ) (hα : 0 < α) (hd : 0 < d) (hlen : N₁.totalLength < N₂.totalLength) :
    N₁.expectedCrossings α d < N₂.expectedCrossings α d := by
  rw [noodle_highdim, noodle_highdim]
  gcongr

/-- **Lipschitz bound.** The expected crossing count is Lipschitz in the total
    length with constant `α/d`. -/
theorem lipschitz {m n : ℕ} (N₁ : Noodle m) (N₂ : Noodle n) (α d : ℝ)
    (hα : 0 ≤ α) (hd : 0 < d) :
    |N₁.expectedCrossings α d - N₂.expectedCrossings α d|
      ≤ α / d * |N₁.totalLength - N₂.totalLength| :=
  le_of_eq <| by
    rw [noodle_highdim, noodle_highdim,
      show α * N₁.totalLength / d - α * N₂.totalLength / d
          = α / d * (N₁.totalLength - N₂.totalLength) from by ring,
      abs_mul, abs_of_nonneg (div_nonneg hα hd.le)]

/-! ## Part V: Approximation limit (polygonal → smooth)

The bridge from polygonal noodles to smooth curves: if a sequence of polygonal
noodles converges in total length to `L`, the expected crossings converge to
`α·L/d`. This is the dimensional analogue of the planar parent's approximation
theorem, and the justification for why the smooth higher-dimensional case follows
from the polygonal one by continuity. -/

/-- **Approximation Limit (any dimension).** If a sequence of noodles has total
    lengths converging to `L`, their expected crossings converge to `α·L/d`. -/
theorem approx_limit (α d : ℝ)
    (ns : ℕ → ℕ) (N : ∀ k, Noodle (ns k)) (L : ℝ)
    (hConverge : Filter.Tendsto (fun k => (N k).totalLength) Filter.atTop (nhds L)) :
    Filter.Tendsto (fun k => (N k).expectedCrossings α d) Filter.atTop
      (nhds (α * L / d)) := by
  simp_rw [noodle_highdim]
  have hcont : Continuous (fun x : ℝ => α * x / d) :=
    (continuous_const.mul continuous_id).div_const d
  exact hcont.continuousAt.tendsto.comp hConverge

/-! ## Part VI: The dimensional recurrence and concrete values -/

/-- **Dimensional recurrence transfer.** The spherical crossing factors obey
    `α_{n+2} = (n/(n+1))·α_n`. Whenever two dimensions' crossing factors are related
    this way, the expected crossings of *any fixed noodle* transfer by the same
    factor — the curve's shape is irrelevant. -/
theorem recurrence_transfers {n : ℕ} (N : Noodle n) (α α' d : ℝ) (k : ℕ)
    (hrec : α' = (k : ℝ) / (k + 1) * α) :
    N.expectedCrossings α' d = (k : ℝ) / (k + 1) * N.expectedCrossings α d := by
  rw [noodle_highdim, noodle_highdim, hrec]; ring

/-- **Dimensional ratio.** For a fixed noodle of nonzero length, the ratio of
    expected crossings between two dimensions equals the ratio of their crossing
    factors `α/β`, independent of the noodle. -/
theorem dimension_ratio {n : ℕ} (N : Noodle n) (α β d : ℝ)
    (hd : 0 < d) (hβ : β ≠ 0) (hN : N.totalLength ≠ 0) :
    N.expectedCrossings α d / N.expectedCrossings β d = α / β := by
  rw [noodle_highdim, noodle_highdim]
  have hd' : d ≠ 0 := hd.ne'
  field_simp

/-- **Planar recovery.** With the planar crossing factor `α₂ = 2/π`, the
    higher-dimensional formula reduces to the classical Buffon–Barbier value
    `2L/(πd)`. -/
theorem planar_recovers {n : ℕ} (N : Noodle n) (d : ℝ) (hd : 0 < d) :
    N.expectedCrossings (2 / π) d = 2 * N.totalLength / (π * d) := by
  rw [noodle_highdim]
  have hπ : π ≠ 0 := pi_ne_zero
  have hd' : d ≠ 0 := hd.ne'
  field_simp

/-- A planar circle of radius `r` (circumference `2πr`) has expected crossings
    `4r/d` — the parent gallery's value, recovered as the `n = 2` specialisation. -/
theorem planar_circle_crossings (r d : ℝ) (hd : 0 < d) :
    segmentCrossings (2 / π) (2 * π * r) d = 4 * r / d := by
  rw [segmentCrossings]
  have hπ : π ≠ 0 := pi_ne_zero
  have hd' : d ≠ 0 := hd.ne'
  field_simp
  ring

/-- **Spatial circle.** In `ℝ³` (crossing factor `α₃ = 1/2`), a circle of radius `r`
    has expected hyperplane crossings `πr/d`. -/
theorem spatial_circle_crossings (r d : ℝ) :
    segmentCrossings (1 / 2) (2 * π * r) d = π * r / d := by
  rw [segmentCrossings, show (1 : ℝ) / 2 * (2 * π * r) = π * r from by ring]

/-- **3D-to-2D crossing ratio.** For the same noodle (nonzero length), the ratio of
    its expected crossings in `ℝ³` to those in `ℝ²` is `α₃/α₂ = π/4`, independent of
    the noodle's shape. So a curve crosses hyperplanes `π/4 ≈ 0.785` times as often
    in space as it crosses lines in the plane. -/
theorem spatial_to_planar_ratio {n : ℕ} (N : Noodle n) (d : ℝ)
    (hd : 0 < d) (hN : N.totalLength ≠ 0) :
    N.expectedCrossings (1 / 2) d / N.expectedCrossings (2 / π) d = π / 4 := by
  rw [dimension_ratio N (1 / 2) (2 / π) d hd (by positivity) hN]
  have hπ : π ≠ 0 := pi_ne_zero
  field_simp
  ring

end BuffonsNoodleHighDim
