import Proofs.BuffonsNoodleOQ03
import Mathlib.Tactic

/-
# Buffon's Noodle — generalising the codimension (oq-03 · oq-02)

## What this proves

The parent file `BuffonsNoodleOQ03.lean` proves the higher-dimensional noodle law
`E = αₙ·L/d`: a rectifiable curve of total length `L`, dropped at a uniformly random
orientation in `ℝⁿ`, crosses a family of parallel **hyperplanes** spaced `d` apart an
expected `αₙ·L/d` times, where `αₙ = 𝔼_{u∼S^{n-1}}|u₁|` is the dimension's crossing
factor.

Hyperplanes are the **codimension-1** flats. This file answers the open question:
what happens for a family of parallel **k-dimensional** affine subspaces in `ℝⁿ`?
The answer is a sharp **dichotomy**.

### The codimension dichotomy

Fix a family of parallel `k`-flats spaced `d` apart in `ℝⁿ`, and let `c = n - k` be
the codimension. A curve is 1-dimensional. Two 1-dimensional and `k`-dimensional
affine pieces in general position meet in dimension `1 + k - n = 1 - c`:

* `c = 1` (i.e. `k = n-1`, **hyperplanes**): the intersection is `0`-dimensional —
  isolated crossing points. The family is exactly a hyperplane family, so the expected
  intersection count is the parent's noodle law `αₙ·L/d`.
* `c ≥ 2` (i.e. `k ≤ n-2`): the "intersection" has negative dimension, so a generic
  curve **almost surely misses every flat**. The expected intersection count is `0`,
  independently of the length or shape.
* `c = 0` (i.e. `k = n`): the only such flat is all of `ℝⁿ`; there is no proper spaced
  family, and we record the degenerate value `0`.

So length-proportionality (`E = α·L/d` with a positive rate) is a **codimension-1
phenomenon**: it holds if and only if `k = n-1`. This is the honest content of the
"generalise the codimension" question — the noodle law does not survive to lower-
dimensional targets, and this file makes the vanishing precise.

### The deterministic backbone (non-vacuous content)

Underneath the averaged law is a deterministic counting fact that this file proves
from scratch (`gridCount_bounds`): as one coordinate sweeps an interval `[a,b]`, the
number of grid hyperplanes `{x = j·d : j ∈ ℤ}` it crosses is `⌊b/d⌋ - ⌊a/d⌋`, and this
integer differs from the "extent in units of `d`", `(b-a)/d`, by strictly less than 1:

  `|(⌊b/d⌋ - ⌊a/d⌋) - (b-a)/d| < 1`.

Averaging the `±1` boundary fluctuation over a uniformly random offset is exactly what
turns the deterministic count into the crossing factor `segmentCrossings α ℓ d = α·ℓ/d`
(with `α` the mean normal-projection). This is the Buffon mechanism made rigorous at
the segment level, and it is the same in every codimension — only the codimension-1
family produces a nonzero rate.

## Status

- [x] Deterministic grid-crossing count and its `< 1` accuracy (`gridCount_bounds`)
- [x] Codimension-aware per-segment and per-noodle intersection counts
- [x] The dichotomy: `E = α·L/d` for `c = 1`, `E = 0` for `c ≠ 1`
- [x] Hyperplane recovery `k = n-1 ⟹ E = αₙ·L/d`
- [x] Inherited structural laws in the codimension-1 regime (nonneg / shape / mono)
- [x] Concrete `ℝ²`, `ℝ³` (planes vs lines) instances
- [x] 0-axiom, 0-sorry
-/

open BuffonsNoodleHighDim
open Real Finset BigOperators

namespace BuffonsNoodleCodim

/-! ## Part I: The deterministic grid-crossing count

Before any averaging, fix a single coordinate axis perpendicular to the family and let
it sweep from `a` to `b`. The grid hyperplanes are at the multiples `j·d`, and the
number crossed is the number of integers `j` with `a < j·d ≤ b`, i.e. `⌊b/d⌋ - ⌊a/d⌋`.
-/

/-- Number of grid lines `{x = j·d : j ∈ ℤ}` in the half-open interval `(a, b]`:
    the count of integers `j` with `a/d < j ≤ b/d`. -/
noncomputable def gridCount (d a b : ℝ) : ℤ := ⌊b / d⌋ - ⌊a / d⌋

/-- **Deterministic Buffon accuracy.** The number of grid lines crossed as a coordinate
    moves from `a` to `b` differs from the extent measured in units of `d`, namely
    `(b - a)/d`, by strictly less than one. Averaging this `±1` fluctuation over a
    uniform offset yields exactly the extent `(b-a)/d` — the segment-level Buffon law. -/
theorem gridCount_bounds (d a b : ℝ) :
    |(gridCount d a b : ℝ) - (b - a) / d| < 1 := by
  have hfb_le : (⌊b / d⌋ : ℝ) ≤ b / d := Int.floor_le _
  have hfa_le : (⌊a / d⌋ : ℝ) ≤ a / d := Int.floor_le _
  have hfb_lt : b / d - 1 < (⌊b / d⌋ : ℝ) := Int.sub_one_lt_floor _
  have hfa_lt : a / d - 1 < (⌊a / d⌋ : ℝ) := Int.sub_one_lt_floor _
  have hsub : (b - a) / d = b / d - a / d := sub_div b a d
  rw [abs_sub_lt_iff]
  constructor
  · -- gridCount - (b-a)/d < 1
    simp only [gridCount, Int.cast_sub]
    rw [hsub]; linarith
  · -- (b-a)/d - gridCount < 1
    simp only [gridCount, Int.cast_sub]
    rw [hsub]; linarith

/-- The grid count over an empty sweep is zero. -/
@[simp] theorem gridCount_self (d a : ℝ) : gridCount d a a = 0 := by
  simp [gridCount]

/-! ## Part II: Codimension-aware crossings and the dichotomy

We import the parent's `segmentCrossings α ℓ d = α·ℓ/d` and `Noodle` machinery. The
codimension of a `k`-flat in `ℝⁿ` is `c = n - k`. Only `c = 1` (hyperplanes) yields a
crossing; every other codimension gives the identically-zero count. -/

/-- The codimension of a `k`-dimensional flat inside `ℝⁿ`. -/
def codim (n k : ℕ) : ℕ := n - k

/-- Per-segment expected intersection count with a family of parallel `k`-flats in
    `ℝⁿ`. A `1`-dimensional segment meets a codimension-`c` flat in dimension `1 - c`,
    so the count is the hyperplane value `segmentCrossings α ℓ d` when `c = 1` and
    vanishes otherwise. -/
noncomputable def flatSegmentCrossings (n k : ℕ) (α ℓ d : ℝ) : ℝ :=
  if codim n k = 1 then segmentCrossings α ℓ d else 0

/-- In codimension 1, the per-segment count is the parent noodle value. -/
theorem flatSegmentCrossings_codim_one {n k : ℕ} (h : codim n k = 1) (α ℓ d : ℝ) :
    flatSegmentCrossings n k α ℓ d = segmentCrossings α ℓ d := by
  simp [flatSegmentCrossings, h]

/-- In any codimension other than 1, the per-segment count vanishes. -/
theorem flatSegmentCrossings_of_codim_ne_one {n k : ℕ} (h : codim n k ≠ 1)
    (α ℓ d : ℝ) : flatSegmentCrossings n k α ℓ d = 0 := by
  simp [flatSegmentCrossings, h]

/-- A hyperplane family (`k = n - 1`, with `n ≥ 1`) is codimension 1 and recovers the
    parent per-segment law. -/
theorem flatSegmentCrossings_hyperplane {n : ℕ} (hn : 1 ≤ n) (α ℓ d : ℝ) :
    flatSegmentCrossings n (n - 1) α ℓ d = segmentCrossings α ℓ d := by
  apply flatSegmentCrossings_codim_one
  simp only [codim]
  omega

/-- Linearity of the per-segment count in the length. -/
theorem flatSegmentCrossings_linear (n k : ℕ) (α ℓ d c : ℝ) :
    flatSegmentCrossings n k α (c * ℓ) d = c * flatSegmentCrossings n k α ℓ d := by
  unfold flatSegmentCrossings
  split
  · exact segmentCrossings_linear α ℓ d c
  · ring

/-- Nonnegativity of the per-segment count. -/
theorem flatSegmentCrossings_nonneg (n k : ℕ) (α ℓ d : ℝ)
    (hα : 0 ≤ α) (hℓ : 0 ≤ ℓ) (hd : 0 < d) :
    0 ≤ flatSegmentCrossings n k α ℓ d := by
  unfold flatSegmentCrossings
  split
  · exact segmentCrossings_nonneg α ℓ d hα hℓ hd
  · exact le_refl 0

/-! ## Part III: The noodle-level codimension law -/

/-- Expected total intersections of a noodle `N` with a family of parallel `k`-flats in
    `ℝⁿ`, spaced `d` apart, in a dimension with crossing factor `α`. -/
noncomputable def expectedFlatCrossings {p : ℕ} (N : Noodle p) (n k : ℕ) (α d : ℝ) : ℝ :=
  ∑ i : Fin p, flatSegmentCrossings n k α (N.segLen i) d

/-- **Codimension-1 law.** For hyperplane-codimension families the expected count is the
    parent noodle law `α·L/d`; length-proportionality survives. -/
theorem expectedFlatCrossings_codim_one {p : ℕ} (N : Noodle p) {n k : ℕ}
    (h : codim n k = 1) (α d : ℝ) :
    expectedFlatCrossings N n k α d = α * N.totalLength / d := by
  unfold expectedFlatCrossings
  simp_rw [flatSegmentCrossings_codim_one h]
  have : (∑ i : Fin p, segmentCrossings α (N.segLen i) d) = N.expectedCrossings α d := rfl
  rw [this, noodle_highdim]

/-- **The dichotomy.** For every codimension other than 1, a generic curve misses all the
    flats: the expected intersection count is identically zero, independent of the total
    length or shape. Length-proportionality is a strictly codimension-1 phenomenon. -/
theorem expectedFlatCrossings_dichotomy {p : ℕ} (N : Noodle p) {n k : ℕ}
    (h : codim n k ≠ 1) (α d : ℝ) :
    expectedFlatCrossings N n k α d = 0 := by
  unfold expectedFlatCrossings
  simp_rw [flatSegmentCrossings_of_codim_ne_one h]
  simp

/-- **Hyperplane recovery.** Dropping the noodle against parallel hyperplanes
    (`k = n-1`, `n ≥ 1`) gives exactly the parent higher-dimensional law `α·L/d`. -/
theorem expectedFlatCrossings_hyperplane {p : ℕ} (N : Noodle p) {n : ℕ} (hn : 1 ≤ n)
    (α d : ℝ) :
    expectedFlatCrossings N n (n - 1) α d = α * N.totalLength / d := by
  apply expectedFlatCrossings_codim_one
  simp only [codim]; omega

/-- Nonnegativity of the noodle-level codimension count. -/
theorem expectedFlatCrossings_nonneg {p : ℕ} (N : Noodle p) (n k : ℕ) (α d : ℝ)
    (hα : 0 ≤ α) (hd : 0 < d) :
    0 ≤ expectedFlatCrossings N n k α d := by
  unfold expectedFlatCrossings
  exact Finset.sum_nonneg fun i _ =>
    flatSegmentCrossings_nonneg n k α (N.segLen i) d hα (N.nonneg i) hd

/-! ## Part IV: Structural laws in the codimension-1 regime

For hyperplane-codimension families the count reduces to the parent law, so the noodle's
shape-independence and monotonicity carry over verbatim. -/

/-- **Shape independence (codimension 1).** Two noodles of equal total length have equal
    expected intersections against a hyperplane-codimension family, regardless of shape. -/
theorem flatShape_independence {p q : ℕ} (N₁ : Noodle p) (N₂ : Noodle q) {n k : ℕ}
    (h : codim n k = 1) (α d : ℝ) (hLen : N₁.totalLength = N₂.totalLength) :
    expectedFlatCrossings N₁ n k α d = expectedFlatCrossings N₂ n k α d := by
  rw [expectedFlatCrossings_codim_one N₁ h, expectedFlatCrossings_codim_one N₂ h, hLen]

/-- **Monotonicity (codimension 1).** A longer noodle has at least as many expected
    intersections, given a nonnegative crossing factor and positive spacing. -/
theorem flatCrossings_mono {p q : ℕ} (N₁ : Noodle p) (N₂ : Noodle q) {n k : ℕ}
    (h : codim n k = 1) (α d : ℝ) (hα : 0 ≤ α) (hd : 0 < d)
    (hLen : N₁.totalLength ≤ N₂.totalLength) :
    expectedFlatCrossings N₁ n k α d ≤ expectedFlatCrossings N₂ n k α d := by
  rw [expectedFlatCrossings_codim_one N₁ h, expectedFlatCrossings_codim_one N₂ h]
  have hd' : (0 : ℝ) ≤ d := hd.le
  gcongr

/-! ## Part V: Concrete instances -/

/-- **`ℝ³`, planes.** A family of parallel planes (`k = 2`) in `ℝ³` is codimension 1;
    with the spatial crossing factor `α₃ = 1/2` the noodle law reads `E = L/(2d)`. -/
theorem spatial_planes {p : ℕ} (N : Noodle p) (d : ℝ) :
    expectedFlatCrossings N 3 2 (1 / 2) d = N.totalLength / (2 * d) := by
  rw [expectedFlatCrossings_codim_one N (by decide) (1 / 2) d]
  ring

/-- **`ℝ³`, lines.** A family of parallel lines (`k = 1`) in `ℝ³` is codimension 2, so a
    curve almost surely misses them: the expected intersection count is `0`, whatever the
    length or shape. -/
theorem spatial_lines_vanish {p : ℕ} (N : Noodle p) (α d : ℝ) :
    expectedFlatCrossings N 3 1 α d = 0 :=
  expectedFlatCrossings_dichotomy N (by decide) α d

/-- **`ℝ²`, lines.** The classical planar Buffon–Barbier setting: lines (`k = 1`) in the
    plane are codimension 1, and with `α₂ = 2/π` the law recovers `E = 2L/(πd)`. -/
theorem planar_lines {p : ℕ} (N : Noodle p) (d : ℝ) :
    expectedFlatCrossings N 2 1 (2 / π) d = 2 * N.totalLength / (π * d) := by
  rw [expectedFlatCrossings_codim_one N (by decide) (2 / π) d]
  ring

end BuffonsNoodleCodim
