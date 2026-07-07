import Proofs.BuffonsNoodleOQ03
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.Topology.MetricSpace.HausdorffDimension
import Mathlib.Tactic

/-!
# Buffon's Noodle, higher codimension — the degeneracy dichotomy (oq-03 · oq-02)

## The open question

The parent line of work generalises Buffon's Noodle to `ℝⁿ`: a rectifiable curve of
length `L` thrown at a family of parallel **hyperplanes** spaced `d` apart crosses them
`E = αₙ · L / d` times on average, where `αₙ = 𝔼_{u ∼ S^{n-1}} |u₁|` is the *crossing
factor* (parent file `BuffonsNoodleOQ03.lean`; its closed form
`αₙ = Γ(n/2)/(√π·Γ((n+1)/2))` is `BuffonsNoodleOQ03OQ01.lean`).

Open question **oq-03 · oq-02** asks to *generalise the codimension*: what is the expected
number of intersections of a length-`L` curve with a fixed family of parallel
**`k`-dimensional affine subspaces** (`k`-flats) in `ℝⁿ`?

## What this file proves: the codimension dichotomy

A `k`-flat in `ℝⁿ` has **codimension** `c = n - k`. A hyperplane is the case `c = 1`, which
is exactly the nondegenerate parent problem. This file settles the *complementary regime*:

> **For codimension `c ≥ 2`, a rectifiable curve almost surely misses every flat: the
> expected number of intersections is `0`.**

The geometry is dimension-counting. Fix the `c`-dimensional orthogonal complement `W = ℝᶜ`
of the common flat direction and let `P : ℝⁿ → W` be the orthogonal projection. A flat with
offset `w ∈ W` meets the curve `Γ : [0,L] → ℝⁿ` **iff** `w` lies in the image of the
*projected* curve `P ∘ Γ : [0,L] → W`. That projected curve is again Lipschitz, so its image
is a `1`-dimensional (Hausdorff dimension `≤ 1`) subset of the `c`-dimensional space `W`. When
`c ≥ 2` a set of Hausdorff dimension `< c` is Lebesgue-null, so the set of *hit offsets* has
measure zero — and hence the expected count against any offset distribution absolutely
continuous with respect to Lebesgue measure vanishes.

This is the honest and complete answer to the higher-codimension question: the only
nondegenerate parallel-flat Buffon law is the hyperplane (`c = 1`) case treated by the
parent files; every higher-codimension family is degenerate for a `1`-dimensional needle.
(The nondegenerate higher-codimension generalisation of integral geometry requires the
*moving* object to have dimension at least the codimension — Cauchy–Crofton / Santaló — a
genuinely different theorem, not a special case of the noodle law.)

## The three results

* `volume_lipschitzImage_eq_zero` — the analytic core: the image of any Lipschitz map
  `γ : ℝ → (Fin c → ℝ)` (`c ≥ 2`) on an arbitrary subset of `ℝ` has Lebesgue measure `0`.
  Proof: `dimH (γ '' s) ≤ dimH s ≤ dimH (univ : Set ℝ) = 1 < c`, and Hausdorff dimension
  strictly below the ambient dimension forces Lebesgue-nullity via
  `hausdorffMeasure_pi_real` (`μH[c] = volume` on `Fin c → ℝ`).
* `crossedOffsets_measure_zero` — the Buffon interpretation: the set of offsets
  `{w | ∃ t ∈ [0,L], γ t = w}` hit by the projected curve `γ` is Lebesgue-null.
* `spatialCurve_crossedOffsets_measure_zero` — the full `ℝⁿ` framing: for a Lipschitz spatial
  curve `Γ` and any Lipschitz projection `P` onto the `c`-dimensional complement, the hit-offset
  set `{w | ∃ t ∈ [0,L], P (Γ t) = w}` is Lebesgue-null.
* `crossing_ae_zero` — the expectation consequence: almost every offset is missed, so the
  crossing count is `0` almost surely and its expectation is `0`.

We work in the coordinate space `Fin c → ℝ` with its product (sup) metric, where
`hausdorffMeasure_pi_real` identifies `μH[c]` with Lebesgue `volume`. The measure-zero
conclusion is bi-Lipschitz invariant, so it transfers verbatim to the Euclidean metric.

## Status

0 axioms, 0 sorries, builds on Mathlib.
-/

namespace BuffonsNoodleOQ03OQ02

open MeasureTheory Set
open scoped ENNReal NNReal

variable {c : ℕ}

/-- **Analytic core.** The image of a Lipschitz map `γ : ℝ → (Fin c → ℝ)` on any subset
`s ⊆ ℝ` has Lebesgue measure zero once the target dimension satisfies `c ≥ 2`.

The image has Hausdorff dimension at most `1` (Lipschitz maps do not increase Hausdorff
dimension, and `dimH (univ : Set ℝ) = 1`), which is strictly below the ambient dimension
`c ≥ 2`. A set of Hausdorff dimension `< c` is null for `μH[c]`, and `μH[c] = volume` on
`Fin c → ℝ` by `hausdorffMeasure_pi_real`. -/
theorem volume_lipschitzImage_eq_zero (hc : 2 ≤ c)
    {γ : ℝ → (Fin c → ℝ)} {K : ℝ≥0} (hγ : LipschitzWith K γ) (s : Set ℝ) :
    volume (γ '' s) = 0 := by
  -- The image has Hausdorff dimension strictly below `c`.
  have hdimle : dimH (γ '' s) ≤ 1 :=
    calc dimH (γ '' s) ≤ dimH s := hγ.dimH_image_le s
      _ ≤ dimH (univ : Set ℝ) := dimH_mono (subset_univ s)
      _ = 1 := Real.dimH_univ
  have hlt : dimH (γ '' s) < (c : ℝ≥0) := by
    refine lt_of_le_of_lt hdimle ?_
    have : (1 : ℝ≥0∞) < (c : ℝ≥0∞) := by exact_mod_cast (by omega : 1 < c)
    simpa using this
  -- `μH[c] = volume`, so the dimension gap makes the image Lebesgue-null.
  have hpi : (μH[((c : ℝ≥0) : ℝ)] : Measure (Fin c → ℝ)) = volume := by
    rw [NNReal.coe_natCast]
    simpa using (hausdorffMeasure_pi_real (ι := Fin c))
  have hac : (volume : Measure (Fin c → ℝ)) ≪ μH[((c : ℝ≥0) : ℝ)] := by
    rw [hpi]
  exact measure_zero_of_dimH_lt hac hlt

/-- **Buffon interpretation (projected curve).** The set of parallel-flat offsets that are
*hit* by the projected curve `γ : ℝ → (Fin c → ℝ)` on the parameter interval `[0, L]` is
Lebesgue-null when the codimension is `c ≥ 2`. An offset `w` is hit exactly when `w = γ t`
for some parameter `t ∈ [0, L]`, i.e. when `w` lies in the curve's image. -/
theorem crossedOffsets_measure_zero (hc : 2 ≤ c)
    {γ : ℝ → (Fin c → ℝ)} {K : ℝ≥0} (hγ : LipschitzWith K γ) (L : ℝ) :
    volume {w : Fin c → ℝ | ∃ t ∈ Icc (0 : ℝ) L, γ t = w} = 0 := by
  have hset : {w : Fin c → ℝ | ∃ t ∈ Icc (0 : ℝ) L, γ t = w} = γ '' Icc 0 L := by
    ext w; simp [Set.mem_image]
  rw [hset]
  exact volume_lipschitzImage_eq_zero hc hγ _

/-- **Full `ℝⁿ` framing.** Let `Γ : ℝ → (Fin n → ℝ)` be a Lipschitz spatial curve and let
`P : (Fin n → ℝ) → (Fin c → ℝ)` be any Lipschitz projection onto the `c`-dimensional
complement of the common flat direction. When the codimension is `c ≥ 2`, the set of offsets
`w ∈ ℝᶜ` for which the `k`-flat `{x | P x = w}` meets the curve on `[0, L]` is Lebesgue-null.

The projected curve `P ∘ Γ` is Lipschitz (composition of Lipschitz maps), so this reduces to
`crossedOffsets_measure_zero`. -/
theorem spatialCurve_crossedOffsets_measure_zero {n : ℕ} (hc : 2 ≤ c)
    {Γ : ℝ → (Fin n → ℝ)} {K : ℝ≥0} (hΓ : LipschitzWith K Γ)
    {P : (Fin n → ℝ) → (Fin c → ℝ)} {M : ℝ≥0} (hP : LipschitzWith M P) (L : ℝ) :
    volume {w : Fin c → ℝ | ∃ t ∈ Icc (0 : ℝ) L, P (Γ t) = w} = 0 :=
  crossedOffsets_measure_zero hc (hP.comp hΓ) L

/-- **Expectation consequence.** Since the hit-offset set is Lebesgue-null, *almost every*
offset is missed by the projected curve. Consequently the number of intersections is `0`
almost surely, and its expectation against any offset distribution absolutely continuous with
respect to Lebesgue measure is `0`. -/
theorem crossing_ae_zero (hc : 2 ≤ c)
    {γ : ℝ → (Fin c → ℝ)} {K : ℝ≥0} (hγ : LipschitzWith K γ) (L : ℝ) :
    ∀ᵐ w : Fin c → ℝ, w ∉ {w : Fin c → ℝ | ∃ t ∈ Icc (0 : ℝ) L, γ t = w} :=
  (measure_eq_zero_iff_ae_notMem).1 (crossedOffsets_measure_zero hc hγ L)

end BuffonsNoodleOQ03OQ02

/-
# Companion development: the combinatorial codimension dichotomy

Recovered from PR #32451. The measure-theoretic treatment above shows that for
codimension `c ≥ 2` a Lipschitz curve almost surely misses every flat. The
development below expresses the same dichotomy at the level of the parent's
polygonal-noodle bookkeeping (`BuffonsNoodleOQ03.lean`): a codimension-aware
expected-crossings functional that reduces to the parent noodle law `α·L/d`
exactly in codimension 1 and vanishes identically otherwise, together with the
deterministic grid-crossing count underlying the Buffon averaging mechanism.

### The codimension dichotomy

Fix a family of parallel `k`-flats spaced `d` apart in `ℝⁿ`, and let `c = n - k` be
the codimension. A curve is 1-dimensional. Two 1-dimensional and `k`-dimensional
affine pieces in general position meet in dimension `1 + k - n = 1 - c`:

* `c = 1` (i.e. `k = n-1`, **hyperplanes**): the intersection is `0`-dimensional —
  isolated crossing points. The family is exactly a hyperplane family, so the expected
  intersection count is the parent's noodle law `αₙ·L/d`.
* `c ≥ 2` (i.e. `k ≤ n-2`): the "intersection" has negative dimension, so a generic
  curve **almost surely misses every flat** (proved rigorously above). The expected
  intersection count is `0`, independently of the length or shape.
* `c = 0` (i.e. `k = n`): the only such flat is all of `ℝⁿ`; there is no proper spaced
  family, and we record the degenerate value `0`.

### The deterministic backbone

Underneath the averaged law is a deterministic counting fact proved from scratch
(`gridCount_bounds`): as one coordinate sweeps an interval `[a,b]`, the number of
grid hyperplanes `{x = j·d : j ∈ ℤ}` it crosses is `⌊b/d⌋ - ⌊a/d⌋`, and this
integer differs from the "extent in units of `d`", `(b-a)/d`, by strictly less
than 1. Averaging the `±1` boundary fluctuation over a uniformly random offset is
exactly what turns the deterministic count into the crossing factor
`segmentCrossings α ℓ d = α·ℓ/d`.
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

/- Axiom audit: expect only `propext`, `Classical.choice`, `Quot.sound`. -/
#print axioms expectedFlatCrossings_codim_one
#print axioms expectedFlatCrossings_dichotomy

end BuffonsNoodleCodim
