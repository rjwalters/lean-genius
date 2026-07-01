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
