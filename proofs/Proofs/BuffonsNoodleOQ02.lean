import Proofs.BuffonsNeedle
import Proofs.BuffonsNoodle
import Mathlib.Tactic

/-
# Buffon's Noodle, OQ-02: the Needle → Noodle composition, axiom-free

## What this file establishes

The `buffons-noodle` gallery entry states the polygonal noodle theorem

  `BuffonsNoodle.buffon_noodle_polygon : N.expectedCrossings d = 2 * N.totalLength / (π * d)`

where the per-segment crossing probability is packaged as

  `BuffonsNoodle.segmentCrossingProb ℓ d := 2 * ℓ / (π * d)`.

The OQ-02 problem statement framed `segmentCrossingProb` as a *definitional / axiomatized
input* and asked to "discharge an axiom" by importing Buffon's Needle. The first finding of
this work is that the premise is inaccurate: `segmentCrossingProb` is a plain `def`, and the
polygonal noodle theorem is **already proven with zero axioms** (purely by linearity of the
finite sum). The two `axiom` declarations in `BuffonsNoodle.lean`
(`smoothExpectedCrossings`, `buffon_noodle_smooth_eq`) belong exclusively to the *smooth*
curve generalization (Part VI), i.e. the genuine Cauchy–Crofton / kinematic-measure gap;
they play no role in the polygonal result.

What is genuinely available — and what this file delivers — is the **composition** the
problem really wanted: showing that the constant `2 * ℓ / (π * d)` used per segment is not a
free-floating definition but exactly the favorable-area / sample-space-area ratio that the
Buffon's Needle entry *derives by integration*:

  `BuffonsNeedle.buffon_needle_probability'`
    : `(∫ θ in 0..π, (ℓ / 2) * sin θ) / ((d / 2) * π) = 2 * ℓ / (π * d)`.

Plugging this into the noodle sum gives the polygonal noodle theorem with every per-segment
value *derived from the Needle entry* (the integral `∫₀^π (ℓ/2) sin θ = ℓ` is the crossing
region's area), composing two gallery entries end to end with **0 axioms, 0 sorries** — and
never touching the smooth-case axioms.

## Status

- [x] `segmentCrossingProb` = Needle entry's machine-derived area ratio (the bridge)
- [x] Noodle expected crossings = sum of Needle area ratios
- [x] Polygonal noodle theorem re-expressed through the Needle integral, axiom-free
- [ ] Smooth case (`smoothExpectedCrossings`, `buffon_noodle_smooth_eq`): still genuinely
      open — requires Mathlib kinematic-measure / Cauchy–Crofton machinery.
-/

namespace BuffonsNoodleOQ02

open Real BuffonsNoodle

/-- **The Needle → Noodle bridge.**

The Noodle entry's per-segment crossing-probability constant `segmentCrossingProb ℓ d`
equals the favorable-to-total area ratio that the Buffon's Needle entry derives by
integration: the numerator `∫₀^π (ℓ/2) sin θ` is the area of the crossing region
(`= ℓ`, by `BuffonsNeedle.crossingRegion_area`), and the denominator `(d/2)·π` is the area
of the `(x, θ)` sample space. So the value plugged into the noodle sum is *derived*, not
assumed. -/
theorem segmentCrossingProb_eq_needle_ratio (ℓ d : ℝ) (hd : 0 < d) :
    segmentCrossingProb ℓ d
      = (∫ θ in (0 : ℝ)..π, (ℓ / 2) * Real.sin θ) / ((d / 2) * π) := by
  unfold segmentCrossingProb
  rw [← BuffonsNeedle.buffon_needle_probability' ℓ d Real.pi_ne_zero hd.ne']

/-- The expected number of crossings of a polygonal noodle is the sum, over its segments, of
the Buffon's Needle area ratio for each segment — i.e. the noodle's expectation is literally
a sum of (derived) single-needle crossing probabilities. -/
theorem expectedCrossings_eq_sum_needle_ratio {n : ℕ}
    (N : PolygonalNoodle n) (d : ℝ) (hd : 0 < d) :
    N.expectedCrossings d
      = ∑ i : Fin n,
          (∫ θ in (0 : ℝ)..π, (N.segLen i / 2) * Real.sin θ) / ((d / 2) * π) := by
  unfold PolygonalNoodle.expectedCrossings
  exact Finset.sum_congr rfl
    (fun i _ => segmentCrossingProb_eq_needle_ratio (N.segLen i) d hd)

/-- **Buffon's Noodle (polygonal case), via the Needle entry — axiom-free.**

Summing the Buffon's Needle area ratios over the noodle's segments yields `2L/(πd)`, where
`L = N.totalLength`. Every per-segment value is the Needle entry's integrated crossing
probability, so the whole chain Needle → Noodle is machine-checked end to end with no axioms
and no sorries. (Contrast the smooth case, whose `2L/(πd)` law remains an axiom pending
Cauchy–Crofton machinery.) -/
theorem buffon_noodle_via_needle {n : ℕ}
    (N : PolygonalNoodle n) (d : ℝ) (hd : 0 < d) :
    (∑ i : Fin n,
        (∫ θ in (0 : ℝ)..π, (N.segLen i / 2) * Real.sin θ) / ((d / 2) * π))
      = 2 * N.totalLength / (π * d) := by
  rw [← expectedCrossings_eq_sum_needle_ratio N d hd]
  exact buffon_noodle_polygon N d hd

/-- A single straight needle, viewed as a one-segment noodle, has expected crossings equal to
the Buffon's Needle area ratio for its length — the base case of the composition. -/
theorem single_needle_ratio (ℓ d : ℝ) (hd : 0 < d) :
    segmentCrossingProb ℓ d
      = (∫ θ in (0 : ℝ)..π, (ℓ / 2) * Real.sin θ) / ((d / 2) * π) :=
  segmentCrossingProb_eq_needle_ratio ℓ d hd

end BuffonsNoodleOQ02
