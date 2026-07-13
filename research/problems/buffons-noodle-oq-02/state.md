# Research State: buffons-noodle-oq-02

## Current State
**Phase**: DELIVER
**Path**: full
**Since**: 2026-06-19T17:27:54-07:00
**Iteration**: 2

## Current Focus
Composition lemma shipped; problem premise corrected. See knowledge.md.

## Active Approach
Approach 1 (Direct substitution bridge) — completed, but reframed: the target was
*not* an axiom to discharge but a `def` to connect. Delivered the Needle→Noodle
composition as `proofs/Proofs/BuffonsNoodleOQ02.lean` (0 axioms, 0 sorries).

## Key Finding (premise correction)
The problem statement asserted `BuffonsNoodle.segmentCrossingProb` is a
"definitional/axiomatized input" and that the base entry is `axiomatized` *solely*
because of it. This is inaccurate:

- `segmentCrossingProb ℓ d := 2 * ℓ / (π * d)` is a plain `noncomputable def`, not an
  `axiom`.
- The polygonal noodle theorem `BuffonsNoodle.buffon_noodle_polygon` is **already proven
  with 0 axioms** (pure linearity of a finite sum).
- The two `axiom` declarations in `BuffonsNoodle.lean` — `smoothExpectedCrossings` and
  `buffon_noodle_smooth_eq` — belong exclusively to the **smooth** curve generalization
  (Part VI: Cauchy–Crofton / kinematic measure). They are untouched by the polygonal
  result, and discharging them is a genuine multi-week Mathlib gap, not a bridging task.

## Delivered
`proofs/Proofs/BuffonsNoodleOQ02.lean`:
- `segmentCrossingProb_eq_needle_ratio` — the Noodle per-segment constant equals the
  Buffon's Needle entry's machine-derived favorable/total area ratio
  `(∫₀^π (ℓ/2)·sin θ)/((d/2)·π)`.
- `expectedCrossings_eq_sum_needle_ratio` — noodle expectation = sum of Needle area ratios.
- `buffon_noodle_via_needle` — polygonal `2L/(πd)` law re-derived through the Needle
  integral, axiom-free, end to end.
- `single_needle_ratio` — base case.

## Attempt Count
- Total attempts: 1
- Current approach attempts: 1
- Approaches tried: 1

## Blockers
Smooth case only: `buffon_noodle_smooth_eq` needs Mathlib kinematic-measure /
Cauchy–Crofton machinery (the space of lines in ℝ², its kinematic density, and a
polygonal→smooth arc-length approximation of the crossing functional). Not currently
available; out of scope for this OQ.

## Next Action
Ship companion + record; leave the smooth-case axioms as the genuine open residue.
A follow-up OQ could target `buffon_noodle_smooth_eq` once Mathlib gains integral-geometry
kinematic measure support.
