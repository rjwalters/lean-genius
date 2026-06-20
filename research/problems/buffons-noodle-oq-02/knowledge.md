# Knowledge Base: buffons-noodle-oq-02

Insights accumulated during research on this problem.

---

## Problem Understanding

Goal as stated: eliminate the "axiomatized" per-segment crossing probability
`segmentCrossingProb = 2ℓ/(πd)` in `BuffonsNoodle.lean` by deriving it from the registered
Buffon's Needle entry, upgrading the base `buffons-noodle` gallery entry from
`axiomatized`/`axiom` to `verified`/`original`.

---

## Insights

### 1. The stated premise is inaccurate — the polygonal case is already axiom-free
`BuffonsNoodle.segmentCrossingProb ℓ d` is a plain `noncomputable def` equal to
`2 * ℓ / (π * d)`, **not** an `axiom`. The polygonal noodle theorem
`BuffonsNoodle.buffon_noodle_polygon : N.expectedCrossings d = 2 * N.totalLength / (π * d)`
is proven purely by linearity of a finite sum — it uses **no axioms**. So there is no
per-segment axiom to "discharge"; the polygonal result never depended on one.

### 2. The real axioms are the *smooth*-case Cauchy–Crofton primitives
`BuffonsNoodle.lean` carries exactly two `axiom` declarations, both in Part VI (smooth
curves):
- `smoothExpectedCrossings (γ : ℝ → ℝ × ℝ) (a b d : ℝ) : ℝ` — the primitive "expected
  crossings of a C¹ curve" functional.
- `buffon_noodle_smooth_eq : smoothExpectedCrossings γ a b d = 2 * planarCurveArcLength γ a b / (π*d)`
  — the Barbier law for smooth curves.
These encode the genuine integral-geometry content (kinematic measure on the space of
lines, plus a polygonal→smooth arc-length approximation of the crossing functional). They
are independent of the polygonal theorem and are a multi-week Mathlib gap, not a bridge.
`leanFile.axiomCount = 2` in the base entry reflects these two, not `segmentCrossingProb`.

### 3. The genuine, deliverable composition: Needle → Noodle (axiom-free)
The Buffon's Needle entry *does* derive the constant by integration:
`BuffonsNeedle.buffon_needle_probability'`
  : `(∫ θ in 0..π, (ℓ/2)·sin θ) / ((d/2)·π) = 2ℓ/(πd)`  (for `π ≠ 0`, `d ≠ 0`),
with `BuffonsNeedle.crossingRegion_area : ∫₀^π (ℓ/2)·sin θ = ℓ` the favorable area and
`(d/2)·π` the sample-space area. Substituting this into `segmentCrossingProb` and the
noodle sum makes every per-segment value *derived from the Needle entry* rather than
asserted, composing the two gallery entries end to end with **0 axioms, 0 sorries**. This
is what `proofs/Proofs/BuffonsNoodleOQ02.lean` delivers
(`segmentCrossingProb_eq_needle_ratio`, `expectedCrossings_eq_sum_needle_ratio`,
`buffon_noodle_via_needle`). It substantiates the problem's real intent without changing
the base entry's axiom count (those 2 axioms remain, for the smooth case only).

### 4. Convention compatibility checks out
Both entries use the same short-segment parametrization: angle `θ ∈ [0, π]`, offset
`x ∈ [0, d/2]`, crossing condition `x ≤ (ℓ/2) sin θ`. No normalization mismatch — the
Needle area ratio and the Noodle constant are literally the same expression `2ℓ/(πd)`, so
the bridge is `rw [← buffon_needle_probability']` after `unfold segmentCrossingProb`.

---

## Dead Ends

- **"Discharge the segment axiom to make `buffons-noodle` verified."** There is no such
  axiom; nothing to discharge in the polygonal case. The base entry's `axiomatized` status
  (if asserted) would instead be attributable to the smooth-case axioms (#2), which this
  bridge does not remove.
- **Cauchy–Crofton route for the per-segment value.** Overkill: the Needle entry already
  supplies the value by a one-line integral; the Crofton machinery would only be needed for
  the smooth-curve axioms, which remain genuinely open.
