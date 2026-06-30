# Research State: simson-line-theorem-oq-01

## Current State
**Phase**: VERIFY
**Path**: full
**Since**: 2026-06-18
**Iteration**: 5

## Current Focus
Nine-point-circle refinement of the Simson-line results. The Simson bisection point
M = (P+H)/2 — where the Simson line of P meets segment PH — lies on the nine-point circle
of △ABC (centre N = H/2, radius 1/2). Proved in SimsonLineTheorem.lean via the pure-ring
identity M − N = P/2, hence |M − N|² = |P|²/4 = 1/4 on the unit circumcircle.

## Active Approach
Complex-number model on the unit circumcircle (circumcentre 0, orthocenter H = A+B+C).
Same conj z = z⁻¹ + field_simp + ring engine as simson_key / simson_bisects_orthocenter_segment.
New: ninePointCenter def + simsonMidpoint_sub_ninePointCenter (ring) + simsonMidpoint_on_nine_point_circle.

## Attempt Count
- Total attempts: 5
- Current approach attempts: 1
- Approaches tried: 1 (complex-number / conjugate-substitution)

## Established Results (verified/original, 0 axioms, 0 sorries)
- simson_key / simson_collinear: Simson's theorem (three feet collinear)
- simson_area_identity / simson_converse / simson_iff: converse + biconditional (collinear feet ⇔ |P|²=1)
- simson_bisects_orthocenter_segment: Simson line of P bisects PH
- antipodal_simson_perp: Simson lines of P and −P are perpendicular
- simsonMidpoint_on_nine_point_circle: bisection point lies on the nine-point circle (NEW)

## Blockers
None.

## Next Action
Docker build CONFIRMED GREEN (3062 jobs, 0 sorries, 0 axioms). En route also fixed a
build-breaking typo in simson_converse (line 214: `h''` → `h'`; the second branch of the
outer rcases binds `h'`, so the prior branch state never actually compiled) and removed
two genuinely-unused simp args. Committing + pushing + PR. Subsequent directions:
Steiner deltoid envelope (needs tangency, not pure ring) — harder, deferred.
