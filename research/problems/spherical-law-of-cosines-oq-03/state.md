# Research State: spherical-law-of-cosines-oq-03

## Current State
**Phase**: DONE (SOLVED + VERIFIED, saturated)
**Path**: full
**Since**: 2026-06-15T06:15:07Z
**Iteration**: 6

## Current Focus
COMPLETE. The literal OQ deliverable `dual_law_trig`
(`cos C = −cos A·cos B + sin A·sin B·cos c`) is on main with 0 axioms, 0 sorries,
together with the full Parts I–VII development (vector toolkit, cleared polynomial
identity, trig form, cross-product form, and polar-triangle duality form). The
build is machine-checked green: PR #24833 flipped the gallery meta to
`verified`/`original` after a successful `docker-build.sh` run
(`Proofs.SphericalLawOfCosinesOQ03`, 7743 jobs, 2026-06-15). Companion files
`SphericalLawOfCosinesOQ03Bidual` (#24644) and `SphericalLawOfCosinesOQ03Primal`
(#24577) are merged and registered in `Proofs.lean`.

## Active Approach
None — slug saturated. The polar-triangle duality (`dual_law_polar_form`), the
polar biduality (`polar_bidual_*`, `polar_triple_sq`), and the primal-side bridge
to the parent `SphericalTriangle` structure (`cos_angleC_eq`,
`spherical_law_of_cosines_trig_complete`) are all on main and verified.

## Attempt Count
- Total attempts: 6
- Current approach attempts: 0 (complete)
- Approaches tried: cleared form, literal trig form, cross-product form, polar
  form, polar biduality, primal `SphericalTriangle` bridge — all merged/verified

## Blockers
None. Prior Docker-down / Aristotle-404 blackout that gated the Part VII build is
resolved: #24833 records a green Docker build of the whole module.

## Next Action
None required — this open question is solved and verified. Optional, non-blocking
future extensions live only in the gallery `meta.json` `openQuestions` (hyperbolic
dual law over a Lorentzian structure; packaging the polar involution as a single
`triangle → polar triangle` definition so the side law and dual law become one
theorem; the degenerate/antipodal non-degeneracy hypothesis for lifting the
cleared form back to the full trig statement). None are research gaps for this
slug.
