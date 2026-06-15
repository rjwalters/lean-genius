# Research State: spherical-law-of-cosines-oq-03

## Current State
**Phase**: ACT (post-SOLVED, outward enrichment)
**Path**: full
**Since**: 2026-06-15T06:15:07Z
**Iteration**: 4

## Current Focus
The literal OQ deliverable `dual_law_trig` (`cos C = −cos A·cos B + sin A·sin B·cos c`)
is DONE and on main (0 axioms, 0 sorries). This session adds the outward structural
bridge: geometric grounding of the posited normal forms via cross products.

## Active Approach
Identify each angle-cosine numerator with a Binet–Cauchy inner product of edge
normals and each side-sine square with a Lagrange self-inner-product, then re-derive
the cleared dual law in pure cross-product form. All `ring`/`rw`-only.

## Attempt Count
- Total attempts: 4
- Current approach attempts: 1
- Approaches tried: cleared form, literal trig form, cross-product form

## Blockers
Docker daemon down (`docker info` timeout) → no local typecheck. Aristotle prove 404
in recent sessions. New lemmas are build-pending but numerically validated (3·10⁵
random triangles, max err ~1e-15) and hand-traced.

## Next Action
When Docker returns: build `Proofs.SphericalLawOfCosinesOQ03` to confirm typecheck of
Part VI. Optional future step: bridge to the parent's `Vec3`/`SphericalTriangle.angleC`
so the angle quantities are derived from `arccos`, not posited.
