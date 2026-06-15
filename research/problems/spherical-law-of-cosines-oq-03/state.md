# Research State: spherical-law-of-cosines-oq-03

## Current State
**Phase**: ACT (post-SOLVED, outward enrichment)
**Path**: full
**Since**: 2026-06-15T06:15:07Z
**Iteration**: 5

## Current Focus
The literal OQ deliverable `dual_law_trig` (`cos C = −cos A·cos B + sin A·sin B·cos c`)
is DONE and on main (0 axioms, 0 sorries). This session (researcher-3) implements the
polar-triangle duality in Lean — the structural "why" PR #24520 documented but only
certified numerically. New **Part VII** realises the dual law as a side-law-shaped
relation among the polar-triangle vertices `U=v×w, V=w×u, W=u×v`.

## Active Approach
Each polar-vertex inner product is a Binet–Cauchy product giving the negated cosine
numerator of the opposite original angle (`⟨U,V⟩ = cos a·cos b − cos c = −(cos C num)`),
and each polar self-inner-product is the Lagrange side-sine square. Substituting these
into `dual_spherical_law_cleared` re-expresses the dual law in the polar triangle's own
coordinates (`dual_law_polar_form`). All `ring`/`rw`/`linear_combination`-only, no
division, no radicals — blackout-safe.

## Attempt Count
- Total attempts: 5
- Current approach attempts: 1
- Approaches tried: cleared form, literal trig form, cross-product form, polar form

## Blockers
Docker daemon down (`docker info` hangs/timeout) → no local typecheck; Aristotle `prove`
404 in recent sessions. Part VII is build-pending but EXACTLY certified (sympy, residual
identically 0) in `verify_polar_form.py`: the three polar inner-product identities are
component-wise polynomial identities, and the capstone `linear_combination
dual_spherical_law_cleared` certificate has residual 0. All lemmas reuse the same
`binet_cauchy`/`lagrange_identity` machinery already trusted in Parts II/VI.

## Next Action
When Docker returns: build `Proofs.SphericalLawOfCosinesOQ03` to confirm typecheck of
Parts VI–VII. Optional future step: bridge to the parent's `Vec3`/`SphericalTriangle.angleC`
so the angle quantities are derived from `arccos`, not posited (introduces division —
defer per `feedback-avoid-field-simp-under-no-build`).
