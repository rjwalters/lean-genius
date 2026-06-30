# Research State: pascals-hexagon-oq-02

## Current State
**Phase**: ACT (SOLVED at axiomatized level; sole residue is the inherited parent axiom)
**Path**: full
**Since**: 2026-04-23T13:50:28+02:00
**Iteration**: 7

## Current Focus
The open question — derive Brianchon's theorem (diagonals of a hexagon
circumscribed about a conic are concurrent) from the formalized Pascal theorem by
projective duality — is RESOLVED in Lean. `Proofs.PascalsHexagonOQ02` (namespace
`Brianchon`) is complete: 0 own sorries, 0 own axioms, registered in `Proofs.lean`
(`import Proofs.PascalsHexagonOQ02`, line 2701). In the homogeneous-coordinate
model, join = meet = `crossProduct` and collinear = concurrent = the same
determinant predicate, so Pascal applied to the six tangent lines (as points on
the dual line-conic `adj C`) yields Brianchon with no new geometric axiom.

Gallery `meta.json` is therefore `status: axiomatized`, `badge: axiom`,
`axiomCount: 1`, `sorries: 0` — the `1` is the single inherited Pascal axiom
`conic_implies_pascal_constraint` from `PascalsHexagon.lean`, NOT anything specific
to Brianchon.

## Active Approach
None active — slug is at its natural axiomatized stopping point. The only way to
upgrade `axiomCount` 1 → 0 is to discharge the parent axiom
`conic_implies_pascal_constraint`. That path is already fully scaffolded in
`PascalsHexagon.lean`: `proof_sketch_conic_implies_pascal` (symmetric,
non-degenerate case) is complete except for ONE isolated standalone sorry,
`sylvester_stdConic_of_isotropic` (line ~1216) — an invertible projective
transformation carrying any symmetric non-degenerate conic with a real point onto
`stdConic`, via Sylvester's law of inertia
(`QuadraticForm.equivalent_one_neg_one_weighted_sum_squared`). Two further steps
remain for the FULL axiom elimination: (a) reduce asymmetric `C` to its
symmetrization `(C+Cᵀ)/2`, (b) handle degenerate `C` (pairs of lines) by a
Pappus-type argument.

## Attempt Count
- Total attempts: 7
- Current approach attempts: 0 (axiomatized resolution complete)
- Approaches tried: projective-duality Brianchon derivation (DONE), Sylvester-law
  scaffold of `conic_implies_pascal_constraint` down to one sorry (DONE), Sylvester
  sorry discharge (BLOCKED — Aristotle target)

## Blockers
`sylvester_stdConic_of_isotropic` is a prime Aristotle `prove_file` target
(Mathlib-only `QuadraticForm` API, no project-specific scaffolding needed), but
Aristotle `prove`/`prove_file` is returning 404 ("Resource not found",
live-probed this session). Hand-writing the `IsometryEquiv → invertible matrix`
extraction blind is risky — the exact Mathlib API names are unverifiable without a
checked-out Mathlib source and a green build to confirm. Docker build state is not
the bottleneck (OQ02 is already registered/complete; nothing to build-verify for
the axiomatized status).

## Next Action
When Aristotle is non-404: submit `sylvester_stdConic_of_isotropic` to
`prove_file` (file `proofs/Proofs/PascalsHexagon.lean`), verify the returned proof
with a Docker build, then handle the asymmetric/degenerate cases to fully
eliminate `conic_implies_pascal_constraint` and flip the gallery meta to
`verified`. Until then the slug is correctly at `axiomatized` — do NOT re-prove or
pad the completed Brianchon derivation, and do NOT hand-write the Sylvester step
blind.
