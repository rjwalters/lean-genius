# Research State: brianchon-theorem-oq-01-oq-01

## Current State
**Phase**: ACT
**Path**: full
**Since**: 2026-06-26
**Iteration**: 1

## Current Focus
Eliminate the parent's shared `conic_implies_pascal` axiom (Pascal's hexagon
theorem in the projective ℝ³ model). Direct ideal-membership route is blocked
(Aristotle down); pursuing the standard-conic / rational-normal-curve reduction,
which reduces Pascal collinearity to a `ring`-closable polynomial identity.

## Active Approach
Parametrise the standard conic `y² = x z` by `t ↦ (1, t, t²)`; the three
opposite-side intersections of the inscribed hexagon are collinear by a true
polynomial identity in the six parameters. Implemented in
`proofs/Proofs/BrianchonTheoremOQ01OQ01.lean`.

## Attempt Count
- Total attempts: 1
- Current approach attempts: 1
- Approaches tried: 1 (rational-normal-curve reduction — proof written)

## Result
- `pascal_std_conic` / `pascal_std_conic_full`: Pascal's hexagon theorem for the
  standard conic, axiom-free and sorry-free (as written).
- Supporting: `threeVectorMatrix_det`, `stdConic_symmetric`,
  `rncPoint_on_stdConic`.
- **BUILD-PENDING**: not yet machine-verified — host disk is 100% full and
  Docker's content store is corrupted (containerd I/O errors), so the docker
  build could not run this session.

## Blockers
- **Environment (shared):** host disk full → Docker builds impossible;
  Aristotle MCP returns 404 → direct ideal-membership discharge unavailable.
- **Mathematical:** the general axiom still needs the PGL₃-equivalence reduction
  (standard conic → arbitrary nondegenerate conic) + the degenerate cases.

## Next Action
Verify the file once Docker/disk is restored; then build the projective
equivalence reduction to generalise beyond the standard conic.
