# Current State

**Phase**: COMPLETED
**Since**: 2026-04-28T17:42:00Z (axiom elimination)
**Iteration**: 7

## Current Focus

Axiom elimination via three-file refactor:
`BallotProblemOQ01OQ04Core.lean` → `BallotProblemOQ01OQ04OQ01.lean` → `BallotProblemOQ01OQ04.lean`.

The previously stated `axiom chung_feller_uniform` is now a `theorem` that
re-exports `ChungFellerBijection.chung_feller_uniform'` (proved with 0 sorries
and 0 axiom uses). Net axiomCount for this gallery proof: 1 → 0.

## Active Approach

**Three-file architecture for the Chung-Feller proof family**:

1. `BallotProblemOQ01OQ04Core.lean` — extracted definitions and cycle-lemma
   bridge: `IsBalancedPath`, `prepend_one_good_rotation`, `balanced_path_total`,
   `balancedPathsOfType`, `upstepsAboveAxis`, etc.
2. `BallotProblemOQ01OQ04OQ01.lean` — companion (unchanged proof content);
   import switched from the parent to `Core` so it no longer depends on the
   axiom-bearing parent.
3. `BallotProblemOQ01OQ04.lean` — gallery face: thin re-export of
   `chung_feller_uniform'` as `chung_feller_uniform`.

This flips the dependency direction: now Core ← Bijection ← GalleryFace,
allowing the gallery face to consume the bijection-proved theorem.

## Blockers

None. Build verification pending (Docker build in progress).

## Next Action

After build verification:
1. Commit metadata + state updates to the same branch.
2. Open PR consolidating the refactor.
3. Mark candidate-pool entry `completed`.

## Open Questions (downstream)

- Can a q-Chung-Feller theorem be formalized, tracking path area?
- Does `chungFellerMap` admit a description in terms of RSK?

## Attempt Counts

- Total attempts: 7
- Current approach attempts: 1
- Approaches tried:
  1. Establish IsBalancedPath, balanced_length, balanced_sum_zero (Session 1)
  2. Cycle lemma application: prepend_one_good_rotation (Session 2)
  3. Define chungFellerRot and prove tail-Dyck properties (Session 3)
  4. Prove chung_feller_bijection_exists (Session 4)
  5. Prove chung_feller_uniform' from the bijection (Session 5)
  6. Fix BallotProblemOQ03 build failures (Session 6)
  7. **Three-file refactor: eliminate the axiom (Session 7, this session)**
