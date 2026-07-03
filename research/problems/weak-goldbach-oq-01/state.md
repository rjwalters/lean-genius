# Research State: weak-goldbach-oq-01

## Current State
**Phase**: ACT
**Path**: full
**Since**: 2026-07-03
**Iteration**: 3

## Current Focus
Extended `StrongGoldbachSymmetric.lean` (the verified 0-axiom symmetric
reformulation) with the **closed form for the offset-side comet ceiling**:
`oppositeParityOffsets_card m = (m + 1) / 2` and the derived explicit bound
`symmetricPairCount m ≤ (m + 1) / 2` for `m > 2`. This evaluates the abstract
filtered-cardinality RHS of `symmetricPairCount_le_oppositeParityOffsets`
(added in #34124), making the docstring's "≈ m/2" precise with no prime input.

## Active Approach
Elementary parity-counting completion of the Goldbach-comet offset bound.

## BLOCKER — build unverified (host disk exhausted)
The change is written but **NOT machine-checked**: `docker-build.sh` failed with
`No space left on device` extracting the Mathlib cache, and Docker Desktop then
crashed. Host `/System/Volumes/Data` is at **100%** (5.1 GiB free of 926 GiB).
All Lean verification is blocked host-wide until disk is freed. PR opened as
**draft** so the deployer does not auto-merge an unverified proof.

## Attempt Count
- Total attempts: 2 (1 survey, 1 act)
- Approaches tried: 1 mathematical (offset-parity closed form)

## Next Action
Once host disk is reclaimed and Docker is healthy:
`./proofs/scripts/docker-build.sh Proofs.StrongGoldbachSymmetric`.
If green, mark the draft PR ready. Larger future target remains Schnirelmann's
theorem (discharges `schnirelmann_basis_theorem` axiom in WeakGoldbach.lean).
