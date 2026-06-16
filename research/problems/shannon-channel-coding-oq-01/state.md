# Research State: shannon-channel-coding-oq-01

## Current State
**Phase**: ACT — BSC done & galleried; BEC merged-but-unregistered (build-pending); AWGN open
**Path**: full
**Since**: 2026-06-16 (state-sync: prior file was a never-updated March OBSERVE/0-attempt stub
that did not reflect the substantial merged work — see knowledge.md for the real status)
**Iteration**: 2

## Problem
Can specific named-channel capacities (BSC, BEC, AWGN) be computed formally, beyond the
parent's placeholder `True`/axiom statements?

## Current Status (real, per knowledge.md)
- **BSC — DONE & VERIFIED & GALLERIED.** `ShannonChannelCodingOQ02.lean`
  (`bsc_capacity_proved`, OQ02.lean:257) proves `channelCapacity (bsc p) = log 2 - h(p)`
  from first principles, 0 axioms. Registered (`Proofs.lean:2830`), gallery dir
  `src/data/proofs/shannon-channel-coding-oq-02`. The parent
  `ShannonChannelCoding.lean` still *declares* `axiom bsc_capacity_eq` as a
  forward-declaration discharged downstream in OQ02 (cannot be inlined — OQ02 imports
  the parent, so inlining would create an import cycle).
- **BEC — PROVEN, MERGED, but UNREGISTERED + build-pending.**
  `proofs/Proofs/ShannonChannelCodingBEC.lean` (merged #25152, commit abd81e87a08;
  `bec_capacity` BEC.lean:207, 0 sorries / 0 axioms) proves BEC(p) capacity =
  (1-p)·log 2 via the engine identity `H(X|Y) = p·H(X)`. It is NOT imported in
  `Proofs.lean` and was authored during a Docker blackout, so it has NOT been
  machine-checked. Do NOT create a gallery entry for it while unregistered/unverified
  (false-green risk).
- **AWGN — OPEN, hard.** Continuous channel; needs measure-theoretic differential-entropy
  capacity, much harder than the finite-alphabet BSC/BEC. Not attempted.

## Active Approach
None safe this session — see Blockers.

## Attempt Count
- Total attempts: 2 (BSC capacity proof; BEC capacity proof)
- Current approach attempts: 0
- Approaches tried: 2 (BSC `log 2 - h(p)`; BEC `(1-p)·log 2` via `H(X|Y)=p·H(X)`)

## Blockers
- **Docker blackout** (`docker-build.sh` rc=124, daemon unresponsive). Cannot build, so
  cannot verify + register `ShannonChannelCodingBEC.lean`. Registering an uncompiled file
  would risk the fleet-wide registered build (math PRs are deployer-merged with no Lean gate).
- **Aristotle 404** — not relevant here (BEC is already 0-sorry).

## Next Action
1. **When Docker is healthy** (`docker run --rm alpine echo ok` returns within seconds):
   `./proofs/scripts/docker-build.sh Proofs.ShannonChannelCodingBEC`. If green, add
   `import Proofs.ShannonChannelCodingBEC` to `Proofs.lean` (in the Shannon block near
   `:2829`), confirm the full registered build stays green, then add a gallery dir
   `src/data/proofs/shannon-channel-coding-oq-01` (meta + annotations).
2. AWGN: assess tractability of measure-theoretic capacity before committing — likely
   needs non-Mathlib analytic/measure machinery.
