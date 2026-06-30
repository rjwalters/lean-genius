# Research State: chinese-remainder-non-coprime-oq-01-oq-02

## Current State
**Phase**: ORIENT
**Path**: full
**Since**: 2026-06-13
**Iteration**: 2
**Status**: blocked (survey complete; only ACT remains, build-gated by the 2026-06-13 verification blackout)

## Current Focus
Paper resolution of the full k-modulus Garner algorithm complete. The algorithm,
its Horner (telescoping) form, the correctness argument, and the `O(k²)` =
`k(k−1)/2` single-precision operation count are all worked out in `knowledge.md`,
together with the exact Lean formalization path reusing the parent's
`garner_mixed_radix` as the `k = 2` base case.

## Active Approach
Generalize `ChineseRemainderNonCoprimeOQ01.garner_mixed_radix` (k = 2) to k
coprime moduli via list recursions `garnerCoeffs`/`garnerReconstruct`; prove
correctness by induction on the modulus list with the parent lemma as the
splitting step; formalize the runtime bound as a closed form of an explicit
operation-counter `garnerCoeffsOps ms = k(k−1)/2`.

## Attempt Count
- Total attempts: 0 (survey only — no Lean committed)
- Current approach attempts: 0
- Approaches tried: 0

## Blockers
- **Verification blackout (2026-06-13)**: Docker daemon down (`docker info`
  timeout) + Aristotle backend returns 404 on a trivial `prove` (confirmed live
  this session). The `garnerCoeffs`/`garnerReconstruct` defs and the main
  correctness theorem require a Docker `lake` build to verify, so no Lean was
  committed.
- **Mathlib gap**: no operation-cost / complexity model. The "runtime complexity
  bounds" half must be formalized as a hand-rolled `Nat` step-counter with a
  proved closed form (no external dependency; tractable once builds work).

## Next Action
When Docker/Aristotle infra recovers: create
`proofs/Proofs/ChineseRemainderNonCoprimeOQ01OQ02.lean`, implement
`garnerCoeffs` / `garnerReconstruct`, prove the per-modulus congruence +
`< ms.prod` bound by list induction off `garner_mixed_radix`, then add the
`garnerCoeffsOps` counter and its `k(k−1)/2` closed-form lemma. Build via
`./proofs/scripts/docker-build.sh Proofs.ChineseRemainderNonCoprimeOQ01OQ02`.
