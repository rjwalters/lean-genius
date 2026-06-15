# Research State: quadratic-reciprocity-algorithm-oq-03

## Current State
**Phase**: ORIENT
**Path**: full
**Since**: 2026-06-14
**Iteration**: 4

## Current Focus
Zolotarev's lemma as the formalization spine: `legendreSym p a = Perm.sign (mulLeft a)` on
`ZMod p`. OQ resolved on paper (researcher-8 S1); Milestone-1 statement + key cycle-structure
step numerically verified (researcher-4 S2). researcher-5 S3 **committed that verification as a
reproducible script** (`verify_zolotarev.py`): asserts the lemma + all four proof steps for every
odd prime 3≤p<80 and every nonzero a, so the M1 target is now a durable, re-runnable certificate.
Formalizable core pinned and de-risked; awaiting Docker for the build.

## Active Approach
Permutation-sign (Zolotarev) proof. Milestone 1 = the Zolotarev lemma itself (cyclic units +
cycle-sign + Euler's criterion), ~80–120 LOC, oq-01-independent. Milestone 2 (reciprocity from the
CRT/shuffle-permutation sign) is gated and larger — assess after Milestone 1.

## Attempt Count
- Total attempts: 0 (no Lean built — Docker down, no materialized Mathlib)
- Current approach attempts: 0
- Approaches tried: 1 surveyed (Zolotarev direct), 1 deprioritized (algorithm-confluence)

## Blockers
- Docker build environment down (`docker info` times out); cannot compile/verify Lean this session.
- No new foundational Mathlib gap for Milestone 1 — it is buildable once the environment returns.

## Next Action
**ACT Milestone 1 (when Docker returns):** new file `proofs/Proofs/QuadraticReciprocityZolotarev.lean`
proving `legendreSym p a = (Perm.sign (Equiv.mulLeft₀ (a : ZMod p) ha) : ℤ)` for odd prime `p`,
`a ≠ 0`. Steps: (1) `π_g` is a single `(p−1)`-cycle on the units ⇒ `sign = −1`; (2) `a = g^k`,
`sign (π_a) = (−1)^k` via `map_pow`; (3) Euler's criterion gives `legendreSym p a = (−1)^k`.
Confirm exact Mathlib names at build time (`Equiv.Perm.IsCycle.sign`, `ZMod.euler_criterion`,
`IsCyclic (ZMod p)ˣ`). Then create the gallery entry `src/data/proofs/quadratic-reciprocity-zolotarev/`.

See knowledge.md for the full survey, Mathlib inventory, and the honesty flag on Milestone 2.
