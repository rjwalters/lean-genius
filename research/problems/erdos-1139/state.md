# Current State

**Phase**: AXIOMATIZED
**Since**: 2026-02-08T00:55:03.568Z (NEW); 2026-05-03 (AXIOMATIZED, via PR #14978)
**Last Updated**: 2026-05-13 (state-sync per `sessions/2026-05-13-state-sync-axiomatized.md`)
**Iteration**: 6

## Current Focus

Stable "axiomatized" steady state. `proofs/Proofs/Erdos1139Problem.lean`
has 16 theorems, 2 axioms, 0 sorries:

- **`erdos_1139`** — the Erdős conjecture statement itself (open conjecture; permanently axiomatized per `CLAUDE.md` "Axiom Integrity Policy")
- **`hardy_ramanujan_asymptotic`** — classical 1917 distribution result for almost-prime counting π_k(N); provable in principle but **not in Mathlib v4.26.0** (PNT/sieve infrastructure gap; verified via `gh api search/code` at lake-pinned SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`)

## Active Approach

Axiomatize the open Erdős conjecture + Hardy-Ramanujan asymptotic; prove
derived consequences (`almostPrimeGap` definitions, axiom-form theorems)
within the file. Restoration of both axioms after a brief removal completed
2026-05-03 (PR #14978).

## Blockers

None — slug is in stable steady state. The two axioms are load-bearing and
appropriate per the Axiom Integrity Policy (open conjecture + Mathlib gap).

## Next Action

Slug is stable. Optional future work:

1. **Mathlib upstream watch**: If a Hardy-Ramanujan-class asymptotic lands
   in `Mathlib.NumberTheory.PrimeCounting` (or similar), the
   `hardy_ramanujan_asymptotic` axiom can be replaced by a derived theorem.
2. **JSON drift-sync** (Mechanic territory): sync research JSON top-level
   `phase` / `currentState.phase` from drifted `OBSERVE` / `ACT` to
   `"AXIOMATIZED"`.
3. **State.md drift-sync** (this PR): from `NEW`/`Iteration: 1`/`2026-02-08`
   → `AXIOMATIZED`/`Iteration: 6`/`2026-05-03`. **Completed in this session.**

The Erdős conjecture `erdos_1139` itself remains permanently axiomatized
(it's the open question; cannot be derived from weaker assumptions).

## Attempt Counts

- Total attempts: 5
- Current approach attempts: 1 (axiomatization, completed)
- Approaches tried:
  1. Initial axiomatization (PR #6247, #6336, #6421 — 2026-03-24)
  2. Axiom restore + define almostPrimeGap (PR #8475 — 2026-03-30)
  3. Re-restore both axioms after brief removal (PR #14978 — 2026-05-03)
