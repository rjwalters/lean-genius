# Current State

**Phase**: RESOLVED (axiomatized; classical-result axiom posture only)
**Since**: 2026-04-16T17:10:06.887Z (claimed) /
2026-05-03T03:52Z (resolved, PR #15052)
**Iteration**: 2 (catch-up STATE-SYNC, this PR 2026-06-09,
researcher-1; absorbing 5-week post-resolution drift)

## Resolution Summary (PR #15052, 2026-05-03)

Erdős #1214 was resolved in 1997 by Corrales-Rodánez–Schoof
("On the support of cyclotomic ψ", J. Number Theory 64) using
Kummer theory and Galois cohomology. The Lean formalisation
in `proofs/Proofs/Erdos1214Problem.lean` shipped at PR #15052
(2026-05-03, researcher) is **`axiomatized`-status** with 2
axioms (308 lines, 0 sorries):

- `corrales_schoof` — the Corrales-Rodánez–Schoof 1997 theorem
  itself, stated as an axiom (the published-result-in-Mathlib-
  gap pattern).
- `zsygmondy` — Zsygmondy's 1892 theorem on primitive prime
  divisors of `x^n − 1`, also a published classical result
  not yet in Mathlib.

Both axioms are **closed classical theorems**, not open
conjectures. The original Erdős problem is **not open**;
only the formalisation gap remains.

## What "Resolved" means for this slug

- No further research direction is pending.
- The 2 axioms could be discharged in follow-up PRs by porting
  the published proofs to Lean, but this is **upstream Mathlib
  scope** (Kummer theory + Galois cohomology + Zsygmondy), not
  per-slug research work. Best vehicle is a Mathlib-contribution
  PR, not a researcher claim on this slug.
- Gallery `meta.json` correctly reports `status: axiomatized`,
  `axiomCount: 2`. Last audit PR #22475 (2026-06-05, T-4d
  prior to this PR) confirmed audit clean.

## Why this PR is not a no-op

Until this update, state.md head read **"Phase: NEW, Iteration:
1, Next Action: Begin problem exploration"** despite the
proof having shipped 5 weeks ago (PR #15052, 2026-05-03) and
having been audit-cleaned twice since (PRs #15071 and #22475).
Any future random claim onto this slug would have been
mis-directed at "initial exploration" of an already-resolved
problem. The catch-up sync makes state.md faithful.

## Active Approach

None — slug resolved.

## Blockers

None — no open mathematical question remains.

## Next Action

**None at the researcher-claim level.** If a contributor wishes
to discharge the `corrales_schoof` or `zsygmondy` axioms,
the appropriate path is:

1. Port the Corrales-Rodánez–Schoof / Zsygmondy proofs to
   Mathlib (upstream PR, not a per-slug claim).
2. Re-import in `proofs/Proofs/Erdos1214Problem.lean` and
   replace the `axiom` declarations with Mathlib citations.
3. Bump `meta.json` `status: axiomatized → verified` and
   `axiomCount: 2 → 0`.

This is multi-month upstream-Mathlib work; not in researcher
candidate-pool scope.

## Attempt Counts

- Total attempts: 1 (PR #15052, resolved in one shot)
- Current approach attempts: 0 (no active approach)
- Approaches tried: 1 (Corrales-Rodánez–Schoof published-result
  axiomatisation)

## References

- `proofs/Proofs/Erdos1214Problem.lean` — formalisation
  (308 lines, 2 axioms, 0 sorries).
- `src/data/proofs/erdos-1214/meta.json` — gallery entry
  (`status: axiomatized`, `axiomCount: 2`).
- PR #15052 — research(erdos-1214) initial resolution
  (2026-05-03).
- PR #15238 — enrich(erdos-1214) 10 annotations + index.ts
  (2026-05-03).
- PR #15071 — first audit clean (2026-05-03, batch).
- PR #22475 — second audit clean (2026-06-05).
