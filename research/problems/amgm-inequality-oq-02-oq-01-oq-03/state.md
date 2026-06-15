# Research State: amgm-inequality-oq-02-oq-01-oq-03

## Current State
**Phase**: ACT
**Path**: full
**Since**: 2026-06-15T00:34:09-07:00
**Iteration**: 2

## Current Focus
Concrete general-Finset Route A shipped build-pending (`AmgmInequalityOQ02OQ01OQ03Finset.lean`).
S2 found the **char-2 obstruction**: L2+L3+L4 only give `2·p₃ = 2·closed`, so Route A needs a
cancellable 2; Route B (aeval) is required for full general-CommRing generality.

## Active Approach
Route A: `sq_split`/`D_collapse`/`p2_closed`/`two_mul_p3_closed` proven (any CommRing);
`newton_girard_three_finset` proven over `[NoZeroDivisors]`+`2≠0`. Two combinatorial sorries
remain (`cube_partition` L2, `two_e2_eq_offPairs` L4). Route B now recommended for generality.

## Attempt Count
- Total attempts: 2
- Current approach attempts: 2
- Approaches tried: 2 (Route A char≠2; Route B pending)

## Blockers
Docker build offline + Aristotle 404 (dual blackout, 2026-06-15) — file build-pending,
unregistered (has 2 sorries). L2/L4 are Aristotle targets when backend returns.

## Next Action
Build-verify the proven parts; pursue Route B aeval reindexing (supersedes L2+L4, char-2 safe);
submit L2/L4 to Aristotle when up.
