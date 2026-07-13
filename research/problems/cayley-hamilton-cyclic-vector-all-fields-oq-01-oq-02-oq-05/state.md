# Research State: cayley-hamilton-cyclic-vector-all-fields-oq-01-oq-02-oq-05

## Current State
**Phase**: ORIENT
**Path**: full
**Since**: 2026-07-04T17:54:16-07:00
**Iteration**: 2

## Current Focus
First self-contained increment toward multi-block RCF: the CRT / elementary-divisor
**coprime block-merge** `fromBlocks (C p) 0 0 (C q) ~ C (p*q)` for coprime monic `p,q`.
Statement skeleton drafted in `lean/OQ01OQ02OQ05-skeleton.lean` (WIP, not build-verified).

## Active Approach
Approach A (module structure / companion-similarity), entered via its minimal multi-block
case: reduce the coprime merge to `minpoly D = charpoly D = p*q` and invoke the scaffold's
`nonderogatory_iff_similar_to_companion`. Lemma chain L1–L5 documented in knowledge.md.

## Attempt Count
- Total attempts: 1 (ORIENT survey; no Lean compiled — tooling blackout)
- Current approach attempts: 1
- Approaches tried: 1

## Blockers
- Build tooling blackout: Docker containerd blob I/O error + Aristotle 404. No new Lean
  could be compiled this session; deliverable is the grounded ORIENT design.
- Full RCF is >1000-line (Mathlib-PR-scale); intentionally deferred behind the coprime
  merge increment.

## Next Action
Once build tooling recovers: implement L2 (`charpoly_companionMx`), then L1
(`minpoly_fromBlocks_eq_lcm`, the lynchpin), then assemble L3/L5 and the merge theorem
`companion_blockmerge_coprime`. See knowledge.md §Next Steps.
