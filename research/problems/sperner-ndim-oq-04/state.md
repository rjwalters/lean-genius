# Current State

**Phase**: BLOCKED
**Path**: full
**Since**: 2026-04-27T00:00:00.000Z (BLOCKED triage by Session 9)
**Iteration**: 9

## Current Focus

Final remaining sorry: `walkTrace_reversal` (line ~980) inside
`bdry_all_even_of_no_fc_walks` of `proofs/Proofs/SpernerNDimOQ04.lean`.

```
show kuhnPathStart c K hKuhn sₙ (Fin.last d) hdoor_n hbdry_n = p.1
```

`kuhnPathStart` returns only the FINAL simplex of the walk; it forgets
the intermediate path. The proof needs to access the entire walk
SEQUENCE in order to reverse it. Current `WalkValid` invariant tracks
door records but not the linear order of the trace.

## Active Approach

None. **BLOCKED** until one of two infrastructure paths is committed:

**Path A — `kuhnWalkSeq` (~150 lines)**
Define `kuhnWalkSeq : KuhnState → ℕ → List (K.Simplex × Fin (d+1) × Fin (d+1))`
returning per-step `(sᵢ, k_in_i, k_out_i)`. Prove length, adj-chain,
and reversal lemmas. Use to close `walkTrace_reversal`.

**Path B — Mathlib `SimpleGraph` (~200+ lines)**
Define the door graph as `SimpleGraph K.Simplex` with `s ~ s'` iff
`∃ k k', K.adj s k = some(s', k')`. Prove max degree ≤ 2 under
`IsKuhnCompatible`. Use Mathlib's `SimpleGraph.Walk.reverse`.

## Blockers

The same single `walkTrace_reversal` sorry has remained across 9
sessions because closing it requires multi-session infrastructure
work (Path A or B above), not a single tactical insight. Per the
research-rules memory: "If 3+ sessions stuck on same sorry: flag as
BLOCKED, move on."

## Next Action

When unblocked: spawn a focused multi-session push to commit Path A
(`kuhnWalkSeq`) as separate infrastructure, then close `walkTrace_reversal`.
Alternative defensible position: re-axiomatize `kuhn_path_existential`
(Session 7 form) at the cost of 1 axiom — defensible because the
result essentially restates Sperner's lemma constructively.

## Attempt Counts

- Total attempts: 9 sessions
- Current approach attempts: 0 (BLOCKED)
- Approaches tried: 2 (direct induction; SimpleGraph framing — both abandoned)
