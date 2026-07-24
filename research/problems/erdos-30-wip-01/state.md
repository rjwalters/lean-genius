# Research State: erdos-30-wip-01

## Current State
**Phase**: ACT
**Path**: full
**Since**: 2026-07-24T01:30:00-07:00
**Iteration**: 8

## Current Focus
Exact Sidon table h(N) = sidonNumber N. COMPLETE for h(0..29) as of the
2026-07-24 session (h(29)=7 via a VERIFIED BACKTRACKING SEARCH: pruned
`searchOK` engine + completeness lemma + `decide +kernel` evaluation of
`searchOK {0,29} 1 28 6 = false`; span dichotomy chains span ≤ 28 to the
h(28) mod-4 theorem).

## Active Approach
Residue-class double counting against forced perfect rulers at the wall
values N = k(k−1)/2 (h(10) parity, h(15) mod-3, h(21) parity, h(28) mod-4);
chained span dichotomy for the in-between values, with the span-N branch now
discharged by the VERIFIED BACKTRACKING ENGINE (`searchOK` +
`searchOK_complete`, parametric in the interval) instead of flat
powersetCard kernel searches. `SidonCheck` converse bridge certifies
witnesses with one `decide`.

## Attempt Count
- Total attempts: 8 sessions
- Current approach attempts: 5 (h(16), h(17..21), h(22..27), h(28), h(29) — all landed)
- Approaches tried: parity wall, mod-3 class count, span dichotomy, mod-4 double count, verified backtracking search

## Blockers
None for h(30..33): the backtracking engine reduces each remaining wall to
one `decide +kernel` evaluation (`searchOK {0,N} 1 (N−1) 6 = false`) plus
the copy-paste span dichotomy with the chain anchor moved up one. Kernel
cost grows with N but stays far below the (infeasible, ≥3 CPU-h) flat
C(N−1,6) enumeration. After h(33): h(34) = 8 needs the 8-mark optimal-ruler
WITNESS {0,1,4,9,15,22,32,34} (easy, SidonCheck bridge) — then the table
hits the 9-element frontier (optimal 9-mark span 44). Beyond the table:
DEEP targets only.

## Next Action
h(30..33) via the engine (one session can likely take all four: each is a
searchOK kernel theorem + shifted dichotomy). Then h(34)=8 via the optimal
8-mark ruler witness. DEEP targets unchanged: Singer √N lower bound,
N^{1/4} refinement, $1000 N^ε conjecture.
