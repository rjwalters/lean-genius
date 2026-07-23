# Research State: erdos-30-wip-01

## Current State
**Phase**: ACT
**Path**: full
**Since**: 2026-07-23T09:19:00-07:00
**Iteration**: 6

## Current Focus
Exact Sidon table h(N) = sidonNumber N. COMPLETE for h(0..27) as of the
2026-07-23 session (h(22..24)=6 via chained span dichotomy + kernel searches,
h(25..27)=7 via the optimal 7-mark Golomb ruler {0,1,4,10,18,23,25}).

## Active Approach
Span dichotomy (slide-down by minimum + pinned-endpoint kernel search),
chained across consecutive N. `SidonCheck` converse bridge certifies
witnesses with a single `decide`.

## Attempt Count
- Total attempts: 6 sessions
- Current approach attempts: 3 (h(16), h(17..21), h(22..27) — all landed)
- Approaches tried: parity wall, mod-3 class count, span dichotomy

## Blockers
h(28..33) wall: counting goes slack for card-8 at N=28 (8·7 = 56 = 2·28);
optimal 8-mark ruler {0,1,4,9,15,22,32,34} has span 34 → six values each
needing per-N nonexistence of an 8-element Sidon set, with C(N−1,6)-scale
kernel searches (~296k candidates at N=28, growing). Elementary layer is
near-saturated.

## Next Action
Either attack h(28) with a smarter pruned search (backtracking encoded as a
decidable predicate rather than raw subset enumeration), or switch to DEEP
targets: Singer √N lower bound, N^{1/4} refinement, $1000 N^ε conjecture.
