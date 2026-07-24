# Research State: erdos-30-wip-01

## Current State
**Phase**: ACT
**Path**: full
**Since**: 2026-07-23T10:45:00-07:00
**Iteration**: 7

## Current Focus
Exact Sidon table h(N) = sidonNumber N. COMPLETE for h(0..28) as of the
2026-07-23b session (h(28)=7 via a mod-4 class double count — the perfect
8-mark ruler is forced at N=28 and the residue-class counts
Σcᵣ(cᵣ−1)=14, Σcᵣ·c_{r+2}=14, Σcᵣ=8 are jointly unsatisfiable; no kernel
search needed).

## Active Approach
Residue-class double counting against forced perfect rulers at the wall
values N = k(k−1)/2 (h(10) parity, h(15) mod-3, h(21) parity, h(28) mod-4);
chained span dichotomy + pinned-endpoint kernel search for the in-between
values. `SidonCheck` converse bridge certifies witnesses with one `decide`.

## Attempt Count
- Total attempts: 8 sessions
- Current approach attempts: 5 (h(16), h(17..21), h(22..27), h(28), Erdős–Turán √N lower bound — all landed)
- Approaches tried: parity wall, mod-3 class count, span dichotomy, mod-4 double count, Erdős–Turán construction + Bertrand

## Blockers
h(29..33) wall: perfect ruler no longer forced (28 diffs in {1,…,N} miss
N−28 values); span dichotomy returns but the span-N branch needs per-N
nonexistence with C(N−1,6)-scale kernel searches (~376k at N=29). Mod-4
alone checked INSUFFICIENT at N=29 (a {4,2,1,1} arrangement with the missing
value ≡ 2 mod 4 survives). Elementary layer near-saturated.

## Next Action
DONE 2026-07-24: Erdős–Turán construction landed — √N/4 ≤ h(N) ≤ √(2N)+1
for N ≥ 49, order h(N) ≍ √N settled elementarily (former DEEP target
"Singer √N lower bound" achieved via Erdős–Turán instead; no projective
planes). h(29) narrowed: missing diff d ≡ 2 (mod 4) (prior "d odd" note was
WRONG — mod-2 class count forces d even). Remaining: fell h(29) via
mod-6/mod-8 cross counts on the narrowed d-list or the ≈192k span-29
search; or DEEP: N^{1/4} refinement, Singer (1−o(1))√N constant, $1000
N^ε conjecture.
