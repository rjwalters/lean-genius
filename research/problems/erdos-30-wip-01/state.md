# Research State: erdos-30-wip-01

## Current State
**Phase**: ACT
**Path**: full
**Since**: 2026-07-24T00:00:00-07:00
**Iteration**: 8

## Current Focus
Two-sided √N-order bracket LANDED (session 2026-07-24): the Erdős–Turán
(1941) modular construction — for odd prime p the set
{2p·i + (i² mod p) : i < p} is Sidon in {0,…,2p²−1} — plus Bertrand
(`Nat.bertrand`) gives `sidonNumber_gt_sqrt : h(N) > ⌊√(N/8)⌋` (N ≥ 32),
real form `√N/4 ≤ h(N)`, and the bracket
`sidonNumber_sqrt_bracket : √N/4 ≤ h(N) ≤ √(2N)+1`. The polynomial gap
(previous lower bound was logarithmic, powers of two) is CLOSED.

## Active Approach
Erdős–Turán construction proof = base-2p digit separation (`etMap_add_eq`,
residues < p never carry) + quadratic uniqueness over 𝔽_p
(`pair_eq_of_sum_sq`, `linear_combination` workhorse; 2 invertible for
p > 2). Exact table h(0..28) stands via the residue-class ladder
(h(10)/h(21) parity, h(15) mod-3, h(28) mod-4) + span dichotomy searches.

## Attempt Count
- Total attempts: 8 sessions
- Current approach attempts: 1 (Erdős–Turán √N lower — landed)
- Approaches tried: parity wall, mod-3 class count, span dichotomy,
  mod-4 double count, Erdős–Turán modular construction

## Blockers
h(29..33) wall: perfect ruler no longer forced (28 diffs in {1,…,N} miss
N−28 values); span dichotomy returns but the span-N branch needs per-N
nonexistence with C(N−1,6)-scale kernel searches (~376k at N=29). Mod-4
alone checked INSUFFICIENT at N=29 (a {4,2,1,1} arrangement with the missing
value ≡ 2 mod 4 survives). Elementary layer near-saturated.

## Next Action
Remaining targets are all DEEP: sharp constants (Singer projective-plane
lower `(1−o(1))√N`; Lindström/BFR upper `√N + N^{1/4} + 1`), the $1000
`N^ε`-error conjecture (open Prop), or the h(29..33) table wall (new
invariant — mod-3×mod-4 combination / endpoint sum-collision pruning — or
a ~376k kernel search). Treat elementary vein as SATURATED.
