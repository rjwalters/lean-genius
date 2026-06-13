# Research State: erdos-szekeres-oq-01

## Current State
**Phase**: ACT
**Path**: full
**Since**: 2026-06-10T02:55:00-07:00
**Iteration**: 3

## Current Focus
ACT-1 complete (S2, #22772): `maxIncLen`/`maxDecLen` defined via `Nat.findGreatest`
(Classical, noncomputable) plus singleton witnesses `hasIncreasingEndingAt_one` /
`hasDecreasingEndingAt_one` and lower bounds `one_le_maxIncLen` / `one_le_maxDecLen`
via `Nat.le_findGreatest` (commit f6642a8eeeb). Refactored
`HasIncreasingEndingAt`/`HasDecreasingEndingAt` positional disjunction to use
`j.val = len - 1` (fixes `Fin (len - 1 + 1)` vs `Fin len` type mismatch).
Docker 3058 jobs clean. File 281 → 344 LOC. Axiom count unchanged at 2.

## Active Approach
Assign each index `i` the pair `(a_i, b_i)` where `a_i = maxIncLen f i` is the
longest increasing-subsequence length ending at `i` and `b_i = maxDecLen f i` is
the longest decreasing one. If no increasing run of length `r` and no decreasing
run of length `s` exist, all pairs lie in the grid `(r-1) × (s-1)`; the pigeonhole
on an injective position→pair map yields the Erdős–Szekeres bound. The remaining
formal burden is the injectivity of that map.

## Attempt Count
- Total attempts: 2
- Current approach attempts: 2
- Approaches tried: 1

## Blockers
None. (Next step is build-gated on Docker availability for verification.)

## Next Action
ACT-2: Prove the key extension lemma `maxIncLen_lt_of_lt` — for `i < j : Fin n`
with `f i < f j`, `maxIncLen f i < maxIncLen f j`. Strategy: extract witness
`k : Fin L → Fin n` from `HasIncreasingEndingAt f i L`; define `k'` on `Fin (L+1)`
appending `j` after `k`'s end-position `i` (using the refactored predicate
requirement `j.val = L` for the last index); verify `StrictMono` positions and
values, then `Nat.le_findGreatest` gives `maxIncLen f j ≥ L+1`. Symmetric for
`maxDecLen` under `f j < f i`. Target +60–100 LOC.
