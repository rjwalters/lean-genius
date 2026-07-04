# Research State: legendre-partial-oq-04

## Current State
**Phase**: COMPLETED (extended)
**Path**: full
**Since**: 2026-06-27T11:33:01-07:00
**Iteration**: extension session 2026-07-04 (researcher-11)

## Current Focus
Enriching the completed Oppermann entry with new 0-axiom structural theorems.
This session added **the Brocard mechanism** and the **total π-count form**.

## Active Approach
Honest hypothesis-taking implications from `OppermannAt` (never asserting the
open conjecture), proved by elementary interval arithmetic + `Finset.card`.

## What was added this session (all VERIFIED, 0-axiom)
- `oppermann_at_four_primes_two_gaps` — Oppermann at two *adjacent* gaps `n`,
  `n+1` ⟹ ≥ 4 primes in the double gap `(n², (n+2)²)`. The elementary
  combinatorial core of the classical **Oppermann ⟹ Brocard** implication.
- `oppermann_implies_four_primes` — its conjecture-level corollary.
- `oppermann_at_pi_total` / `oppermann_implies_pi_total` — total π-count form
  `π((n+1)²) − π(n²) ≥ 2`.
- `four_primes_2` — sanity corollary (≥ 4 primes in `(4,16)`) from `oppermann_2`,
  `oppermann_3`.

`#print axioms` on the two new structural theorems reports only
`propext, Classical.choice, Quot.sound` (genuinely 0-axiom). Build:
`docker-build.sh Proofs.LegendrePartialOQ04` → exit 0, 7744 jobs.

## Blockers
None. The remaining frontier (full Brocard over consecutive primes) is a
packaging step, recorded in `nextSteps`.

## Next Action
To assemble full Brocard from the mechanism: prove consecutive primes `p<q≥3`
satisfy `q ≥ p+2` (both odd) and sum `oppermann_at_four_primes_two_gaps`-style
adjacent-gap contributions over `p..q-1` to get `π(q²) − π(p²) ≥ 4`.
