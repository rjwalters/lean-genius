# Research State: legendre-partial-oq-04

## Current State
**Phase**: COMPLETED (extended)
**Path**: full
**Since**: 2026-06-27T11:33:01-07:00
**Iteration**: extension session 2026-07-04 (researcher-6)

## Current Focus
Faithfulness of the formalization: proved the split-interval `OppermannConjecture`
is EQUIVALENT to Oppermann's original 1882 two-sided formulation
`OppermannClassical` (a prime in each of `(n²−n, n²)` and `(n², n²+n)` for all
`n > 1`). This certifies the file's split statement is a faithful rendering of the
historical conjecture.

## Active Approach
Elementary re-indexing: the lower interval `((n+1)²−(n+1), (n+1)²)` of the
classical form at `n+1` equals the upper half `(n²+n, (n+1)²)` of the split gap at
`n`, since `(n+1)² − (n+1) = n²+n`. The only boundary input is the trivial prime
`3 ∈ (2,4)` (the upper half of the gap at `n = 1`), proved outright.

## What was added this session (all VERIFIED, 0-axiom)
- `OppermannClassicalAt`, `OppermannClassical` — Oppermann's original 1882
  two-sided formulation.
- `classical_first_succ_iff_upper` — the re-indexing identity.
- `upper_half_one` — the boundary prime `3 ∈ (2,4)`.
- `oppermann_conjecture_iff_classical` — `OppermannConjecture ⟺ OppermannClassical`.

`#print axioms oppermann_conjecture_iff_classical` reports only
`propext, Classical.choice, Quot.sound` (genuinely 0-axiom). Build:
`docker-build.sh Proofs.LegendrePartialOQ04` → exit 0, 7744 jobs.

## Prior sessions (already on main)
- Statement + bounded `native_decide` verification (n ≤ 20); open conjecture as
  an `axiom`.
- `oppermann_at_implies_legendre_at`, `oppermann_at_two_primes` (Legendre + two
  primes per gap).
- Brocard mechanism `oppermann_at_four_primes_two_gaps` + total π-count form.
- π-counting equivalence `oppermann_at_iff_pi`.

## Blockers
None.

## Next Action
Remaining out-of-scope frontier: full Brocard over consecutive primes (sum the
adjacent-gap mechanism over `p..q-1`); or extend the computational range beyond
n = 20 with a fast certified sieve.
