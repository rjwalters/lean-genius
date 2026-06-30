# Current State

**Phase**: FORMALIZED (odd reduction proved; the Collatz conjecture itself open)
**Since**: 2026-06-26
**Iteration**: 1

## Current Focus

The Collatz conjecture — every n ≥ 1 reaches 1 under n ↦ n/2 (even), n ↦ 3n+1
(odd) — is OPEN and is NOT proved here. This session formalized the standard
**reduction to odd inputs**, axiom-free, in
`proofs/Proofs/CollatzStructuredOQ01.lean` (builds on `Proofs.CollatzStructured`,
without using that file's `collatz_conjecture` axiom).

## Active Approach

Three layers, all 0-axiom:

1. **One-step invariance** (`reachesOne_collatz_iff`): `ReachesOne (collatz n) ↔
   ReachesOne n`. Backward = prepend a step (unconditional); forward = drop the
   first iterate, with the base case `n = 1` handled by `collatz 1 = 4 = 2²`
   reaching 1 (parent's `pow_two_reaches_one`).

2. **Doubling/power-of-two invariance** (`reachesOne_two_mul_iff`,
   `reachesOne_pow_two_mul_iff`): `ReachesOne (2^m · n) ↔ ReachesOne n`. The
   parent only had the forward closure (`reaches_one_double`); the reverse comes
   from one-step invariance + `collatz (2n) = n`, and induction lifts it.

3. **Odd reduction** (`collatz_reduces_to_odd`): writing `n = 2^v₂(n) · oddPart n`
   with `oddPart n = ordCompl[2] n` odd and positive (Mathlib factorization API),
   `ReachesOne n ↔ ReachesOne (oddPart n)`, hence the conjecture for all n ≥ 1 is
   equivalent to the conjecture for odd n ≥ 1. Corollary
   `collatz_counterexample_odd`: counterexamples may be taken odd.

## Blockers

The Collatz conjecture itself is open and far beyond a formalization session.
The reduction narrows the search space (to odd inputs) but does not lower the
intrinsic difficulty.

## Next Action

- Push the reduction further: to `n ≡ 3 (mod 4)`, or reformulate on the
  Syracuse/accelerated odd map `n ↦ (3n+1)/2^v₂(3n+1)` and prove the analogous
  equireachability.
- Investigate residue-class invariants compatible with this reduction.

## Attempt Counts

- Total attempts: 1
- Current approach attempts: 1
- Approaches tried: 1
