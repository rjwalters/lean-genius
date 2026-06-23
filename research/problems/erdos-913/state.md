# Current State

**Phase**: ACT (axiomatized — single axiom is a genuine open Bunyakovsky-type conjecture)
**Path**: full
**Last Updated**: 2026-05-08 (Iteration 8, researcher-11 — state.md sync)
**Iteration**: 8

## Current Focus

The Lean formalization in `proofs/Proofs/Erdos913Problem.lean`
(344 lines, 16 theorems, 0 sorries, 1 axiom) **completes the conditional
result**: if there are infinitely many primes `p` such that `8p² − 1` is
also prime, then there are infinitely many `n` with the distinct-exponent
property `HasDistinctExponents n`.

The single remaining axiom — `infinite_8p_sq_minus_1_primes` — is a
**Bunyakovsky-type conjecture** about prime values of the polynomial
`8p² − 1` evaluated at primes `p`. This is genuinely open and
appropriate as an axiomatic limit; eliminating it would be major
mathematical news (Bunyakovsky's conjecture remains open in general).

## Iteration History

- **Iter 1** (2026-03-26, PR #7259): bootstrap + 4 axioms eliminated
  across erdos-374/913/1020.
- **Iter 2** (2026-03-27, PR #7258): infrastructure + false-axiom fix.
- **Iter 3** (2026-03-27, PR #7265): proved further axioms (with
  erdos-689, erdos-406).
- **Iter 4** (2026-03-29, PR #7676): Mersenne conditional + related
  conditional results.
- **Iter 5** (2026-04-26, PR #13369): erdos-913 completion (alongside
  erdos-827 audit).
- **Iter 6** (2026-04-27, PR #13630, #13631): axiom line-range and
  duplicate-section audit fixes; tracker mark issues-fixed.
- **Iter 7** (2026-05-07, PR #16559): JSON reconciliation with
  completed state.
- **Iter 8** (2026-05-08, this PR, researcher-11): state.md sync to
  reflect actual gallery state (was at iter 1 NEW for ~3 months).

## Built Items

- **`HasDistinctExponents (n : ℕ) : Prop`** — `Set.InjOn` on
  `(n * (n + 1)).factorization` over the prime factors of `n(n+1)`.
  Uses Mathlib's `Nat.factorization` and `Nat.primeFactors`.
- **`DistinctExponentSet : Set ℕ`** — the set of all `n` with the
  distinct-exponent property.
- **`PrimePairs8 : Set ℕ`** — primes `p` such that `8p² − 1` is also
  prime. The Bunyakovsky-type set whose infinitude is conjectural.
- **`erdos913_conditional`** — the main conditional theorem: if
  `PrimePairs8` is infinite, then `DistinctExponentSet` is infinite.
- **16 theorems total** including coprimality of `n` and `n+1`,
  factorization combinator lemmas, the `8p² − 1 = (some factorization)`
  identity for primes `p`, and the conditional construction.

## Active Approach

The single axiom `infinite_8p_sq_minus_1_primes` is a **Bunyakovsky-type
conjecture** — specifically, that the polynomial `8x² − 1` takes
infinitely many prime values as `x` ranges over primes. Bunyakovsky's
conjecture (1857) is genuinely open: no irreducible polynomial of
degree ≥ 2 has been proven to produce infinitely many primes (the
twin-prime conjecture is the smallest case for `x² + x − 1` analogues).

Eliminating this axiom would require either:
- Resolving Bunyakovsky's conjecture (or a substantial special case).
- Reformulating the result around a different sufficient condition
  whose infinitude is provable.

Neither is in scope for incremental Lean work.

## Blockers

None for axiom-side work. The single axiom is appropriate.

## Next Action

This slug is **substantially complete**. The remaining axiom
(`infinite_8p_sq_minus_1_primes`) is appropriate and not removable
without major mathematical advances.

**Iter 9 candidate** (incremental polish, optional): add a few more
explicit witness-checking theorems for small primes `p`. For instance,
`p = 2` gives `8·4 − 1 = 31` (prime), `p = 3` gives `8·9 − 1 = 71`
(prime), `p = 5` gives `8·25 − 1 = 199` (prime), etc. Adding ~5 small
explicit witnesses via `decide` / `native_decide` would document
the empirical evidence supporting the conjecture and serve as a
sanity-check for the construction logic.

The slug could also be marked `completed` in the candidate pool
(rather than `available`) since the substantive work is done.

## Attempt Counts

- Total attempts: 8
- Current approach attempts: 1 (state.md sync, this PR)
- Approaches tried: bootstrap + axiom elimination (Iter 1–4);
  Mersenne conditional + completion (Iter 4–5); audit fixes (Iter 6);
  JSON reconciliation (Iter 7); state.md sync (Iter 8).

## References

- `proofs/Proofs/Erdos913Problem.lean` — main file (344 lines, 16
  theorems, 1 axiom, 0 sorries).
- `src/data/proofs/erdos-913/meta.json` — gallery integration
  (status: `axiomatized`).
- Erdős [Er82c, p. 28] — original problem.
- Bunyakovsky's conjecture (1857) — generic open question for
  prime values of irreducible polynomials.
