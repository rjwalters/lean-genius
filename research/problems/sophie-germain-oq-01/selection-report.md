# Selection Report: sophie-germain-oq-01

**Selected**: 2026-04-23
**By**: Seeker (SELECT mode)
**Composite Score**: 27

## Problem

**ID**: sophie-germain-oq-01
**Title**: Sophie Germain Primes: Are There Infinitely Many?
**Tier**: A
**Significance**: 7/10
**Tractability**: 2/10
**Knowledge Score**: 0 (EMPTY)

## Selection Rationale

1. **EMPTY knowledge tier** grants highest priority. No prior research exists for this problem.
2. **Significance 7**: Sophie Germain primes are foundational in cryptography (safe primes
   used in Diffie-Hellman and RSA key generation) and the infinitude question is a natural
   analogue of the twin prime conjecture. Lean formalization of the formal statement and
   related Mathlib infrastructure has clear value.
3. **Tractability 2**: the conjecture is open. As with the twin prime and Goldbach problems
   selected in this batch, the researcher should produce an axiomatized statement formalization,
   document the connection to safe primes, and identify any Mathlib sieve infrastructure.
4. Selected together with `twin-primes-special-oq-01` and `weak-goldbach-oq-01` as a natural
   cluster of prime conjecture formalizations — analogous problems benefit from shared
   infrastructure discoveries.

## Rejection Summary

- **Candidates considered**: 34 available (3 with no prior workspace)
- **Candidates rejected**: 31 with existing workspaces from prior batches
- **Confidence**: high — lowest of the 3 new problems by composite score (sig=7 vs 8)

## Related Gallery Proofs

- `twin-primes-special-oq-01`: analogous prime pair infinitude conjecture
- `weak-goldbach-oq-01`: additive prime conjecture (same batch)
- `prime-number-theorem`: asymptotic prime density infrastructure

## Suggested First Steps

1. **OBSERVE**: Read problem.md. Search Mathlib for `SophieGermain`, `safePrime`, or
   manually check if `Nat.Prime p ∧ Nat.Prime (2*p+1)` has any existing theorems.
2. **ORIENT**: Check `Mathlib.NumberTheory.Primorial` and sieve methods for any
   relevant partial results. Document what's known about the asymptotic density of
   Sophie Germain primes (conjectured ~ C·n/(log n)²).
3. **DECIDE/ACT**: Formalize `∃ᶠ p in atTop, Nat.Prime p ∧ Nat.Prime (2*p+1)` as
   an axiom with documentation of computational evidence and the cryptographic connection.

## Pool Summary

| Status | Count |
|--------|-------|
| Available | 34 |
| In Progress | 559 |
| Completed | 1403 |
| Graduated | 3 |
| Blocked | 2 |
| **Total** | **2001** |

## Pool Health

Pool depth adequate (34 available). No refresh needed.
