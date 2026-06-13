# Current State

**Phase**: AXIOMATIZED (statement corrected)
**Since**: 2026-06-13T08:00:00Z
**Iteration**: 3

## Current Focus

S3 RESOLVED the S2 blocker. Recovered the correct Erdős statement directly from
erdosproblems.com/1210 (via curl; WebFetch was 403-blocked). The earlier
"unsoundness" was a transcription error, not a flaw in Erdős's conjecture.

## What the source actually says

> Let A ⊆ [1,n) be a set of integers such that (a,b)=1 for all distinct
> a,b ∈ A. Is it true that ∑_{a∈A} 1/(n-a) ≤ ∑_{p<n} 1/p + O(1)?

Two corrections vs. the original Lean transcription:
1. **RHS is ∑_{p<n} 1/p** (prime reciprocals, the Mertens sum ~ log log n),
   NOT ∑_{p<n} 1/(n-p).
2. **There is a +O(1) additive term** — the inequality is asymptotic up to an
   absolute constant, not exact.

The S2 counterexample (n=5, A={4}: LHS=1 > 5/6) does NOT refute the real
conjecture; the 1/6 gap is absorbed by the O(1) constant.

Erdős's own note ([Er80]): he "did not state [this] quite correctly" in
[Er77c]. The [Er80] reformulation concerns primes in an interval: if
n < q₁ < ⋯ < q_k ≤ m are the primes in (n,m], then
∑ 1/(qᵢ-n) < ∑_{p<m-n} 1/p + O(1). See also #460, #950.

## Action taken (S3)

Rewrote `proofs/Proofs/Erdos1210Problem.lean` (Docker-verified, 3058 jobs):
- New def `primeReciprocalSum n = ∑_{p<n} 1/p` (corrected RHS).
- Replaced the unsound exact axiom with the honest O(1) form:
  `axiom erdos_1210 : ∃ C, ∀ n ≥ 3, ∀ pairwise-coprime A ⊆ [1,n),
   ∑ 1/(n-a) ≤ primeReciprocalSum n + C`.
- Kept all verified structural lemmas (primes_coprime, primesBelow_*,
  pairwiseCoprime_at_most_one_even, primeReciprocalSum_nonneg/pos).
- Reframed the n=5 case: `naive_statement_fails_at_five` (the C=0 version is
  false) + `corrected_statement_consistent_at_five` (any C ≥ 1/6 works), proving
  the O(1) term is essential.
- Updated gallery `meta.json` to the corrected statement and counts
  (14 theorems, 4 defs, 1 axiom, 230 lines).

## Blockers

None remaining for the statement. The conjecture itself is open and "cannot be
resolved with a finite computation" (per the source).

## Next Action

S4 — explore a partial bound: can one prove ∑_{a∈A} 1/(n-a) ≤ C·log log n
(or any explicit unconditional upper bound) for pairwise coprime A, e.g. via
the "at most one even element" structure plus a sieve/Mertens estimate? That
would be a genuine partial result toward the open conjecture.

## Attempt Counts

- Total attempts: 3
- Approaches tried: 3 (S1 formalization/axiomatization; S2 falsification of the
  mis-transcribed statement; S3 source recovery + corrected re-axiomatization)
