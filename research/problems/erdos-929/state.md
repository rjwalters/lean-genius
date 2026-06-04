# Current State

**Phase**: ACT
**Since**: 2026-06-04T00:00:00Z
**Iteration**: 3

## Current Focus

Structural threshold infrastructure for S(k). With the new
`smoothThreshold_ge_three`, we have 3 ≤ S(k) ≤ k+1 for k ≥ 2 in addition to
monotonicity. The conjecture S(k) ≥ k^{1−o(1)} remains a Prop definition;
formalizing genuine sieve bounds requires Mathlib analytic number theory
infrastructure not yet present.

## Active Approach

Lift k=2 emptiness/subset arguments to general k ≥ 2 via the
`smoothBlockSet_antitone` lemma. This gives concrete strict lower bounds at
the bottom of the threshold without requiring sieve theory.

## Blockers

Mathlib lacks the sieve-theory and prime-gap infrastructure to formalize
Rosser's k^{1/2−o(1)} lower bound or the FGKMT upper bound.

## Next Action

Optional: prove S(3) = 3 specifically by combining `smoothThreshold_ge_three`
with a positive-density witness at x = 3 (e.g., the AP n ≡ 1 mod 6 makes
n+1, n+2, n+3 cover residues 2, 3, 4 mod 6, all with minFac ≤ 3).

## Attempt Counts

- Total attempts: 3
- Current approach attempts: 1
- Approaches tried: 1 (general antitone lift)
