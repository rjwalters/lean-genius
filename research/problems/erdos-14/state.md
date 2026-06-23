# Current State

**Phase**: COMPLETED
**Since**: 2026-05-03T20:00:00Z
**Iteration**: 1

## Result

Erdős Problem #14 formalized in `Proofs/Erdos14Problem.lean`
(110 lines, 0 sorries, 2 axioms).

## What Was Built

1. **`def Erdos14a : Prop`**: Open conjecture (a) — for all A ⊆ ℕ and ε > 0,
   `∃ C > 0, ∃ᶠ N, C * N^{1/2-ε} ≤ nonUniqueSumCountInf A N`.

2. **`def Erdos14b : Prop`**: Open conjecture (b) — ∃ A ⊆ ℕ with
   `nonUniqueSumCountInf A =o[atTop] N^{1/2}`.

3. **`axiom ess_upper_lower_bound`**: Erdős-Sárközy-Szemerédi combined result —
   ∃ A with `nonUniqueSumCountInf A N =O N^{1/2+ε}` eventually AND
   `≥ C * N^{1/3-ε}` frequently.

4. **`axiom erdos_freud_finite`**: Erdős-Freud finite bound —
   `nonUniqueSumCount A N < 2^{3/2} * N^{1/2}` for all finite A.

5. **`theorem non_unique_monotone`** (proved): nonUniqueSumCountInf is
   non-decreasing in N.

## Axiom Justification

- `ess_upper_lower_bound`: ESS construction requires probabilistic method +
  sieve theory; far beyond current Mathlib infrastructure.
- `erdos_freud_finite`: Erdős-Freud 1991 result requires intricate extremal
  combinatorics argument.

## Attempt Counts

- Total attempts: 1
- Current approach attempts: 1
- Approaches tried: 1
