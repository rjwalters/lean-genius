# Current State

**Phase**: COMPLETED
**Since**: 2026-03-23T04:30:45Z (registry graduated)
**Iteration**: 5
**Last Updated**: 2026-05-17

## Status Summary

Sum-Divides-Product Avoidance: structural lemmas + Van Doorn's
(25/28 + o(1))·N upper bound axiomatized; the underlying Erdős conjecture
(can A be substantially larger than the odd numbers?) remains open.
Registry graduated 2026-03-23 after PRs #3481 (oddNumbers + coprime),
#4970 (GCD characterization), #4984 (axiom elimination 2→1). Gallery
`meta.json` reflects current Lean state (198 LOC / 8 thm / 5 def / 1 axiom
/ 0 sorry, status `axiomatized`, badge `axiom`).

## Lean File Canonical Counts

`proofs/Proofs/Erdos327Problem.lean` (198 LOC):

| Surface       | Count |
|---------------|-------|
| theorem/lemma | 8     |
| def           | 5     |
| axiom         | 1     |
| sorry         | 0     |

## Axiom Inventory (1)

1. `vanDoorn_bound (N : ℕ) (A : Finset ℕ)` (line 53)
   — Van Doorn's (25/28 + o(1))·N upper bound: if |A| ≥ (25/28 + o(1))·N
   then A must contain a, b with a + b ∣ a·b. Axiomatized pending Lean
   formalization of the analytic-NT proof.

## Theorem Inventory (8)

- `sumDvdProd_iff_unitFraction` (line 70) — bridge to unit fractions
  (a + b ∣ a·b ⇔ 1/a + 1/b is a unit fraction); was an axiom until PR
  #4984 derived it from Mathlib divisibility lemmas
- `sumNotDvdProd_empty` (line 105) — trivial base case
- `sumNotDvdProd_singleton` (line 109) — trivial 1-element case
- `sumNotDvdProd_subset` (line 115) — monotonicity under ⊆
- `oddNumbers_sumNotDvdProd` (line 124) — the odd numbers in {1,…,N}
  satisfy SumNotDvdProd; gives the lower bound A ≈ N/2 (PR #3481)
- `coprime_sumNotDvdProd` (line 144) — pairwise-coprime pairs satisfy
  the avoidance condition (PR #3481)
- `sumNotDvdProd_of_pairwise_coprime` (line 158) — pairwise-coprime
  Finsets satisfy SumNotDvdProd globally
- `sumDvdProd_iff_reduced_divides_gcd` (line 174) — GCD characterization:
  a + b ∣ a·b iff (a/g + b/g) ∣ g where g = gcd(a,b) (PR #4970)

## Definition Inventory (5)

- `def SumNotDvdProd` (line 30) — main avoidance predicate
- `def SumNotDvdTwoProd` (line 34) — variant predicate (factor of 2)
- `noncomputable def maxAvoidSize` (line 38) — extremal function over
  subsets of {1,…,N}
- `def ErdosProblem327` (line 45) — formal problem statement
- `def ErdosProblem327_variant` (line 61) — formal variant statement

## Open Conjecture

The Erdős problem itself (can A be much larger than ≈ N/2?) remains open.
The standing axiom `vanDoorn_bound` encodes Van Doorn's published upper
bound (analytic number theory, beyond current Mathlib coverage). Further
axiom elimination would require Lean formalization of Van Doorn's paper —
a substantial dedicated project.

The SumNotDvdTwoProd variant (must |A| = o(N) if a+b ∤ 2·a·b for distinct
a,b?) has no Lean content beyond the definition; it is a sibling open
question.

## Blockers

None for the current state. The slug is at its honest rest-state pending
either (a) Lean formalization of Van Doorn's bound or (b) progress on the
underlying conjecture.

## Next Action

`COMPLETED` — no further iteration planned without external mathematics.
Pool flipped to `completed`; claim released. Re-open with a SCOPED phase
if Van Doorn's bound becomes formalizable or if the SumNotDvdTwoProd
variant gets traction.

## Attempt Counts

- Total attempts: 5 (iter 1 OBSERVE → iter 2 oddNumbers+coprime PR #3481
  → iter 3 GCD characterization PR #4970 → iter 4 axiom 2→1 PR #4984
  → iter 5 STATE-SYNC)
- Current approach attempts: 0 (rest state)
- Approaches tried: OBSERVE/enhance, structural-lemma-development,
  GCD-characterization, axiom-elimination-via-Mathlib, documentation sync

## Iteration Ledger

| Iter | Date       | Phase / Action                                         | PR     |
|------|------------|--------------------------------------------------------|--------|
| 1    | 2026-01-26 | OBSERVE — initial Lean file w/ 2 axioms + variants     | #1175  |
| 2    | 2026-03-11 | ACT — `oddNumbers_sumNotDvdProd` + coprime lemmas      | #3481  |
| 3    | 2026-03-22 | ACT — `sumDvdProd_iff_reduced_divides_gcd`             | #4970  |
| 4    | 2026-03-22 | ACT — eliminate `sumDvdProd_iff_unitFraction` (2→1)    | #4984  |
| 5    | 2026-05-17 | STATE-SYNC — docs catch up to gallery (registry T-55d) | (this) |
