# Current State

**Phase**: STATEMENT_REVISION_NEEDED
**Since**: 2026-06-09T20:35:00Z
**Iteration**: 2

## Current Focus

Discovered the transcribed axiom `erdos_1210` is **unsound** as literally
stated. Adding machine-checked counterexample and flagging the formalization
for statement-revision.

## Active Approach

S2 COUNTEREXAMPLE — Construct a concrete witness (n = 5, A = {4}) where the
hypotheses of `erdos_1210` hold but the conclusion fails. Verify in Lean.

## Findings (S2)

The transcribed statement
`∑_{a ∈ A} 1/(n-a) ≤ ∑_{p < n, p prime} 1/(n-p)`
admits the following counterexample at n = 5:

- A = {4} trivially satisfies `ValidSubset 5 A` (1 ≤ 4 < 5) and
  `PairwiseCoprime A` (singleton).
- LHS = 1/(5-4) = 1.
- RHS = 1/(5-2) + 1/(5-3) = 1/3 + 1/2 = 5/6 ≈ 0.833.
- 1 > 5/6, so the conjectured inequality FAILS.

Hence the existing `axiom erdos_1210` and its four consequence theorems are
unsound and should be refactored once the intended Erdős statement is
recovered from [Er77c] / [Er80].

## Blockers

- Source-text access: cannot directly fetch the original Erdős papers
  ([Er77c] Erdős 1977c, [Er80] Erdős 1980) to recover the unstated hypothesis
  (e.g., a > n/2, a > √n, or a different weight like 1/a).
- Without the corrected statement, the axiom cannot be replaced — only flagged.

## Next Action

S3 — A future iteration should:
  1. Locate the Erdős source for problem 1210 (likely contains the missing
     hypothesis).
  2. Replace the unsound axiom with the corrected statement (or with a verified
     theorem if the corrected version is provable).
  3. Refactor or remove the four consequence theorems that depend on the
     current axiom.

## Attempt Counts

- Total attempts: 2
- Current approach attempts: 1 (S2 counterexample)
- Approaches tried: 2 (S1 formalization → axiomatization; S2 falsification)
