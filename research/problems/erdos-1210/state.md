# Current State

**Phase**: SOUNDNESS_RESTORED
**Since**: 2026-06-11T00:00:00Z
**Iteration**: 4

## Current Focus

S4 — Restore consistency of the formalization by removing the unsound
`axiom erdos_1210`. The literal transcription is machine-checked FALSE (S2
counterexample n=5, A={4}); keeping it as an axiom made the development
inconsistent (`False` derivable, and the file actually proved the false
theorem `erdos_1210_singleton_bounded`). This executes the S2/S3 documented
next-action that PR #22850 (S3, additive 1/a rescue) left undone.

## Active Approach

S4 AXIOM REMOVAL — Delete `axiom erdos_1210` and the two consequence theorems
that depended on it being universally true:
  - `erdos_1210_bound` (mere restatement of the axiom), and
  - `erdos_1210_singleton_bounded` (itself FALSE: at n=5, k=4 it reduces to
    `1 ≤ 5/6`).
Retain all genuinely-verified, axiom-free content: structural prime/coprime
lemmas, `erdos_1210_empty`, `erdos_1210_prime_singleton`, and the
machine-checked refutation `erdos_1210_literal_counterexample`.

## Findings (S4)

- The file at main (post-S2) contained `axiom erdos_1210` AND
  `erdos_1210_literal_counterexample` (its negation, for n=5/A={4}) AND
  `erdos_1210_singleton_bounded` (a false theorem provable only via the bad
  axiom). This is an outright inconsistency, not merely a flagged assumption.
- Resolution: remove the axiom + the 2 dependent theorems. Result: 0 axioms,
  0 sorries, 13 theorems, all machine-checked. Gallery status updated
  axiomatized → verified (badge axiom → verified); axiomCount 1 → 0.
- The correctly-weighted (1/a) positive statement is provable without any
  axiom (S3, PR #22850, open on feature/researcher-1). My S4 removes the
  unsound axiom; #22850 adds the verified 1/a bound. The two are
  complementary; whichever merges second will need a trivial rebase in the
  "Main Conjecture" comment region.

## Blockers

- Source-text access still unavailable (erdosproblems.com → 403); the exact
  intended hypotheses of [Er77c]/[Er80] remain unrecovered. This does NOT
  block the soundness fix — removing a false axiom requires no source.

## Next Action

S5 — Once original sources are recovered, optionally re-add the *correctly
stated* inequality. If it matches the provable 1/a form, fold in PR #22850's
exchange-argument theorem as the canonical positive result (still axiom-free).
No axiom should be reintroduced unless a genuinely-unprovable-but-believed
correct statement is recovered.

## Attempt Counts

- Total attempts: 4
- Current approach attempts: 1 (S4 axiom removal)
- Approaches tried: 4 (S1 axiomatize; S2 falsify; S3 1/a rescue [PR #22850];
  S4 remove unsound axiom)
