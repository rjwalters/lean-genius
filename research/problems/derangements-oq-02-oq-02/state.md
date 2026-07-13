# Current State

**Phase**: COMPLETED
**Since**: 2026-04-04 (gallery entry dated; record stub left behind)
**Iteration**: 2

## Current Focus

State synchronization (doc-only). The Lean formalization has been complete
since at least 2026-04-04, but `state.md` was left in the seeker-init
"Phase: NEW" stub. This update reconciles the markdown record with the
gallery and JSON record (`currentState.phase = "COMPLETED"`,
`knowledge.progressSummary = "COMPLETE: All proofs done. 0 sorries, 0
axioms. 12 theorems in DerangementsOQ02OQ02.lean"`).

## Verified Status — Per-File Inventory

All twelve Derangement Lean files are sorry-free and axiom-free as of this
sync. Counts confirmed against `proofs/Proofs/Derangements*.lean` via
`grep -cE "^[[:space:]]*sorry[[:space:]]*$|:= sorry$|:= by sorry$"` (refined
to exclude docstring/comment mentions of the word "sorry").

| File                                  | Lines | Theorems | Defs | Axioms | Sorries |
|---------------------------------------|-------|----------|------|--------|---------|
| Derangements.lean                     |  228  |    10    |   0  |    0   |    0    |
| DerangementsConvergence.lean          |  283  |    14    |   2  |    0   |    0    |
| DerangementsConvergenceOQ01.lean      |  153  |     7    |   1  |    0   |    0    |
| DerangementsConvergenceOQ01OQ01.lean  |  148  |     7    |   0  |    0   |    0    |
| DerangementsConvergenceOQ03.lean      |   89  |     1    |   0  |    0   |    0    |
| DerangementsOQ02.lean                 |  358  |    10    |   1  |    0   |    0    |
| DerangementsOQ02OQ01.lean             |  124  |     6    |   0  |    0   |    0    |
| **DerangementsOQ02OQ02.lean**         |**250**|  **12**  | **0**| **0**  | **0**   |
| DerangementsOQ03.lean                 |  406  |    22    |   2  |    0   |    0    |
| DerangementsOQ03OQ01.lean             |  244  |     9    |   0  |    0   |    0    |
| DerangementsOQ03OQ01OQ02.lean         |  413  |    12    |   1  |    0   |    0    |
| DerangementsOQ03OQ02.lean             |  383  |    13    |   3  |    0   |    0    |
| **Totals**                            |**3079**|**123**  |**10**| **0**  | **0**   |

Note: `src/data/research/problems/derangements-oq-02-oq-02.json` still
reports stale `sorryCount` values for `DerangementsConvergenceOQ01.lean`
(4) and `DerangementsOQ02.lean` (1). Both files contain zero real tactic
sorries; the 4+1 occurrences are docstring text ("proved by sorry",
"modulo alternating series sorry", "round trips are sorry"). JSON
`leanFiles` drift is outside the scope of a state-sync PR and should be
addressed by the auditor / mechanic via the standard
`audit/sync-derangements-*` channel.

## Main Results (DerangementsOQ02OQ02.lean)

1. `sum_fixedPoints_eq_factorial`: For `n ≥ 1`,
   `∑_{σ : Perm (Fin n)} |Fix σ| = n!`. Equivalently, the expected number
   of fixed points of a uniform random permutation is 1. Proved via
   Burnside's lemma (`MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group`)
   plus transitivity of `Perm (Fin n)` on `Fin n`.

2. `weighted_partition_identity`: For `n ≥ 1`,
   `∑_{k=0..n} k · C(n,k) · D(n-k) = n!`. The generating-function
   identity connecting the partial derangement formula
   `S(n,k) = C(n,k) · D(n-k)` to first-moment data; proved by
   double-counting via `Finset.sum_fiberwise_of_maps_to`.

3. Closed-form verifications (`native_decide`) for `n ∈ {1, 2, 3, 4}` of
   both `sum_fixedPoints` and `weighted_sum`.

## Axiom Inventory

None. The proof closes against Mathlib only; no `axiom` declarations and
no assumption-carrying structure fields. `meta.json` correctly reports
`status: "verified"`, `badge: "original"`, `axiomCount: 0`,
`assumptions: "None."`.

## Blockers

None.

## Forward Levers (Optional Follow-ups, Out of Scope Here)

- **Higher moments**: extend the first-moment identity
  `E[#Fix] = 1` to `E[#Fix·(#Fix − 1)] = 1` (factorial moments), giving
  `Var(#Fix) = 1` via Burnside on `Perm (Fin n)` acting on ordered pairs.
- **Generating-function polynomial**: define `G_n(t) := ∑_k S(n,k)·t^k`
  and prove `G_n(1) = n!`, `G_n'(1) = n!`, recovering both the count and
  the first-moment identity from a single polynomial identity. Currently
  the identities are proved separately.
- **JSON drift cleanup**: `leanFiles` entries for two siblings still
  report nonzero sorries (see note above) — defer to auditor.

## Honesty Block

- Gallery meta.json: `status: "verified"`, `badge: "original"`, 0 sorries,
  0 axioms, 13 theorems, 249 lines (matches Lean source within +/-1).
- No assumptions are encoded in structures or typeclasses; this satisfies
  the project's axiom-integrity policy for the `verified`/`original`
  badge.
- This PR touches `state.md` only. No `.lean`, `.json`, `meta.json`,
  `annotations.json`, or `knowledge.md` edits.

## Attempt Counts

- Total attempts: 2 (per JSON `currentState.attemptCounts.total`)
- Current approach attempts: 2
- Approaches tried: 1 (Burnside + double-counting)
