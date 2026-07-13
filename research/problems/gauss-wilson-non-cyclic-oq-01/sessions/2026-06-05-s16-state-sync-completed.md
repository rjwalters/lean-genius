# S16 STATE-SYNC — Gallery JSON Sync to COMPLETED + Docker Re-Verify

**Date**: 2026-06-05
**Author**: researcher-1
**Phase**: STATE-SYNC (no Lean changes; gallery JSON catch-up)
**Iteration**: 16

## Outcome

**The slug is SOLVED and the gallery JSON now reflects it.** Pure doc-only state-sync: 0 Lean edits, 0 mathematical content changed; only the gallery-JSON `currentState` was advancing 11 iterations behind reality.

## What was found

`src/data/research/problems/gauss-wilson-non-cyclic-oq-01.json` showed:
- `currentState.iteration = 11`
- `currentState.focus = "S8 ACT shipped ..."` (the moment the Phase B sorry was discharged)
- `currentState.nextAction = "S9 ACT — close the Phase C non-cyclic-direction sorry ..."`
- `status: "active"`

But `state.md` and the Lean files show:
- **S15 ACT shipped 2026-05-30** (doc-drift cleanup, PR landed)
- **S12 ACT PR #19440 closed the Phase C sorry on 2026-05-16**
- **Phase A + B + C all build-verified, 0 sorries / 0 axioms slug-wide**

The JSON was stale by ~3 weeks. State.md tracked the post-S8 iterations (S9 PREP → S15 ACT) but the gallery JSON did not.

## What this iteration did

1. **Docker re-verified Phase C builds clean**: `./proofs/scripts/docker-build.sh Proofs.GaussWilsonNonCyclicOQ01` → `✔ [3066/3066] Built ... === Build succeeded ===`. Mathlib v4.26.0.
2. **Updated gallery JSON** `currentState.phase` (ACT → COMPLETED), `iteration` (11 → 15), `focus` (rewritten to reflect S15 ACT shipped + slug-wide solved status + 2026-06-05 re-verification), `nextAction` (rewritten to "None"), `attemptCounts.total` (10 → 15). Also updated `knowledge.progressSummary` to reflect the slug-solved state. Set `status: "completed"`.
3. **Marked slug COMPLETED in the pool** via `claim-problem.sh update gauss-wilson-non-cyclic-oq-01 completed`.

## What did NOT change

- **0 Lean files modified.** All three Phase files (A, B, C) remain at their S15 ACT post-cleanup state.
- **0 sorries, 0 axioms, 0 structure-encoded assumptions** slug-wide (unchanged).
- **No new mathematical content.**

## Counts after S16

| File | Lines | Theorems | Axioms | Sorries |
|------|-------|----------|--------|---------|
| `GaussWilsonNonCyclicOQ01A.lean` | 66 | — | 0 | 0 |
| `GaussWilsonNonCyclicOQ01B.lean` | 244 | — | 0 | 0 |
| `GaussWilsonNonCyclicOQ01.lean` | 257 | — | 0 | 0 |
| **Slug-wide** | **567** | — | **0** | **0** |

## Build status

**Docker-verified clean (2026-06-05)**: `./proofs/scripts/docker-build.sh Proofs.GaussWilsonNonCyclicOQ01` → `✔ [3066/3066] Built Proofs.GaussWilsonNonCyclicOQ01 (8.3s) === Build succeeded ===`. Mathlib v4.26.0.

## Honesty

This is a **state-sync only** iteration. Zero mathematical content, zero Lean code changes. The value is bringing the gallery JSON in line with the actual slug state, so that downstream consumers (pool selection, peer-reviewer, mechanic, deployer) see the correct "completed" status rather than a stale "active" with "next action = S9 ACT" (already done in S12 ACT 2026-05-16).

The slug has been solved since S12 ACT PR #19440 merged on 2026-05-16. The intervening S13–S15 iterations were housekeeping; this S16 is the JSON catch-up.

## What this slug actually proves

For the non-cyclic case of (ℤ/nℤ)ˣ with n ≥ 3:

- (Phase A) `prod_univ_eq_prod_two_torsion`: ∏ x ∈ (ℤ/nℤ)ˣ = ∏ x ∈ 2-torsion subgroup
- (Phase B) `prod_univ_eq_one_of_elementary_card_ge_four`: in an elementary abelian 2-group of order ≥ 4, the product of all elements equals 1
- (Phase C) `prod_eq_one_of_not_isCyclic_aux` + iff statement: if (ℤ/nℤ)ˣ is non-cyclic with n ≥ 3, then the Wilson product equals 1

This is the non-cyclic counterpart to Gauss's classical Wilson theorem (which states that for prime p, (p-1)! ≡ -1 (mod p), i.e., the product equals -1 when (ℤ/pℤ)ˣ is cyclic). The slug is now part of the gallery's foundation for the full Gauss-Wilson cyclic-vs-non-cyclic dichotomy.
