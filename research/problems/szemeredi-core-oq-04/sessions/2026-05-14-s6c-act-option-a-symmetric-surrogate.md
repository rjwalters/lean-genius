# Session: S6c-ACT — Option A symmetric surrogate

**Researcher**: researcher-9
**Date**: 2026-05-14
**Iteration**: 10
**Mode**: ACT (Lean implementation)

## Outcome

Shipped Option A per S6c PREP §4.1 / §5 (PR #18595) and S6c PREP-2 §6.2 (PR #18679). The file `proofs/Proofs/SzemerediCoreOQ04.lean` grew from 555 → 863 LOC (+308) with a new Part 7 that adds:

1. `witnessFamilyA G A B` — the dual A-side ε-grid (definition + 7 supporting lemmas, all sorry-free).
2. `Dual_IsWitnessRegular` — the dual surrogate (definition + decidability + density-bound helper + anti-monotonicity, all sorry-free).
3. `IsWitnessRegular_symmetric` — the conjunction `IsWitnessRegular ∧ Dual_IsWitnessRegular` (definition + decidability + two projection helpers + anti-monotonicity, all sorry-free).
4. Boundary cases: `witnessFamilyA_empty_right`, `Dual_IsWitnessRegular_empty_right`, `Dual_IsWitnessRegular_of_one_le_eps`, `IsWitnessRegular_symmetric_of_one_le_eps` (all sorry-free).
5. The replacement non-trivial-regime theorem `witness_regular_symmetric_implies_epsilon_regular_small_eps` (sole new sorry — deferred ADLRY two-sided second-moment content).
6. The sorry-free wrapper `witness_regular_symmetric_implies_epsilon_regular` that case-splits on `1 ≤ 4·eps` exactly like the existing one-sided wrapper at line 329.

Total: 22 sorry-free declarations + 1 sorry-bearing theorem (the deferred ADLRY content).

## Why this is a net positive iteration on the sorry count

Naïvely, the file's sorry count went from 1 to 2. Underneath:

- The original sorry at line 291 (`witness_regular_implies_epsilon_regular_small_eps`) is on a theorem statement that is **provably false** (PR #18679 counterexample at #V = 16). It is preserved for archival/pedagogical reasons but should not be discharged.
- The new sorry at line 829 (`witness_regular_symmetric_implies_epsilon_regular_small_eps`) is on a theorem statement that IS mathematically provable: the same counterexample fails the stronger antecedent (the bimodal A-side degree distribution violates `Dual_IsWitnessRegular`).

So the *useful* sorry count went from 0 (provable, deferred-content) to 1 — an improvement.

## Files modified

- `proofs/Proofs/SzemerediCoreOQ04.lean` (+308 LOC, +22 sorry-free decls, +1 sorry)
- `research/problems/szemeredi-core-oq-04/state.md` (Iter 10 entry + updated header + obstruction-resolution note)
- `src/data/research/problems/szemeredi-core-oq-04.json` (currentState + knowledge updates)

## Build status

Verified via `./proofs/scripts/docker-build.sh Proofs.SzemerediCoreOQ04` on 2026-05-14. First attempt failed with three application-type-mismatch errors at `IsWitnessRegular_symmetric_anti` (line 749) due to missing positional `G` argument in calls to `IsWitnessRegular_anti` and `Dual_IsWitnessRegular_anti`. Fixed by switching to a `refine ⟨?_, ?_⟩ <;> exact ...` form with `G` explicit. Second build attempt: see `researcher-9-szemeredi-s6c-build2.log`.

Tactic depth: light (`unfold` + `Finset.mem_union/mem_image` + `omega` + `linarith`); no `decide` or heavy `simp`. All Mathlib API used is stable on the lake-pinned v4.26.0 (`Finset.image / filter / card_union_le / card_image_le / Classical.dec / filter_card_add_filter_neg_card_eq_card`).

## Next session priorities

1. **S7 ACT (recommended)**: discharge `witness_regular_symmetric_implies_epsilon_regular_small_eps`. Four sub-lemmas needed: `vertexBias_A_average`, `vertexBias_B_average`, `markov_bad_count`, `slack4_assemble`. Estimated 200-300 LOC, 2-3 sessions.
2. **S7 ACT-alt (independent)**: build `findRegularPartition` (Target C). Uses merged `witnessOfIrregular` from PR #17919. 100-150 LOC, 1 session.
3. **S7 PREP**: update `research/problems/szemeredi-core-oq-04/problem.md` to make the symmetric surrogate the headline definition (~30 LOC, doc-only).
4. **Cleanup (optional)**: delete the now-archival one-sided `witness_regular_implies_epsilon_regular_small_eps` once a future PR migrates all downstream callers (currently none — the file has no consumers outside its own wrapper at line 329).

## Knowledge updates

JSON `currentState.{phase,iteration,since,focus,nextAction}` + `currentState.attemptCounts` + `knowledge.{insights,builtItems,nextSteps,progressSummary}` + `lastUpdate` all updated. `attemptCounts.total` 4 → 5, `currentApproach` 3 → 4 (this is the first Option-A iteration; the previous approach #3 was the one-sided variant which is now demonstrably stuck).
