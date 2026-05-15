# Session 2026-05-14 — S7-prep ACT (Part 8: B-side bias + biased-vertex Finsets)

**Mode**: FRESH (continuation of Iter 10 / PR #18959 S6c-ACT — Option A symmetric surrogate)
**Researcher**: researcher-9
**Iteration**: 11
**Outcome**: progress — 19 sorry-free declarations added at `Proofs/SzemerediCoreOQ04.lean:866-1054` (Part 8). Sorry count unchanged at 2 (Iter 10 baseline). Build verified via Docker wrapper (7744 jobs, 0 errors).

## What I Did

1. Confirmed Iter 10 / PR #18959 (S6c-ACT) had landed on `origin/main` with build verified (per merged PR title).
2. Diagnosed the S7 next-action options from Iter 10 state.md:
   - **S7 ACT (main)**: 200-300 LOC, 2-3 sessions — too big for one session.
   - **S7 ACT-alt** (Target C, `findRegularPartition`): 100-150 LOC, 1 session, but orthogonal to the Iter 10 sorry and touches an independent area (`SzemerediRegularity.lean:436` integration).
   - **S7 PREP** (doc-only `problem.md` update): ~30 LOC, but counts against memory-noted 2-per-session STATE-SYNC cap.
3. Decomposed S7 ACT (main) into its natural sub-steps:
   - (a) Define the bad/good biased-vertex Finsets + dual B-side bias (combinatorial primitives).
   - (b) Prove `|A_bad| ≤ eps · |A|` via Markov on `IsWitnessRegular` (substantive `Finset.sum` averaging).
   - (c) Triangle-inequality final assembly.
4. Picked sub-step (a) as the deliverable for this session — sorry-free, single-session, no `Finset.sum` calculus.
5. Wrote Part 8 of `Proofs/SzemerediCoreOQ04.lean` (+189 LOC, 19 sorry-free declarations).
6. Caught the main-repo-absolute-path Edit trap (memory: `feedback_mechanic_edit_absolute_main_repo_path_silent_drift`) — first Edit attempt landed in main repo (mtime jumped to `May 14 04:59`, line count went to 1054 there but worktree stayed at 865); recovered via `git -C /Users/.../lean-genius checkout HEAD --` and re-applied at worktree-rooted absolute path.
7. Docker-build verified from worktree CWD (memory: `feedback_researcher_docker_build_cwd_must_be_worktree`) → 7744 jobs, 0 errors, 2 sorries (= Iter 10 baseline).
8. Updated `state.md` (Iter 11 entry) and JSON (`phase`, `currentState.{phase,since,iteration,focus,nextAction,attemptCounts}`, `knowledge.{insights,builtItems,nextSteps,progressSummary}`, top-level `lastUpdate`).
9. Wrote this session log.

## Key Findings

- **Filter-with-negated-predicate idiom**: defining `A_good` as `A.filter (fun a => ¬ (eps < vertexBias G a A B))` (syntactic negation) lets `Finset.filter_card_add_filter_neg_card_eq_card` fire directly — no extra lemma needed for the cardinality partition. The good-set membership is then re-exposed in the natural `≤` form via `not_lt.mp` / `not_lt.mpr` (one-line `refine ⟨..., ...⟩`).
- **Trivial-regime collapse template generalizes cleanly**: same `Finset.filter_eq_empty_iff.mpr` / `Finset.filter_eq_self.mpr` + `linarith` pattern used by Part 5 `*_of_one_le_eps` lemmas extends to both `A_bad`/`A_good` and `B_bad`/`B_good`. Four lemmas, identical structure.
- **Dual B-side bias mirrors Part 6 exactly**: the only difference from `vertexBias` (A-side, `|d({a}, B) - d(A, B)|`) is which `abs_edgeDensity_sub_le_one*` lemma applies — `abs_edgeDensity_sub_le_one` (no suffix, varies right arg) for the B-side dual, vs `abs_edgeDensity_sub_le_one_left` (varies left arg) for the A-side. Both are in Part 5 (lines 448-478).
- **Scope discipline**: Part 8 is **prerequisite scaffold**, not the Markov bound itself. The hard `Finset.sum` averaging argument that gives `|A_bad| ≤ eps · |A|` is **deferred to S7 ACT next session**. This keeps the deferred sorry tightly scoped at one location (line 831) and lets Aristotle (or a future researcher) target the Markov bound without having to also reproduce the Finset definitions.

## Files Modified

- `proofs/Proofs/SzemerediCoreOQ04.lean` — +189 lines (Part 8 at lines 866-1054).
- `src/data/research/problems/szemeredi-core-oq-04.json` — iter 10 → 11; refreshed `phase`, `currentState.*`, `knowledge.*`, `lastUpdate`.
- `research/problems/szemeredi-core-oq-04/state.md` — added Iter 11 entry at top.
- `research/problems/szemeredi-core-oq-04/sessions/2026-05-14-s7-prep-part8-biased-vertex-finsets.md` — this file.

## Build

`./proofs/scripts/docker-build.sh Proofs.SzemerediCoreOQ04` (from worktree CWD) → `Build completed successfully (7744 jobs)`. Only linter warnings about unused `[Fintype V]` / `[DecidableEq V]` section variables on the new Part 8 lemmas — pre-existing pattern in the file (also present on Part 6 / Part 7 lemmas merged in Iter 10), not blocking. Log: `.loom/logs/researcher-9-szemeredi-s7-build1.log`.

## Net Delta

| Metric | Iter 10 | Iter 11 | Δ |
|---|---|---|---|
| `sorry` count | 2 | 2 | 0 |
| `axiom` declarations | 0 | 0 | 0 |
| File line count | 865 | 1054 | +189 |
| Sorry-free declarations (Part 8) | — | 19 | +19 |
| Markov-step Finset primitives in place | A-side `vertexBias` only | both sides + 4 Finsets + partition lemmas | ✓ |

## Next Steps

1. **S7 ACT (substantive)**: prove `A_bad_card_le_eps_card` via Markov on per-vertex bias averaged over `witnessFamilyB`. ~40-60 LOC.
2. **S7 ACT (dual)**: prove `B_bad_card_le_eps_card` from `Dual_IsWitnessRegular`. Mirrors above, ~40-60 LOC.
3. **S7 ACT (assemble)**: close `witness_regular_symmetric_implies_epsilon_regular_small_eps` via triangle inequality. ~50-80 LOC.
4. **S7 ACT-alt (still independent)**: build `findRegularPartition` (Target C) using merged `witnessOfIrregular` (#17919). ~100-150 LOC.
