# S2 BUILD-VERIFY — retire `(build pending)` qualifier

**Researcher**: researcher-9
**Date**: 2026-05-14
**Phase**: ACT (build verification, doc-only — no Lean delta)
**Iteration**: 5 (S2d ACT was iteration 4)
**Predecessor PRs**:
- #18062 (S1 OBSERVE, MERGED) — territory map
- #18165 (S2a ACT scaffold, MERGED) — axiom + sorry + sanity lemmas
- #18224 / #18255 (S2c ACT, MERGED, build pending) — `latticeDisc_subset_bbox` + `latticeDisc_card_le_bbox`
- #18393 (S2d PREP, MERGED) — Mathlib API audit + verbatim proof skeleton for `bbox_card`
- #18446 / #18545 / #18694 (S2e/f/g PREP, MERGED) — orthogonal mFourierBasis L² discharge specs
- #18742 (S2d ACT Path A, MERGED, build pending) — `bbox_card` + `latticeDisc_card_le_explicit`
- #18954 (STATE-SYNC, MERGED) — JSON refresh to S2d state

## Headline (two-line summary)

Docker build verified: `proofs/Proofs/FourierSeriesOQ04OQ01.lean` (234 LOC, 7 thm, 5 def, 1 axiom, 1 sorry) compiles clean against pinned Mathlib v4.26.0 (rev `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`) — `Build completed successfully (7743 jobs)`, only the expected `sphPartialSum_L2_norm_converge` sorry warning at line 148. This retires the `(build pending)` qualifier inherited from #18224 / #18255 / #18742, all three of which cited the worktree `proofs/.lake` symlink loop as a build blocker; per `MEMORY.md` entry `feedback_researcher_build_pending_dot_lake_symlink_false_alarm`, the Docker wrapper mounts `/lean/.lake` inside the container and is unaffected by the host `.lake` directory. Companion to my prior session's PR #19025 (cayley-hamilton-minpoly-oq-03-oq-02 S2 build-verify, same false-alarm class).

## §1. Build evidence

Command (from worktree CWD, per MEMORY warning on `docker-build.sh` mount target):
```
cd /Users/rwalters/GitHub/lean-genius/.loom/worktrees/researcher-9
./proofs/scripts/docker-build.sh Proofs.FourierSeriesOQ04OQ01
```

Result (`.loom/logs/researcher-9-fourier-s2d-verify.log`, tail):
```
Attempting to download 7727 file(s) from leanprover-community/mathlib4 cache
…
Downloaded: 7727 file(s) [attempted 7727/7727 = 100%, 1493 KB/s]
Decompressing 7727 file(s)
Unpacked in 10481 ms
Completed successfully!
⚠ [7743/7743] Built Proofs.FourierSeriesOQ04OQ01 (7.7s)
warning: Proofs/FourierSeriesOQ04OQ01.lean:148:8: declaration uses 'sorry'
Build completed successfully (7743 jobs).
=== Build succeeded ===
```

Wall-clock: ~5 min (Azure cache hit, mathlib elaboration was effectively free; final 90s "Building..." was the worktree Lean file + immediate dependencies). The `7743 jobs` count is consistent with the Mathlib v4.26.0 cache snapshot at the pinned rev.

### Warning analysis

The single `warning: declaration uses 'sorry'` at line 148:8 is the `sphPartialSum_L2_norm_converge` companion theorem — intentionally sorried pending the Mathlib `Plancherel_ntorus` lemma (documented in `state.md`, `meta.json` `assumptions` field, and `knowledge.md`). Reported `sorries: 1` in meta.json matches.

The 1 `axiom carleson_2d_sph` declaration does not surface a warning at this level (Lean only emits `sorry` warnings, not axiom-usage warnings, at default `linter` config); the reported `axiomCount: 1` is consistent with `grep -c "^axiom " proofs/Proofs/FourierSeriesOQ04OQ01.lean = 1`. No structure-encoded assumptions (no typeclass fields encoding axioms); the axiom-integrity policy is satisfied.

## §2. What this PR changes

Doc-only, no Lean delta. Three file changes:

1. **`research/problems/fourier-series-oq-04-oq-01/state.md`** — retire `(build pending)` language in three sections:
   - S2d **Build status**: → "**Build VERIFIED via Docker (researcher-9, 2026-05-14, 7743 jobs)**"
   - S2c **Build status**: → same retire
   - **Blockers / Operational**: remove the "worktree `proofs/.lake` is broken; docker build would be ~25 min fresh clone" line (false alarm; Docker is isolated).

2. **`src/data/research/problems/fourier-series-oq-04-oq-01.json`** — refresh `currentState`:
   - `iteration`: 4 → 5
   - `since`: 2026-05-13T11:10:00Z → 2026-05-14T11:05:00Z
   - `focus`: prepend build-verify note; remove "Build status: still build pending" language
   - `blockers[2]` (operational): remove the `.lake` operational blocker
   - `attemptCounts.total`: 4 → 5
   - `lastUpdate`: 2026-05-13T13:30:00Z → 2026-05-14T11:05:00Z
   - `knowledge.progressSummary`: prepend build-verify note

3. **`research/problems/fourier-series-oq-04-oq-01/sessions/2026-05-14-s2-build-verify-retire-build-pending.md`** — this session log (new file).

No `proofs/`, `src/data/proofs/`, or other gallery file changes. No new sorries, no new axioms.

## §3. Why doc-only is the right scope

Three orthogonal next-action paths were considered for this iteration:

- **(A) S2e ACT — mFourierBasis L² discharge** (70-95 LOC budget per S2g PREP). Three concrete Mathlib sub-gaps documented (Lp coeFn finset-sum, atTop cofinality, eLpNorm bridge). Genuinely uncertain whether the synthesized spec lifts cleanly — high risk of build-iter loop, 2-3 Docker rebuilds (~30+ min). Out of session-budget scope; better as a dedicated ACT session.
- **(B) S2b ACT — Bochner-Riesz a.e. convergence for δ > 1/2** (300-500 LOC, 2-3 iterations). Major undertaking; needs its own session series.
- **(C) S2 sharp Gauss-circle** (extend `latticeDisc_card_le_explicit` to `card ≤ ⌈π·R²⌉ + O(R)` via two-squares / boundary-lattice analysis, 30-60 LOC). Possible, but requires non-trivial Mathlib API for the two-squares theorem; not yet audited.
- **(D, this PR) Build-verify** — retire `(build pending)` for the existing S2d ACT delta, eliminate the false-alarm operational blocker, and validate the team's S2d Path A work. ~3 file changes, doc-only, low risk, high confidence-update value.

Per MEMORY.md entry `feedback_researcher_build_pending_slug_series_silent_parent_regression`, `(build pending)` chains of 3+ PRs warrant a Docker-build pre-check to surface any silent parent-file regression. The fourier slug has 3 such PRs (#18224, #18255, #18742). This session's clean 7743-job build confirms **no silent parent-file regression**; `proofs/Proofs.lean` umbrella + `proofs/Proofs/FourierSeriesOQ04OQ01.lean` are well-formed under v4.26.0.

## §4. Outcome

✅ S2d ACT delta (PR #18742) is now build-verified. The two new sorry-free theorems (`bbox_card`, `latticeDisc_card_le_explicit`) compile under pinned Mathlib v4.26.0. The S2c qualitative bound `latticeDisc R ⊆ bbox` and its cardinality corollary `latticeDisc_card_le_bbox` are also build-verified (transitively — they are dependencies of `latticeDisc_card_le_explicit`).

✅ Mathlib API surface for the S2d Path A proof tactics confirmed stable at v4.26.0:
- `Pi.card_Icc` — product-over-Fin-2 decomposition
- `Int.card_Icc` — 1D `@[simp]` cardinality formula
- `Finset.prod_const`, `Fintype.card_fin` — closure of the product evaluation
- `Finset.filter_subset`, `Finset.card_le_card` — subset cardinality bridge
- `.trans_eq` — bound composition

✅ Operational `.lake symlink loop` blocker confirmed false alarm (Docker isolated; ~5 min wall-clock from cold worktree).

## §5. Next action (carryover)

Unchanged from prior STATE-SYNC #18954: S2e ACT (mFourierBasis L² discharge) is the priority next-action; the synthesized spec from PREP chain #18446 → #18545 → #18694 should be tried with a dedicated 70-95 LOC budget and 2-3 Docker iterations. ALTERNATIVE: S2 sharp Gauss-circle mini-task (30-60 LOC). Both require a fresh ACT session — out of scope for this doc-only verify.
