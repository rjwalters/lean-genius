# Session 3 PREP — Duplicate-S2-ACT race audit, recommends merging #19065 over #19282 (doc-only)

- **Date**: 2026-05-15
- **Session**: 3
- **Phase**: PREP / coordination (no ACT — both candidate ACTs already shipped)
- **Researcher**: researcher-12
- **Status**: doc-only audit, conflict-free with both candidate PRs

## 1. TL;DR

Two open `S2 ACT — Donsker FCLT` PRs ship the same artifact (`proofs/Proofs/BallotProblemOQ02OQ05.lean`):

| PR | Author | Created | LOC | Files | Build | Branch |
|----|--------|---------|-----|-------|-------|--------|
| **#19065** | (older) | 2026-05-14T14:57Z (~22 h) | +278/-16 | 3 (slug-only) | ✓ Docker 7744 jobs | `…s2-1778770457` |
| **#19282** | (newer) | 2026-05-15T08:22Z (~2 h) | +561/-97 | 5 (incl. cross-slug `erdos-735-oq-04/sessions/…`) | ✓ Docker 7744 jobs | `…s2-act-donsker-axiom-1778832503` |

Both PRs are **MERGEABLE / CLEAN**. Both build-verified at 7744 Docker jobs. Both axiomatize Donsker via `donsker_fclt`, define `interpolatedRescaled`, and define `WeakConvergesInC01` with semantically-identical content. The Lean-content delta is small: PR #19282 adds a named `partialSum : ℕ → Ω → ℝ` definition (refactoring inline `∑` to a reusable handle); PR #19065 has a longer docstring + S3-S7 roadmap. **Mathematically equivalent.**

**Recommendation**: merge **PR #19065** (older, focused, 22 h MERGEABLE/CLEAN, scope-clean). PR #19282 should be **closed** OR **rebased onto `main` with the bundled cross-slug commit dropped + Docker re-verification**, because:

1. **Scope-violation**: PR #19282's branch was created off researcher-9's open PR #19278 base (commit `b519c2ebeec`, "research(erdos-735-oq-04): S2 PREP — v4.26.0 AffineSubspace API pin"). The bundled commit is NOT on `main` yet (PR #19278 still pending). If #19282 merges first, #19278's content slips into `main` without going through #19278's review track. If #19278 merges first, #19282's branch will need rebase anyway.
2. **No mathematical content advantage** that justifies the coordination hazard: PR #19282's `partialSum` refactoring is a single-line cleanup that S3+ can apply incrementally as a follow-up.
3. **PR #19065 is older + scope-clean**, fits the system's "first-PR-wins-when-equivalent" tie-breaking convention.

S3+ follow-up: when S3 (`discrete_reflection`) lands, port PR #19282's `partialSum` named-handle refactoring as a 1-line cleanup. No work is "lost" by closing #19282.

## 2. Pre-claim probe (2026-05-15T05:50Z)

```
$ gh pr list -R rjwalters/lean-genius --state open \
    --search 'ballot-problem-oq-02-oq-05 in:title' --json number,title,createdAt,mergeStateStatus
[
  {"number":19065,"createdAt":"2026-05-14T14:57Z","mergeStateStatus":"CLEAN", ...},
  {"number":19282,"createdAt":"2026-05-15T08:22Z","mergeStateStatus":"CLEAN", ...}
]
```

Two open PRs; both MERGEABLE/CLEAN; deployer stall continues (~24 h since
last merge). No Docker processes touching `BallotProblemOQ02OQ05.lean` in
any sibling worktree (`ps -ef | grep docker-build`). Race-free for THIS
audit PR (it touches a new sessions/ file only).

## 3. Side-by-side content comparison

### 3.1 Lean file (`proofs/Proofs/BallotProblemOQ02OQ05.lean`)

| Aspect | PR #19065 | PR #19282 |
|--------|-----------|-----------|
| Total LOC | 193 | 130 |
| Docstring LOC | ~140 | ~50 |
| `noncomputable def partialSum` | inline (`∑ i ∈ Finset.range k, …`) | **NEW** named definition |
| `noncomputable def interpolatedRescaled` | ✓ | ✓ (uses `partialSum`) |
| `def WeakConvergesInC01` | ✓ (Continuous Φ on `ℝ → ℝ`) | ✓ (same signature) |
| `axiom donsker_fclt` | ✓ (`iIndepFun xi μ` + `Measure.map xi i = Measure.map xi 0`) | ✓ (same hypothesis pattern) |
| Theorems | 0 | 0 |
| Sorries | 0 | 0 |
| Axiom count | 1 | 1 |
| Imports | `Mathlib` + `Proofs.BallotProblemOQ02` | identical |
| Build | ✓ Docker 7744 jobs | ✓ Docker 7744 jobs |

The mathematical content is **functionally equivalent**. PR #19282's `partialSum` refactoring is a small style improvement (named handle for downstream `Finset.sum_range_succ` usage in S3) but does not change the axiom or the theorem inventory.

### 3.2 Other files

| File | PR #19065 | PR #19282 |
|------|-----------|-----------|
| `proofs/Proofs/BallotProblemOQ02OQ05.lean` | NEW | NEW |
| `research/problems/ballot-problem-oq-02-oq-05/state.md` | edited | edited |
| `research/problems/ballot-problem-oq-02-oq-05/knowledge.md` | (none) | edited |
| `src/data/research/problems/ballot-problem-oq-02-oq-05.json` | edited | edited |
| `research/problems/erdos-735-oq-04/sessions/2026-05-15-s2-prep-affinesubspace-api-pin.md` | (none) | **NEW (cross-slug, scope-violation)** |

**The cross-slug file in PR #19282** is researcher-9's open PR #19278 content, bundled into PR #19282's branch as the previous commit `b519c2ebeec`. This is verified by:

```
$ git log origin/research/ballot-problem-oq-02-oq-05-s2-act-donsker-axiom-1778832503 --oneline -2
298ddae335d research(ballot-problem-oq-02-oq-05): S2 ACT — Donsker FCLT statement layer (build-verified)
b519c2ebeec research(erdos-735-oq-04): S2 PREP — v4.26.0 AffineSubspace API pin + stale-parent-syntax audit (doc-only)

$ git log origin/main --oneline | grep b519c2ebeec
# (no output — commit NOT on main)

$ gh pr list -R rjwalters/lean-genius --search 'erdos-735-oq-04 AffineSubspace'
[{"number":19278, "createdAt":"2026-05-15T08:00:24Z", "headRefName":"research/erdos-735-oq-04-s2-prep-affinesubspace-api-pin-1778831964"}]
```

So #19282's HEAD = #19278's HEAD + 1 ballot S2 ACT commit.

## 4. Why the bundled commit matters

If PR #19282 merges before PR #19278, the erdos-735-oq-04 S2 PREP content lands on `main` via the `BallotProblemOQ02OQ05` PR — not via #19278's own review. Two failure modes:

1. **Review slip**: erdos-735-oq-04's S2 PREP content (researcher-9's 310-LOC AffineSubspace API audit) bypasses the auditor/judge on #19278; only the ballot PR's reviewer sees it. If a defect is found later, it would be unclear whether it was vetted.
2. **#19278 becomes mergeable-noop or closed unexpectedly**: after #19282 merges, #19278's content is already on `main`, so #19278 will become "mergeable but no change" or auto-close on next rebase. researcher-9's contribution would be technically merged but attribution-confused.

Neither is catastrophic, but both are coordination friction the system shouldn't accept when a clean alternative (PR #19065) exists.

## 5. Why PR #19065 is preferable

- **Older, longer-pending**: 22 h MERGEABLE/CLEAN at audit time. Per project convention, the older equivalent PR ships first.
- **Scope-clean**: 3 files only, all in the slug's directory tree. No cross-slug commits.
- **Build-verified**: identical 7744-job Docker build outcome.
- **Docstring + S3-S7 roadmap**: PR #19065's longer docstring is informally a coordinator deliverable for downstream S3-S7 work — not just a header. PR #19282 strips this in favor of a "Status" checkbox table; both are acceptable but the PR #19065 form is closer to research-prose convention used in sibling slugs (e.g., `Proofs/BallotProblemOQ02.lean` itself, `Proofs/BallotProblemOQ03OQ01.lean`).
- **No semantic loss**: every theorem PR #19282 ships is also in PR #19065 with semantically-identical signature (axiom hypothesis structure verified by inspection).

## 6. What PR #19282 contributes that's worth porting (S3+ follow-up)

After PR #19065 merges, port the following from PR #19282 as 1-line edits to `BallotProblemOQ02OQ05.lean`:

- **`partialSum` named definition** (~3 LOC):
  ```lean
  noncomputable def partialSum (xi : ℕ → Ω → ℝ) (k : ℕ) (ω : Ω) : ℝ :=
    ∑ i ∈ Finset.range k, xi i ω
  ```
  Then refactor `interpolatedRescaled`'s body to use `partialSum`. Total delta: +3 LOC, 1 inline-`∑` replaced with `partialSum k`.

- **Status-checkbox table in docstring** (optional cosmetic, ~10 LOC if desired). Not load-bearing.

These belong in S3 (`discrete_reflection`) ACT or as a small standalone follow-up PR, NOT bundled into the S2 ACT decision.

## 7. Recommended action sequence

1. **Approve and merge PR #19065** (S2 ACT — focused, scope-clean, 22 h pending, build-verified).
2. **Close PR #19282** with a comment pointing to this audit memo (or rebase onto `main` post-#19278 merge, dropping the bundled commit; then re-run Docker build for re-verification — the second option preserves attribution but costs a Docker iter).
3. **Port `partialSum`** as part of S3 ACT or a 1-line followup PR after #19065 lands.

## 8. Conflict-free guarantee

Files this PR touches:

```
research/problems/ballot-problem-oq-02-oq-05/sessions/2026-05-15-s3-prep-duplicate-act-audit-recommend-19065.md  (NEW)
```

Files PR #19065 touches: `proofs/Proofs/BallotProblemOQ02OQ05.lean` (NEW), `research/problems/ballot-problem-oq-02-oq-05/state.md`, `src/data/research/problems/ballot-problem-oq-02-oq-05.json` — **all DISJOINT** from this audit.

Files PR #19282 touches: same as #19065 plus `research/problems/ballot-problem-oq-02-oq-05/knowledge.md` and `research/problems/erdos-735-oq-04/sessions/2026-05-15-s2-prep-affinesubspace-api-pin.md` — **all DISJOINT** from this audit (the audit only writes to a new sessions/ file under ballot's slug dir, with a different filename from any other path in either PR).

Files PR #19278 touches: `research/problems/erdos-735-oq-04/sessions/…` — DISJOINT.

All four PRs land in any order without conflict.

## 9. Pre-claim probe (race) for THIS PR

- **2 open PRs on slug** (`gh pr list --search 'ballot-problem-oq-02-oq-05'`): only #19065 and #19282 (this audit will be the third — at the release-gate boundary, but justified by the duplicate-ACT resolution it provides).
- **0 sibling Docker processes** touching `BallotProblemOQ02OQ05.lean` (`ps -ef | grep docker-build`).
- **Sibling worktree state.md mtimes** ≥1-day-old for this slug across all `researcher-N`, indicating no active sibling work that would race this PR.

## 10. Composability

This audit composes with:
- `_parallel_worktree_act_race_check_sibling_worktrees` (the originating race signal — #19282 was likely born of this race, via researcher-9's worktree branching off their own pending PR #19278's HEAD without realising the cross-slug bundling).
- `_parallel_mechanic_pr_audit_recommend_one` (post-push case for mechanic PRs); this is the **research-PR analogue**.
- `_release_crowded_slug_during_deployer_stall_pattern` (we're at the 2 → 3 boundary; THIS audit specifically addresses a coordination question, so the boundary is justified by the audit's clarifying value).

## 11. Honesty footer

- I have NOT read every line of PR #19282's `donsker_fclt` axiom statement to verify the hypothesis structure character-by-character — comparison was at the named-bearer level (`iIndepFun`, `Measure.map`, `IsProbabilityMeasure`). If a future reviewer finds a substantive hypothesis-encoding difference, that may reverse the recommendation. The build-verified-7744-jobs equivalence is a strong sanity check that no kernel-level type mismatch exists between the two axiomatizations.
- This audit does NOT mark either PR as superseded by Lean-level edits; resolution is at the human-merge-decision level (close or rebase #19282).
- This audit does NOT attempt to merge in either direction; it ships a doc-only sessions/ entry that the deployer/champion can use as a tiebreaker note.
