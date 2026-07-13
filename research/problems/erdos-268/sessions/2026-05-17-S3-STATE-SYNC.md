# Session S3 STATE-SYNC — 2026-05-17

**Researcher**: researcher-10
**Slug**: erdos-268
**Tier**: B (significance: 7, tractability: 6, knowledge: 40 RICH, MODERATE+
depth-first slot 435 of 1260 available)
**Predecessor**: state.md mass-imported via PR #19454 (sperner-ndim-mathlib-oq-01-oq-04
S2-A ACT, 2026-05-16, T-1d). Last substantive research PR: aaafddfae68
(#11983, 2026-04-23, T-24d). Registry graduated 2026-04-25T12:53:24Z (T-22d).

## §0 — Why this STATE-SYNC

`claim-problem.sh claim-random` selected `erdos-268` from a candidate pool
that still lists `status: in-progress`, yet:
- `research/registry.json`: `phase: COMPLETED, status: graduated,
  completed: 2026-04-25T12:53:24Z`.
- `src/data/research/problems/erdos-268.json`: top-level `phase: COMPLETED,
  status: completed`, but `currentState.phase: OBSERVE, iteration: 2,
  since: 2026-04-21`.
- `research/problems/erdos-268/state.md`: iter-2 OBSERVE template with the
  `harmonicPointSet_path_connected` sorry as current focus — yet that sorry
  was axiomatized 2026-04-23 via PR #11983.
- `src/data/proofs/erdos-268/meta.json`: correct
  (`status: axiomatized, badge: axiom, axiomCount: 2, sorries: 0`,
  `lineCount: 979, theoremCount: 34, definitionCount: 17` all match actual
  Lean source).

This is a textbook instance of the systemic 728-slug registry-vs-pool drift
+ research-wave-bypass pattern documented in researcher-10's memory entries
`_systemic_pool_drift_728_slugs` and
`_long_completed_per_registry_slug_with_research_wave_bypass_pool_and_json_drift`.

## §1 — Predecessor chain

The active research arc on erdos-268 ran 2026-04-21 → 2026-04-23 with 7 PRs:

| # | PR | Date | Author | Title |
|---|----|------|--------|-------|
| 1 | #10920 | 2026-04-21 | rjwalters | Erdős #268: prove 7/8 sorries in harmonic subseries formalization |
| 2 | #11210 | 2026-04-22 | rjwalters | Research: erdos-268 — prove d=0 path-connectivity, telescoping infrastructure |
| 3 | #11277 | 2026-04-22 | rjwalters | Research: Erdős #268 — d=0 proved, d=1 convexity framework (3→2 sorries) |
| 4 | #11304 | 2026-04-22 | rjwalters | Research erdos-268: greedy harmonic construction for d=1 |
| 5 | #11460 | 2026-04-22 | rjwalters | Research: Erdős #268 Session 4 — fix greedySet_infinite with consecutiveProducts |
| 6 | #11504 | 2026-04-22 | rjwalters | Research: Erdős #268 Session 5 — fix hAconv via HasSum.add_disjoint (2→1 sorries) |
| 7 | #11983 | 2026-04-23 | rjwalters | Research: Erdős #268 — eliminate sorry via harmonicPointSet_path_connected axiom |

The S7 PR (#11983) axiomatized the last open sorry of `Erdos268Problem.lean`,
landing the file at the current 979 lc / 34 theorems / 2 axioms / 0 sorries
state. The Seeker pool was selected via PR #11071 (2026-04-21).

After 2026-04-23 no further commits touched `Erdos268Problem.lean` content;
only mass batches did (`#14929` JacobiTrudi reformat-only touch 2026-05-04,
`#18059` angle-trisection touch 2026-05-12, `#19454` sperner touch
2026-05-16). The structured numeric meta.json fields were synced by one of
the meta-batches; the research JSON `leanFiles[]` was not.

## §2 — Mass-import audit (sperner PR #19454)

```
$ git log --all --diff-filter=A -- research/problems/erdos-268/state.md
ecb47b35601 2026-05-16  research(sperner-ndim-mathlib-oq-01-oq-04): S2-A ACT — ... (#19454)
```

The state.md "creator" is a Lean ACT for a totally different slug. PR #19454
includes 10+ unrelated slug state.md / problem.md / knowledge.md /
literature/README.md files (erdos-268, erdos-268-incomplete-01,
erdos-268-oq-01, and others). The content is byte-identical to the prior
iter-2 OBSERVE template — sperner PR just re-imported the directory tree
into main. Hence `git log` of `state.md` makes the creator look like sperner
even though the file content has been frozen since 2026-04-21.

This is the same `_S2_SCOPED_orphan_commit_never_PRd_mass_imported_via_unrelated_pr`
trap pattern documented in memory.

## §3 — Drift surfaces inventory

### state.md (re-written wholly in this PR)
- Phase: `OBSERVE` → `COMPLETED`
- Iteration: `2` → `3`
- Active Approach section pruned to "None — slug is COMPLETED"
- Current Focus section replaced with STATE-SYNC summary
- NEW Iteration History table (3 rows)
- Next Action rewritten to post-merge pool flip

### research JSON (surgical)
| Field | Before | After |
|-------|--------|-------|
| top-level `lastUpdate` | — (missing) | `"2026-05-17"` |
| `currentState.phase` | `"OBSERVE"` | `"COMPLETED"` |
| `currentState.iteration` | `2` | `3` |
| `currentState.since` | `"2026-04-21"` | `"2026-05-17"` |
| `currentState.focus` | iter-2 ORIENT-Mathlib prose | S3 STATE-SYNC prose with PR citations |
| `currentState.nextAction` | iter-2 ORIENT-Mathlib search | "COMPLETED. Post-merge pool flip ..." |
| `currentState.attemptCounts.total` | `0` | `8` |
| `currentState.attemptCounts.approachesTried` | `0` | `2` |
| `leanFiles[0].lineCount` | `143` | `142` |
| `leanFiles[1].lineCount` | `952` | `979` |
| `leanFiles[1].theoremCount` | `19` | `34` |
| `leanFiles[1].defCount` | `15` | `17` |
| `leanFiles[2].lineCount` | `213` | `212` |

Note: `leanFiles[*].axiomCount` and `leanFiles[*].sorryCount` were already
correct. `meta.json` was NOT touched (already correct).

### NOT-touched surfaces (deliberately)
- `meta.json`: structured numeric fields all match actual source; prose
  description / originalContributions correctly describe the 2-axiom
  axiomatized state.
- `Erdos268Problem.lean` / `Erdos268Aristotle.lean` /
  `Erdos268ProblemAristotle.lean`: zero Lean edits in this PR (doc-only).
- `annotations.json` / `index.ts`: unchanged.
- `knowledge.md` / `problem.md`: unchanged (research-local detail consistent
  with the current axiomatized state; both reference the d=0/d=1 cases as
  PROVED).
- `knowledge.builtItems` / `insights` / `nextSteps`: unchanged — they
  faithfully record the 7-PR research arc's outputs.

## §4 — Numerical verification

```
$ wc -l proofs/Proofs/Erdos268{Aristotle,Problem,ProblemAristotle}.lean
     142 proofs/Proofs/Erdos268Aristotle.lean
     979 proofs/Proofs/Erdos268Problem.lean
     212 proofs/Proofs/Erdos268ProblemAristotle.lean

$ grep -cE "^(protected |private |noncomputable )*(theorem|lemma) " proofs/Proofs/Erdos268*.lean
proofs/Proofs/Erdos268Aristotle.lean:9
proofs/Proofs/Erdos268Problem.lean:34
proofs/Proofs/Erdos268ProblemAristotle.lean:10

$ grep -cE "^(protected |private |noncomputable )*def " proofs/Proofs/Erdos268*.lean
proofs/Proofs/Erdos268Aristotle.lean:4
proofs/Proofs/Erdos268Problem.lean:17
proofs/Proofs/Erdos268ProblemAristotle.lean:8

$ grep -cE "^axiom " proofs/Proofs/Erdos268*.lean
proofs/Proofs/Erdos268Aristotle.lean:0
proofs/Proofs/Erdos268Problem.lean:2
proofs/Proofs/Erdos268ProblemAristotle.lean:0

$ grep -cE "\bsorry\b" proofs/Proofs/Erdos268*.lean
proofs/Proofs/Erdos268Aristotle.lean:0
proofs/Proofs/Erdos268Problem.lean:0
proofs/Proofs/Erdos268ProblemAristotle.lean:1
```

All values match the post-sync research JSON `leanFiles[]` entries.

## §5 — meta.json sanity (NOT edited, verification only)

`src/data/proofs/erdos-268/meta.json` already reflects the correct state:
- `meta.status: "axiomatized"`, `meta.badge: "axiom"` ✓
- `meta.axiomCount: 2`, `meta.sorries: 0` ✓
- `meta.lineCount: 979`, `meta.theoremCount: 34`, `meta.definitionCount: 17` ✓
- top-level `leanFile.lineCount: 979`, `theoremCount: 34`, `axiomCount: 2`,
  `sorries: 0`, `definitionCount: 17` ✓
- `originalContributions[]` includes
  `harmonicPointSet_one_eq`, `harmonicSubseriesSum_surjective_on_pos`, and
  the contains_open_ball derivation from the d≥1 interior axiom — all
  match grep of the Lean source.
- `conclusion.summary` accurately describes 2 axioms + 0 sorries +
  Kovač-Tao 2024 / Kovač 2024 layering.

Hence no `meta.json` edit is required.

## §6 — INFRA carry-forward (advisory only; doc-only PR is insensitive)

Per the 7-bearer 3-RED INFRA pattern documented across same-window
researcher sessions (G7 disk soft-floor, G8 Docker hung, G9 `.lake` self-loop),
this STATE-SYNC is doc-only and does not depend on local Docker / `.lake`
state. Mathlib pin (`2df2f0150c…`) is unchanged in this PR.

The post-merge pool flip uses `scripts/research/claim-problem.sh` which does
not require Docker.

## §7 — Pool flip plan (post-merge, deliberate)

After PR merges, run from `main`:
```
scripts/research/claim-problem.sh update erdos-268 completed
```

This flips `.lean/state/candidate-pool.json` `erdos-268.status:
"in-progress" → "completed"`. The flip is safe to defer until post-merge
since:
1. The current claim by `researcher-71911` (this session) is the only
   active claim; no race window.
2. The flip is independent of any PR content.

The systemic 728-slug drift remains as a class — only this single slug is
resolved here. See `_systemic_pool_drift_728_slugs` memory for the
batch-script proposal addressing the underlying root cause.

## §8 — Files in this PR

| File | Change | Net |
|------|--------|-----|
| `research/problems/erdos-268/state.md` | Full rewrite | template OBSERVE → COMPLETED, iter 2 → 3, iteration-history table |
| `src/data/research/problems/erdos-268.json` | 4 surgical edits | currentState 6-field + leanFiles 5-field |
| `research/problems/erdos-268/sessions/2026-05-17-S3-STATE-SYNC.md` | NEW | this memo |

Zero `.lean` edits. Zero `meta.json` edits.

## §9 — Comparison to recent same-pattern STATE-SYNCs (this session)

| iter | slug | Predecessor type | meta.json edited? | drift surfaces |
|------|------|------------------|--------------------|----------------|
| 1 (researcher-10 PR #20140) | erdos-1153 | research-wave-bypass + mechanic-batch (T-4d index.ts only) | YES (5 surgical: prose summary / originalContributions ghost / sections endLines) | 7 (3 research-local rewrites + 4 meta.json + pool) |
| 2 (this PR) | erdos-268 | research-wave-bypass + sperner state.md mass-import (T-1d) | NO (meta.json correct) | 5 (state.md rewrite + research JSON 6-field + leanFiles 5-field + sessions memo + pool) |

erdos-268's research JSON is more substantially drifted than erdos-1153's
(line-count diff +27 for Erdos268Problem.lean vs +1/-1 typical), but its
meta.json is fully accurate — opposite to erdos-1153 where structured numerics
were correct but prose drifted.

## §10 — Outcome

PR ships 3 files doc-only. Iteration bumps from 2 (stale, frozen since
2026-04-21) to 3 (this STATE-SYNC). Post-merge pool flip
`in-progress → completed` brings the candidate-pool into agreement with the
registry, removing erdos-268 from the 728-slug drifted-set. Slug remains
COMPLETED + graduated + axiom-badged + 2-axiom + 0-sorry in `Erdos268Problem.lean`.
