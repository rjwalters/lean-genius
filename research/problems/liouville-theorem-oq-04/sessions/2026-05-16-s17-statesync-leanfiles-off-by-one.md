# S17 STATE-SYNC — `leanFiles[0]` off-by-one fix + sessions/ bootstrap

**Slug**: liouville-theorem-oq-04
**Phase**: COMPLETE → COMPLETE (no transition)
**Iteration**: 16 → 17
**Date**: 2026-05-16
**Researcher**: researcher-3
**PR**: this PR (doc-only, 3 files)
**Triggering observation**: `claim-random` lands on a T-8d-completed slug; audit finds a single isolated off-by-one on a shared parent file's `leanFiles[0].lineCount` (529 vs `wc -l` = 528). No drift elsewhere; siblings + gallery already at 528.

---

## §1. Why S17 fires

`claim-random` selected `liouville-theorem-oq-04`. This slug last had a
researcher session on 2026-05-08 (S16, PR #17076 — gallery-metadata
promotion to `verified` / `original` after the S15 bridge discharge in PR
#17053). T-8d since last touch; the slug is content-complete (axiom-free,
sorry-free, 1344-LOC OQ-04 file on `origin/main`).

Audit reveals a single residual numeric drift:

| File | `wc -l` | JSON `leanFiles[i].lineCount` | Action |
|---|---|---|---|
| `LiouvilleTheorem.lean` (parent) | 528 | 529 (`leanFiles[0]`) | **fix → 528** |
| `LiouvilleTheoremOQ04.lean` (slug-specific) | 1344 | 1344 (`leanFiles[1]`) | unchanged |

All other JSON counts match: parent file at 17 thm / 1 axiom / 0 def / 0
sorry; OQ-04 file at 35 thm / 0 axiom / 6 def / 0 sorry. The 35-theorem
count includes 2 `private` declarations (35 = 33 public + 2 private:
`natAbs_finset_sum_le` and `padicNorm_intCast_pow_le_one`, both in Part
IV.9). Four matches of the string `sorry` in `LiouvilleTheoremOQ04.lean`
are all in comments (historical "(was sorry)" annotations and the literal
S15 commit message reference), not `by sorry` proofs.

## §2. Cross-slug evidence the parent is at 528

```
liouville-theorem-oq-01.json | leanFiles[*].LiouvilleTheorem.lean.lineCount: 528
liouville-theorem-oq-02.json | leanFiles[*].LiouvilleTheorem.lean.lineCount: 528
liouville-theorem-oq-03.json | leanFiles[*].LiouvilleTheorem.lean.lineCount: 528
liouville-theorem-oq-04.json | leanFiles[*].LiouvilleTheorem.lean.lineCount: 529  ← outlier
gallery liouville-theorem/meta.json | proofRepoPath: Proofs/LiouvilleTheorem.lean, lineCount: 528
```

All three sibling research JSONs (`oq-01/02/03`) and the gallery
`liouville-theorem` meta.json already use `wc -l` = 528. Only `oq-04`
carries the inflated 529 value. This is **not** a mechanic-batch
candidate — there is no fleet of N siblings with the same drift to sync
in bulk; the fix is a single-line edit in a single JSON.

## §3. Root cause: split('\n').length vs wc -l

The `liouville-theorem-oq-04.json` file was (re)introduced into the
research-problems bootstrap on 2026-05-15 (commit `ecb47b3`,
`research(sperner-ndim-mathlib-oq-01-oq-04): S2-A ACT`, which bundled
many research JSONs alongside the sperner Lean work). At that bootstrap
moment, `leanFiles[0].lineCount` was set to 529 for `LiouvilleTheorem.lean`.

This is consistent with the `split('\n').length` convention (= `wc -l + 1`
for files ending in a trailing newline). Per memory pattern: "Mechanic —
`pnpm build` regenerates ALL research JSONs via research:enrich (~1047
files), uses `split('\n').length` convention (= `wc -l + 1`) not raw `wc -l`,
and leaks untracked JSON files for new slugs". The gallery side and recent
mechanic batch syncs have converged on the raw `wc -l` convention as the
canonical value, so the OQ-04 entry is the outlier that needs alignment.

## §4. Why ship S17 vs. release-without-PR?

The release-without-PR memory pattern fires when:

- actively-worked (not COMPLETED), ≤6h since predecessor STATE-SYNC,
  next nextAction will rewrite drifted fields naturally, drift is purely
  LOC off-by-one prose + leanFiles:null, no gallery slug.

This slug:

- ❌ NOT actively-worked: COMPLETE phase, no successor work planned (the
  S16 "Session 17 (optional / future work)" lists 3 follow-up OQs that
  are explicitly *not urgent*).
- ❌ NOT ≤6h since predecessor: T-8d since S16.
- ❌ NO planned next iteration that would rewrite `leanFiles[0].lineCount`
  — without an active research arc, the drift persists indefinitely.
- ✅ Drift IS isolated: single off-by-one on shared parent file's
  `leanFiles[0].lineCount` (one line in JSON).
- ✅ Sessions/ dir does not exist — bootstrap concern.

Sibling precedents shipping STATE-SYNC for nearly identical patterns:

- `research(twin-primes-special-oq-01)` S2 STATE-SYNC (PR #19827, T-1h
  before this S17) — catchup + sessions/ bootstrap + `leanFiles[0]`
  151 → 150 (also single off-by-one).
- `research(shannon-channel-coding-oq-02-oq-03)` S2 STATE-SYNC
  (PR #19819, T-2h) — post-mechanic-batch-sync drift + sessions/
  bootstrap + `leanFiles[4]` 163 → 162.

Tiebreaker per memory: "would 24h-future-researcher find SAME drift
(= ship) or would next planned iter have rewritten it (= release)?"
Without an active arc, no next iter rewrites this. Ship.

## §5. Bearer stability declaration

The OQ-04 file (`LiouvilleTheoremOQ04.lean`) is byte-stable since the
S16 promotion PR #17076 merged on 2026-05-08T11:27:03Z. Mathlib SHA
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0) unchanged since the
S15 era. The parent `LiouvilleTheorem.lean` was last touched as part of
broader Liouville work prior to S15; gallery and 3 sibling JSONs all
report the same parent-file numbers (528/17/1/0/0). No bearer recheck
performed in this S17 cycle — SHA-stable busywork per memory pattern.

The chain on `origin/main`:

```
padic_liouville_norm_bridge (theorem, no axiom)
   ↓ via min-witness C' := min(1/(L·M), δ) and ℚ-decidable case split
padic_liouville_estimate (proved via factorization + bridge)
   ↓
padic_algebraic_not_liouville (proved, 0 sorries)
```

remains intact.

## §6. Files this S17 doc-only PR (3)

1. **EDIT** `src/data/research/problems/liouville-theorem-oq-04.json` (5
   logical edits):
   - `currentState.since`: 2026-05-08T12:00Z → 2026-05-16T21:38Z
   - `currentState.iteration`: 16 → 17
   - `currentState.focus`: rewritten to S17 STATE-SYNC summary
   - `currentState.nextAction`: re-labelled S17 → S18; semantically unchanged
     (still the 3 follow-up OQ candidates)
   - `currentState.attemptCounts.total`: 15 → 16
   - `knowledge.progressSummary`: prepended S17 STATE-SYNC summary (S16
     content preserved verbatim after the `—` separator)
   - `knowledge.nextSteps[0]`: prepended a "DONE (S17, this PR)" entry
   - `leanFiles[0].lineCount`: 529 → **528**
   - top-level `lastUpdate`: 2026-05-08T12:00Z → 2026-05-16T21:38Z

2. **EDIT** `research/problems/liouville-theorem-oq-04/state.md` —
   prepend Session 17 entry (Phase line refresh, Since refresh, Iteration
   bump 16 → 17, Last Updated line added). Preserve all S16 → S1 content
   verbatim below under the "Current Focus (historical, S16, preserved
   verbatim)" heading.

3. **NEW** `research/problems/liouville-theorem-oq-04/sessions/2026-05-16-s17-statesync-leanfiles-off-by-one.md`
   (this file, ~180 LOC) — bootstraps the `sessions/` directory. Retains
   the historical flat files (`session-26-asymp-large-n.md` … etc., which
   don't actually exist for this slug; the slug used inline state.md
   entries instead of separate session memos).

## §7. Explicit non-actions

- ❌ No `.lean` file touch (slug is content-complete; no proof work
  needed).
- ❌ No `proofs/Proofs/LiouvilleTheorem.lean` edit (parent file is
  out-of-scope for this slug — it's tracked by the sibling `liouville-theorem`
  gallery + sibling `oq-01/02/03` research JSONs which are already
  correct).
- ❌ No gallery `meta.json` edit. Both `liouville-theorem` (lineCount
  528 ✓) and `liouville-theorem-oq-04` (status verified / axiomCount 0 /
  sorries 0 ✓) are accurate.
- ❌ No `lake-manifest.json` touch.
- ❌ No `problem.md`, `knowledge.md`, `literature/` touch.
- ❌ No bearer re-spot-check (SHA byte-stable since S15 PR #17053 merged
  2026-05-08; ~8d at SHA `2df2f0150c…`).
- ❌ No Docker build attempt. Host disk pressure observed at ~4.5 Gi
  available at claim time (down from ~5.2 Gi 1h earlier per the
  erdos-1151-oq-04 S33 STATE-SYNC memo). Docker daemon `Server:` empty.
  Three RED INFRA blockers (G7 disk 4.5 Gi, G8 Docker hung,
  G9 proofs/.lake circular self-symlink) — none relevant to this
  doc-only PR.
- ❌ No `research:enrich` or `pnpm build` run (would regenerate ALL
  research JSONs and likely re-introduce the 529 via `split('\n').length`
  convention per memory pattern).
- ❌ No sibling fix. The three sibling JSONs `oq-01/02/03` are already
  at 528 — out of scope. If a future mechanic batch sync re-introduces
  the off-by-one, the next researcher who lands on any of the siblings
  can re-fix per the same pattern.

## §8. Honesty calibration

This S17 is a 3-file doc-only patch closing a single 1-line numeric
off-by-one (529 → 528) on a slug that has been content-complete and
inactive for 8 days. The cycle is small (~30 min including audit) and
the PR diff is ~10 substantive JSON lines + the S17 state.md/sessions
prose. There is no mathematical novelty in this iteration; the value
is purely book-keeping consistency: the OQ-04 research JSON now agrees
with its three sibling JSONs and the gallery on the shared parent file's
line count, and the `sessions/` directory is bootstrapped so any future
session memo can land cleanly.

If a mechanic batch-sync system eventually catches such single-slug
off-by-ones automatically, this S17 is harmless — the value reverts to
"researcher established sessions/ dir + put STATE-SYNC on the visible
session-log path" while the mechanic does the numeric work elsewhere.

## §9. PR summary

- **Title**: research(liouville-theorem-oq-04): S17 STATE-SYNC — leanFiles[0] off-by-one fix (529→528) + sessions/ bootstrap (doc-only)
- **Files (3)**: 1 JSON + 1 state.md + 1 NEW sessions/ note
- **Lean changes**: 0
- **Gallery changes**: 0
- **Build verification**: not required (doc-only)
- **Branch**: `research/liouville-theorem-oq-04-s17-statesync-leanfiles-off-by-one`
- **Cycle**: ~30 min (audit + edits, no Docker, no Lean)
