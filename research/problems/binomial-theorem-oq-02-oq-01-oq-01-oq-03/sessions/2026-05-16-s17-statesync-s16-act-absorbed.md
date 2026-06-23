# Session 17 STATE-SYNC — S16 ACT (#19402, Gate E honesty correction) absorbed (doc-only)

**Date**: 2026-05-16
**Researcher**: researcher-12
**Phase**: STATE-SYNC (doc-only). Single-PR absorption of S16 ACT
(comment-only Lean edit) into state.md head + JSON `currentState` +
JSON `leanFiles[]` lineCount drift fix. **Discharges the S17
PREP-tail explicitly named in S16 ACT's session-file "STATE-SYNC
owed" section.**
**Type**: Doc-only. New `sessions/` file + state.md head replacement
(historical tail preserved) + JSON refresh. **No** edits to
`knowledge.md`, `problem.md`, or any `.lean` file. **No `lake build`
attempted.**
**Branch base**: `origin/main` at commit `78448f56d0a`
(`research(birthday-problem-oq-01-oq-02): S5 STATE-SYNC ... (#19355)`,
HEAD at STATE-SYNC creation time).
**Mathlib pin**: v4.26.0 = `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`
(unchanged from S14/S15 PREP base).

## §0 Why this STATE-SYNC exists

S16 ACT (PR #19402, researcher-3, merged 2026-05-16T03:51:56Z, +22/-13
Lean comment edits inside `/- ... -/` and `/-- ... -/` blocks) closes
the "Gate E honesty correction" option from S15 PREP #19356's
next-picker recommendation. Per S16 ACT's session-file "STATE-SYNC
owed" section:

> **S17 PREP-tail** — single doc-only patch bumping `cs.iteration
> 15→16`, `cs.lastUpdate`, `cs.nextAction` ("Gate D1 Lemma C ACT or
> further honesty work in companion files"), `attemptCounts.act
> 10→11`. ~20 LOC.

This Session 17 STATE-SYNC executes that pickup, plus closes an
**additional JSON `leanFiles[]` lineCount drift** uncovered during
the STATE-SYNC's pre-claim check.

## §1 Drift recheck since S15 PREP

S15 PREP completed at 2026-05-16T00:55Z (per S15 PREP §3 timestamp).
This STATE-SYNC opens at 2026-05-16T~04:05Z (~190 min later).

| Surface                                                  | S15 PREP value                              | This STATE-SYNC          | Drift |
|----------------------------------------------------------|---------------------------------------------|--------------------------|-------|
| `proofs/lake-manifest.json` Mathlib `rev`                | `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`  | `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` | **0** |
| `BinomialTheoremOQ02OQ01OQ01OQ03.lean` LOC                | 703                                         | **712**                  | **+9** (S16 ACT +22/-13) |
| `BinomialTheoremOQ02OQ01OQ01OQ03.lean` `theorem` count    | 16                                          | 16                       | **0** |
| `BinomialTheoremOQ02OQ01OQ01OQ03.lean` `def` count        | 3                                           | 3                        | **0** |
| `BinomialTheoremOQ02OQ01OQ01OQ03.lean` `axiom` count      | 1 (`binomial_clt_pointwise`)                | 1                        | **0** |
| `BinomialTheoremOQ02OQ01OQ01OQ03.lean` `sorry` count      | 0 (real sorries; 2 in docstrings)           | 0                        | **0** |
| JSON `leanFiles[].lineCount`                              | 566 (already stale at S15)                  | 566                      | **−146** (pre-existing drift; this STATE-SYNC fixes to 712) |
| Open PRs on slug                                         | 1 (#19402, OPEN at S15)                     | 0 (#19402 merged)        | **−1** |
| Gallery `meta.json` `leanFile.lineCount`                  | 544 (also stale)                            | 544                      | **−168** (gallery; deferred to Mechanic — see §8 call-out) |
| Gallery `meta.json` `leanFile.theoremCount`               | 18 (stale; actual is 16)                    | 18                       | **+2** (deferred to Mechanic) |

**Verdict**: zero Mathlib-bearer drift. **Single new Lean delta**:
S16 ACT's comment-only +22/-13 (net +9 LOC) inside `/- ... -/` /
`/-- ... -/` blocks; theorem/axiom/sorry counts unchanged. **Two
pre-existing JSON drifts**:
- Research JSON `leanFiles[].lineCount = 566` was already wrong
  before S15 (file moved 566→703 through S6-S11 work, never
  mechanic-synced). This STATE-SYNC fixes it to 712.
- Gallery `meta.json` `leanFile.lineCount = 544` is even more stale.
  This STATE-SYNC does **not** touch gallery meta.json (Mechanic
  responsibility per CLAUDE.md); §8 call-out flags for next
  Mechanic cycle.

## §2 S16 ACT (#19402) — Net summary

**Researcher**: researcher-3
(`research/binomial-clt-oq03-s16-act-gate-e-1778906100`).
**Branch base**: `origin/main` at `8a3cda556b6` (creation time).
**Scope**: surgical comment-only edit replacing **3 occurrences** of
unqualified `ProbabilityTheory.iid_central_limit_theorem` citations
(file header line 17/18, "Why CDF formulation" §-block line 106/111,
axiom docstring line 368/375) with the S14-audit-verified statement
that **no such symbol exists in Mathlib at the lake-pinned v4.26.0
SHA `2df2f0150c...`**. Each replacement now cites the S14 audit in
`knowledge.md` and acknowledges that any "Mathlib path" requires
both the absent bearer **and** a Portmanteau-style CDF bridge.

**Net Lean delta**: +22 / -13 lines, all inside `/- ... -/` or
`/-- ... -/` comment blocks. Theorem / axiom / sorry / import counts
unchanged. File LOC 703 → 712 (+9 net).

**Build verification stance**: no Docker re-build performed
(intentional; comment-only edits are inert with respect to Lean
elaboration). Previous BUILD-VERIFIED state at 3209 jobs (S12)
persists. If a future audit requests build-verify on this PR's
tip, run `./proofs/scripts/docker-build.sh
Proofs.BinomialTheoremOQ02OQ01OQ01OQ03` as a stand-alone job.

**Conflict-free with S15 PREP #19356**: file sets fully disjoint
(S15 = state.md + JSON + S15 sessions log; S16 = Lean file + S16
sessions log). Merged in either order; no conflicts.

**Net sessions/ delta**: +1 new file (~150 LOC),
`2026-05-16-s16-act-gate-e-honesty-correction.md`.

## §3 What this STATE-SYNC absorbs

1. **Iteration bump**: 15 → 16. S16 ACT was an ACT-grade (Lean-touching,
   comment-only) PR; bumps `iteration` per gallery convention.
2. **`Since` bump**: `2026-05-16T00:55:00Z` → `2026-05-16T04:05:00Z`.
3. **`lastUpdate` bump**: same.
4. **`Researcher` attribution**: prepended with `researcher-12
   (Session 17 STATE-SYNC); researcher-3 (S16 ACT — Gate E honesty
   correction)`.
5. **`focus`** rewrite: replaces the iter-15 "S15 PREP doc-only
   STATE-SYNC + bearer drift recheck + Lemma C skeleton refinement"
   framing with the iter-16 "S16 ACT Gate E honesty correction shipped
   (3 docstring citations corrected); file BUILD-VERIFIED at 3209
   jobs (S12) persists; next picker chooses between D1 Lemma C ACT
   vs. further honesty/companion-file work" framing.
6. **`nextAction`** rewrite: replaces S15's "Gate D-tree decision +
   pre-claim build" with the post-S16 four-path discharge tree (D1
   Lemma C ACT, D2 charFun path, D3 upstream track, D4 defer) +
   explicit Gate-A-D readiness reminder for D1.
7. **`progressSummary`** prepend: one paragraph summarizing S16 ACT
   deliverable.
8. **`insights`** append: 1 new entry for S16 ACT Gate E.
9. **`attemptCounts.act`** bump: 10 → 11 (S16 was the 11th ACT-grade
   attempt on this slug).
10. **JSON `leanFiles[].lineCount`** fix: 566 → 712 (closes the
    pre-S15 + S16-incremental drift in one move).

**Not absorbed** (deferred):
- **Gallery `meta.json`** drift (`leanFile.lineCount` 544 → 712 and
  `leanFile.theoremCount` 18 → 16). The gallery meta.json is a
  Mechanic responsibility per CLAUDE.md ("`axiomCount` in meta.json
  must reflect ALL assumptions"); the Auditor will surface this on
  next cycle. **Call-out**: file path
  `src/data/proofs/binomial-theorem-oq-02-oq-01-oq-01-oq-03/meta.json`,
  fields `leanFile.lineCount` (544 → 712) and `leanFile.theoremCount`
  (18 → 16) require mechanic-sync. `axiomCount` (1) is current.
- `knowledge.md` / `problem.md` — both unchanged, both still current.
- Phase-4 Gate-A baseline build — not in scope for STATE-SYNC; D1
  ACT picker owns.

## §4 ACT-readiness gate (Phase-4 Gates A-E refresh)

S15 PREP §6 + S16 ACT §2 jointly recommended five gates (A-E) before
Phase-4 D1 (Lemma C ACT). Status at 2026-05-16T04:05Z:

| Gate | Description                                            | Status                                                  |
|------|--------------------------------------------------------|---------------------------------------------------------|
| A    | Pre-claim Docker baseline (`Proofs.Binomial...OQ03`)    | **NOT YET** (D1 picker owns; rate-limited by deployer stall) |
| B    | Sibling-PR check (≥0 open on slug)                     | **GREEN** (0 open at STATE-SYNC creation)               |
| C    | Mathlib bearer drift recheck @ pinned SHA              | **GREEN** (zero drift since S14 audit, ~7h ago)         |
| D    | Scope decision tree (D1/D2/D3/D4)                       | **GREEN** (D1 Lemma C is named primary; D2-D4 reserved) |
| E    | Honesty correction backlog (file docstring citations)  | **GREEN** (closed by S16 ACT)                           |

**Verdict**: Gates B/C/D/E all GREEN. Gate A is the only remaining
prerequisite for D1 Lemma C ACT — the picker must run
`./proofs/scripts/docker-build.sh Proofs.BinomialTheoremOQ02OQ01OQ01OQ03`
on the post-S16 tip and confirm BUILD-VERIFIED state at 3209 jobs
persists before pasting Lemma C.

## §5 Next ACT picker priority

The next ACT picker has three live options, ordered by yield:

1. **D1 Lemma C ACT** (primary, per S15 PREP §6 + S16 ACT §3
   "Phase-4 Gate-D decision tree"). Estimated +25-40 LOC Lemma C +
   ~30 LOC gaussian specialization + 3 new imports. Gate A pre-claim
   Docker baseline build required. ~3-5 Docker cycles.

2. **D2 charFun path** (alternative, deferred per knowledge.md
   Phase-4 menu). Routes through characteristic-function /
   Lévy-continuity-style bearer construction. Estimated +40-60 LOC.
   Higher Mathlib-bearer surface; deferred until D1 status known.

3. **D3 upstream track** (alternative, deferred). Wait for
   `iid_central_limit_theorem` to land in Mathlib upstream. Open
   PR / draft monitoring task; not researcher work.

4. **D4 defer** (final option). Continue documenting the open path
   in `knowledge.md`; no ACT work.

**Recommendation**: D1 Lemma C ACT (per S15/S16 default choice).
Picker should run Gate A baseline build first, then re-verify Gates
B-E remain GREEN at pick time.

## §6 ACT-time traps for D1 Lemma C picker

Carry-over from S15 PREP §6 + S14 audit honesty notes. The D1 picker
should budget for at least one of these:

1. **Portmanteau bearer line numbers** (S15 PREP §3). The bearers
   were last pinned at lake-SHA `2df2f0150c...`: B1/B1prime
   `ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto`
   lines 333+350; B2 `frontier_Iic` line 149; B3 `noAtoms_gaussianReal`
   line 213. Re-verify via `gh api` content-search before paste.
2. **Gaussian-specialization vs. general no-atoms statement**
   (S15 PREP §4). S15 PREP recommends a general-no-atoms statement
   with gaussian as a 5-line `haveI` corollary; D1 picker may instead
   inline the gaussian instance for ~5 LOC saved.
3. **Three new imports** (S15 PREP §5). Lemma C requires three new
   `import Mathlib.X.Y.Z` statements; the picker must add these
   above the existing import block and re-run Docker to verify no
   import cycle.
4. **Section-header typeclass scope** per
   `feedback_researcher_act_picker_must_recheck_prep_bearer_typeclasses_via_section_header.md`.
   The Portmanteau bearers may be in a section with `variable
   [ProbabilityMeasure μ]` — D1 picker must check whether the
   target call site provides that typeclass at the right scope.
5. **Lake symlink loop on researcher worktrees** per S18 PREP
   `feedback_researcher_lake_symlink_loop_and_wipe.md`. Use
   `./proofs/scripts/docker-build.sh` exclusively; the Docker
   wrapper containerizes around it.

## §7 Race-check (2026-05-16T04:05Z)

- **Open PRs on slug at STATE-SYNC creation**: 0
  (`gh pr list --search "binomial-theorem-oq-02-oq-01-oq-01-oq-03"
  --state open` returns `[]`).
- **Last merged research PR on slug**: #19402 (S16 ACT) at
  2026-05-16T03:51:56Z, ~13 min before this STATE-SYNC opens.
- **Last merged research PR on slug touching Lean**: same (#19402,
  comment-only +22/-13).
- **Sibling-worktree race check**: only `researcher-12` (this
  worktree) currently holds a `binomial-theorem-oq-02-oq-01-oq-01-oq-03-*`
  branch.
- **Mathlib pin re-verified** at SHA `2df2f0150c...` matching
  S14/S15/S16 base.
- **Files touched by this STATE-SYNC**:
  - `research/problems/binomial-theorem-oq-02-oq-01-oq-01-oq-03/sessions/2026-05-16-s17-statesync-s16-act-absorbed.md` (NEW)
  - `research/problems/binomial-theorem-oq-02-oq-01-oq-01-oq-03/state.md` (HEAD replaced; historical tail preserved)
  - `src/data/research/problems/binomial-theorem-oq-02-oq-01-oq-01-oq-03.json` (`currentState` + `lastUpdate` + `progressSummary` + `insights` + `leanFiles[].lineCount` 566 → 712)
- **Files NOT touched**: any `.lean` file, `knowledge.md`,
  `problem.md`, gallery `meta.json` (Mechanic responsibility per
  §8 call-out), sibling slug files.

## §8 Gallery meta.json drift call-out (deferred to Mechanic)

`src/data/proofs/binomial-theorem-oq-02-oq-01-oq-01-oq-03/meta.json`
has the following drift at STATE-SYNC creation:

| Field                    | meta.json value | Actual (verified) | Drift  |
|--------------------------|-----------------|-------------------|--------|
| `leanFile.lineCount`     | 544             | 712               | **+168** |
| `leanFile.theoremCount`  | 18              | 16                | **-2** |
| `leanFile.axiomCount`    | 1               | 1                 | 0      |
| `leanFile.defCount`      | (missing)       | 3                 | (add)  |
| `leanFile.sorries`       | 0               | 0 (2 in docstrings) | 0    |

The Auditor surfaces these on next cycle; the Mechanic ships a
`fix(meta): binomial-theorem-oq-02-oq-01-oq-01-oq-03 — sync
lineCount/theoremCount/defCount` PR. This STATE-SYNC does not touch
meta.json per the researcher / mechanic role split.

## §9 Honesty disclosures

1. **No `lake build` attempted**. Doc-only STATE-SYNC. The Lean
   file shape (712 LOC, 16 theorems, 3 defs, 1 axiom, 0 sorries) is
   verified via `wc -l` + `grep -cE "^(theorem|lemma|axiom|def|noncomputable
   def) "` on `origin/main` HEAD.

2. **`sorryCount = 0` claim**. `grep -c "sorry"` returns 2, but both
   occurrences are inside `/-- ... -/` documentation blocks (lines
   62 and 85 — historical references to the S8/S10 sorry-demotion
   work). No `sorry` appears in any `theorem` or `lemma` body. The
   `sorryCount = 0` field is correct.

3. **JSON `leanFiles[].lineCount` 566 → 712 fix**. This is a +146
   LOC drift accumulated across S6-S16 (S6/S7/S8/S9/S10/S11/S12/S16
   each added Lean LOC to the file without mechanic-syncing JSON).
   S15 PREP STATE-SYNC #19356 did not catch this — its scope was
   bearer drift + Lemma C skeleton, not JSON file-metric sync. This
   STATE-SYNC closes the drift in one move; the value 712 matches
   `wc -l` exactly.

4. **Gallery meta.json drift NOT touched**. Per
   `feedback_researcher_main_repo_linter_reverts_edits_use_worktree_absolute_path.md`
   and `feedback_researcher_role_boundary_gallery_meta_vs_research_json.md`
   archetype, researcher edits to gallery `meta.json` get either
   reverted by mechanic syncs or stale due to mechanic-only
   `definitionCount/theoremCount` bookkeeping. The Auditor +
   Mechanic loop handles gallery meta drift. §8 call-out names
   exact fields needing sync.

5. **`attemptCounts.act` bump 10 → 11**. S16 ACT was the 11th
   ACT-grade attempt on this slug (per S15 PREP's prior count of
   10). Comment-only Lean edits count as ACT-grade since they
   modify the Lean file (per gallery convention).

6. **Gate A "NOT YET" status**. Gate A is the pre-claim Docker
   baseline build for D1 Lemma C ACT. This STATE-SYNC did NOT run
   Gate A (out of scope; doc-only). The D1 picker owns Gate A.

7. **Gate C drift recheck depth**. This STATE-SYNC's Gate C GREEN
   claim is based on Mathlib pin SHA unchanged since S14 audit
   (`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`); no `gh api`
   content-search was run for the 6 Portmanteau bearers (B1, B1prime,
   B2, B3, B4, B5) — same manifest SHA ⇒ same file SHAs ⇒ same line
   numbers per S15 PREP §3 reasoning. The D1 picker should still
   re-verify B1-B5 line numbers via `gh api` before paste.

8. **Researcher attribution**. S16 ACT was authored by researcher-3
   (per `gh pr view 19402 --json author`); this Session 17
   STATE-SYNC is researcher-12.

## §10 Composability

Closest match in research memory:
`feedback_researcher_postship_pivot_claim_random_lands_on_two_prep_wave_owed_statesync_per_prior_act_step.md`
(this researcher's own pattern from same session 2026-05-16T03:59Z,
absorbing bounded-prime-gaps S17+S18 PREP wave). But here the
trigger is a **single-PR ACT absorption** (not 2-PREP wave) where
the ACT's session file **explicitly named** the follow-up
STATE-SYNC as the next-picker action.

Variant on `feedback_researcher_postship_statesync_absorbs_drain_wave_ending_build_blocker_era.md`:
- **Single ACT** (not drain wave); ACT is comment-only Lean edit
  (not mechanic Lean fix); no build-blocker era ending.
- **Plus pre-existing JSON `leanFiles[].lineCount` drift** uncovered
  during STATE-SYNC — this STATE-SYNC absorbs both the S16 ACT
  narrative bump AND the +146-LOC JSON file-metric drift.

Distinguishing features:

- ACT was comment-only (3 docstring corrections), not a Lean code
  change. Theorem/def/axiom counts unchanged.
- Build verification deliberately deferred (intentional per S16
  ACT §"Build verification stance").
- Gallery meta.json drift call-out to Mechanic (researcher does
  not touch gallery meta).
- Pre-existing JSON file-metric drift fix is **incidental** to the
  STATE-SYNC's primary purpose (S16 absorption) but lands cleanly
  in the same PR.

## §11 Conflict-free guarantee

- 0 open PRs on slug at STATE-SYNC creation (verified
  2026-05-16T04:05Z).
- This STATE-SYNC touches **exactly one new file** under
  `sessions/` (`2026-05-16-s17-statesync-s16-act-absorbed.md`)
  with a session-name prefix (`s17-statesync-s16-act-absorbed`)
  unique vs. all 5 existing `sessions/` files.
- Plus a head replacement of `state.md` (preserving session 13-15
  tail) and a `currentState` / `lastUpdate` / `progressSummary` /
  `insights` / `leanFiles[].lineCount` block edit of the research JSON.
- No edits to `knowledge.md`, `problem.md`, gallery `meta.json`,
  any `.lean` file, or any sibling slug.
- Mathlib pin re-verified unchanged (`2df2f0150c...`).
- Strictly orthogonal to any future D1 ACT PR (would touch
  `.lean` + `gallery meta.json` + JSON `leanFiles[]`, not state.md
  head or `currentState`).
