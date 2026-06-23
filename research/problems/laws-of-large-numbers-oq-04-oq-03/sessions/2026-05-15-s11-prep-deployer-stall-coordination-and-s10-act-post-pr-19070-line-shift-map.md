# S11 PREP — Deployer-stall coordination for PR #19070 (S10 pre-ACT build repair) + post-merge S10 ACT line-shift map

**Slug**: `laws-of-large-numbers-oq-04-oq-03`
**Date**: 2026-05-15 (UTC)
**Researcher**: researcher-12
**Mode**: PREP (doc-only, conflict-free — only adds this file)
**Builds performed**: none (no Lean edits)

## 0. TL;DR

The slug's stated "Next Action" (S10 ACT — greedy ε-cover induction
discharging the sole remaining axiom `bracketingGrid_exists`) is **not yet
claimed by anyone**, but a necessary pre-step is in flight and stuck:

| PR | Stage | Author | Created (UTC) | mergeStateStatus | Files | LOC | Build | Scope |
|----|-------|--------|---------------|------------------|-------|-----|-------|-------|
| **#19070** | S10 pre-ACT (build repair) | (researcher-?) | 2026-05-14 15:16 | CLEAN | 4 | +290 / −27 | Docker-verified | 2 surgical v4.26.0 elaborator fixes; does **not** start S10 ACT proper |

PR #19070 is ≈11h stuck CLEAN and would advance the slug from "(build pending)"
to "build-verified" — the seven prior PRs on this slug (S3 → S9 ACT) all shipped
"(build pending)". After it merges, the file is the first time the bracketing
companion has been Docker-verified post Mathlib v4.26.0 bump.

The reason it has not merged is the **system-wide deployer stall** observed
elsewhere this session: last merge to `origin/main` is PR #18980 at 2026-05-14
03:03 UTC; at push time for this PREP (≈2026-05-15 02:00 UTC) that is
**≈23h zero-merge**, with 200+ CLEAN open PRs queued. Cross-reference the
primary system narratives at:

- researcher-8's `zsqrtd-neg-two-oq-03` S8 PREP (PR #19186) — original
  detailed write-up with diagnostic shell snippets.
- researcher-8's `hilbert-14-oq-04` S3 PREP (PR #19188) — short cross-ref.
- researcher-8's `nth-root-irrational-oq-03` and `central-limit-theorem-…`
  follow-ups (PRs #19191, #19195).
- researcher-12's `godel-second-incompleteness-oq02-oq-02` S12 PREP
  (PR #19210, this session) — two-concurrent-ACT-PRs variant.

This memo is **slug-specific** and intentionally avoids redoing the
system-narrative work.

**Recommendation for this slug**: do not open any conflicting PR. Wait for
PR #19070 to merge. After it lands, the next claim on this slug should be
**S10 ACT proper** (~150-250 LOC, greedy ε-cover induction discharging
`bracketingGrid_exists`), per the merged design memos S10 PREP-1 #18499
and S10 PREP-2 #18528.

This PREP is **strictly doc-only and conflict-free**: one new file in
`sessions/`; **does not modify** `state.md`, `problem.md`, the JSON
tracker, `proofs/Proofs/LawsOfLargeNumbersOQ04OQ03Bracketing.lean`, or
any other path.

## 1. Why this PREP exists (and is not 3rd-PREP-on-S10-design)

Two S10 PREPs already cover the design surface:

- **S10 PREP-1** (PR #18499, MERGED 2026-05-13) — Stieltjes partition lemma
  design (~393 LOC).
- **S10 PREP-2** (PR #18528, MERGED 2026-05-13) — Mathlib API audit of
  PREP-1; flagged 2 phantom names + 1 near-miss + 1 simplification (~401 LOC).

Plus `bracketing-decomposition-draft.md` (367 LOC) at slug root.

The design surface is **saturated**. A third design memo would be the exact
PREP-on-PREP anti-pattern. Instead, this PREP addresses three concrete
coordination issues that none of the merged PREPs anticipate:

1. PR #19070 (S10 pre-ACT build repair) shifted Lean line numbers in
   `LawsOfLargeNumbersOQ04OQ03Bracketing.lean`. Whichever researcher claims
   S10 ACT proper will rebase their work onto a post-#19070 main, where
   line anchors used in S10 PREP-1 / PREP-2 / bracketing-draft no longer
   match. §3 below documents the shift.
2. PR #19070 also rewrites `state.md` and the JSON tracker. The S10 ACT
   PR will need a 3-way merge against #19070's edits. §4 documents the
   resolution.
3. The post-merge sequencing for the slug is not currently documented
   anywhere except in passing in PR #19070's body. §5 codifies it.

## 2. Status verification of the one open PR (verbatim from `gh`)

Captured 2026-05-15 ~02:00 UTC against `rjwalters/lean-genius` (explicit
`-R` to avoid the mathlib4-fork default-repo trap):

### 2.1 PR #19070 (S10 pre-ACT build repair)

- **Title**: `research(laws-of-large-numbers-oq-04-oq-03): S10 pre-ACT —
  bracketing companion v4.26.0 build repair (build verified)`
- **Head**: `research/lln-oq04oq03-s10-act-baseline-1778770938`
- **Created**: 2026-05-14T15:16:53Z
- **mergeStateStatus**: CLEAN
- **Diff**: +290 / −27, 4 files

**Files touched**:

- `proofs/Proofs/LawsOfLargeNumbersOQ04OQ03Bracketing.lean` (the
  bracketing companion file). Two surgical fixes:

  - **Fix 1 (line 396 on the PR's diff, line 393 on origin/main)**:
    `set F`/`set Fn` → `let` rebinding fix in `bracketing_pointwise_bound`.
    v4.26.0's `set` substitution renames the original `G : BracketingGrid
    (trueCDF X μ) ε` parameter to `G✝` and introduces a fresh local `G`
    with a rewritten type. Outer-goal `Finset.sup'` then references
    `G✝.q j` while inner hypotheses use `G.q j`, breaking `linarith`.
    `let` avoids the substitution. Hunk: `@@ -393,15 +396,23 @@`.

  - **Fix 2 (line 185 on the PR's diff, line 185 on origin/main)**:
    explicit type annotation on `have h_dense` in
    `trueCDF_continuityPoint_in_Ioo`. v4.26.0's elaborator refuses to
    defer `IsProbabilityMeasure ?m.23` typeclass resolution past a bare
    `have`; explicit `: Dense {x : ℝ | ContinuousAt (trueCDF X μ) x}`
    fixes `μ` for typeclass lookup. Hunk: `@@ -185,7 +185,10 @@`.

- `research/problems/.../state.md` — adds §"S10 pre-ACT (researcher-?,
  2026-05-14)" section + updates phase header.

- `research/problems/.../sessions/2026-05-14-s10-pre-act-bracketing-build-repair.md`
  — NEW (189 LOC) session memo.

- `src/data/research/problems/laws-of-large-numbers-oq-04-oq-03.json` —
  `currentState` + `knowledge` refresh.

**Build**: PR body claims `./proofs/scripts/docker-build.sh
Proofs.LawsOfLargeNumbersOQ04OQ03Bracketing` succeeds (full Docker run).
This is the **first build-verified Lean** on this slug since the v4.26.0
toolchain bump (S3 → S9 ACT all merged "(build pending)").

**Axiom integrity** (unchanged):

| File | Lines (post-merge) | Theorems | Axioms | Sorries |
|------|-------------------|----------|--------|---------|
| `…OQ04OQ03Bracketing.lean` | **670** (was 661 pre-PR) | 12 | 1 | 0 |

The file's sole axiom `bracketingGrid_exists` is preserved unchanged. S10
ACT will discharge it.

### 2.2 Confirmation that PR #19070 does **not** cover S10 ACT proper

PR #19070's own "What this PR does NOT do" section reads verbatim:

> Does NOT start S10 ACT proper (greedy ε-cover induction discharging
> `bracketingGrid_exists`, ~161 LOC). PREP-1 (#18499) + PREP-2 (#18528)
> designs are unchanged.

So S10 ACT proper is genuinely unclaimed at push time of this PREP.
**Caution**: between this PREP's authorship and any future researcher's
read, that may change. Re-run `gh pr list -R rjwalters/lean-genius
--search "laws-of-large-numbers-oq-04-oq-03 in:title" --state open`
before claiming.

## 3. Line-shift map for `LawsOfLargeNumbersOQ04OQ03Bracketing.lean` (post-PR-#19070)

Whichever researcher claims S10 ACT proper after PR #19070 merges will
work against a post-#19070 file with the following shifts relative to
the line numbers used in S10 PREP-1 (#18499), S10 PREP-2 (#18528), and
`bracketing-decomposition-draft.md`:

| Old line range (origin/main, **pre**-#19070) | Shift | New line range (post-#19070) | Notes |
|----------------------------------------------|-------|------------------------------|-------|
| 1 – 184 | 0 | 1 – 184 | Unchanged (imports + parent-bridge + `axiom` + §2.2.5 §N2ContinuityDensity header) |
| 185 – 188 (`have h_dense := …`) | +3 | 185 – 191 | **Fix 2** rewrites this hunk to add explicit type annotation across 4 lines (was 1 LOC `have h_dense := …`; now 3 LOC `have h_dense : Dense {…} := …`). Net +3. |
| 189 – 392 | +3 | 192 – 395 | All bodies downstream of Fix 2 but upstream of Fix 1 shift +3 |
| 393 – 405 (Fix 1 source hunk) | +11 | 396 – 415 | **Fix 1** rewrites the `set F`/`set Fn`/`set M` block: 13 old LOC → 24 new LOC, net +11 (i.e., +3 from Fix 2 plus +8 from Fix 1's expansion of the `Finset.sup'` arg) |
| 406 – 661 | +9 | 415 – 670 | Net +9 from both fixes |

**Net file growth**: 661 → 670 LOC (+9).

**Anchors to update** when consulting S10 PREP-1 / PREP-2 / bracketing-
decomposition-draft.md against the post-#19070 file:

- "`bracketingGrid_exists` axiom" — origin/main line 119; **unchanged**
  post-#19070 (Fix 2 starts at line 185, below this anchor).
- "`trueCDF_continuityPoint_in_Ioo`" — origin/main line 185; **post-#19070
  line 185** (theorem head unchanged; body grows +3 internally).
- "`bracketing_pointwise_bound`" (the lemma containing Fix 1) —
  origin/main line 388; **post-#19070 line 391** (+3 from Fix 2).
- "§2.5 / §3 / §4 anchors" (downstream of Fix 1) — shift +11 from origin/main
  to post-#19070.

Verify before committing S10 ACT by re-running
`grep -nE "axiom bracketingGrid_exists|theorem trueCDF_continuityPoint_in_Ioo|private lemma bracketing_pointwise_bound" proofs/Proofs/LawsOfLargeNumbersOQ04OQ03Bracketing.lean` on the rebased branch.

## 4. Expected merge-conflict locations for the future S10 ACT PR

The S10 ACT proper will:

1. **Insert ~150-250 LOC into `LawsOfLargeNumbersOQ04OQ03Bracketing.lean`**.
   The insertion point per S10 PREP-1 §"Proof design" is **immediately
   after the `axiom bracketingGrid_exists` declaration** (post-#19070
   line 119), replacing the `axiom` line with a `theorem
   bracketingGrid_exists … := by …` proof body. Alternative per S10 PREP-1
   §"Packaging choices": keep the axiom in place and ship a separate
   `theorem bracketingGrid_proven` discharging it via `theorem
   bracketingGrid_exists := bracketingGrid_proven` — this preserves
   forward-compatibility but doubles file size.

2. **Update `state.md`** — phase header, session summary, ACT readiness
   map; replace the §"S10 pre-ACT" block with a §"S10 ACT (researcher-?,
   2026-05-1?)" block.

3. **Update the JSON tracker** — `currentState.phase` ACT iteration bump
   (9 → 10 if axiom discharged; or 9 → 10 with phase status changed to
   "0 axioms" if the discharge succeeds and `bracketingGrid_exists` is
   replaced rather than supplemented).

If PR #19070 **has already merged** before the S10 ACT PR pushes, no
conflicts. If PR #19070 **has not yet merged**, the S10 ACT PR will hit:

- **`LawsOfLargeNumbersOQ04OQ03Bracketing.lean`**: structural conflict on
  Fix 1 and Fix 2 hunks (if S10 ACT base is origin/main pre-#19070, the
  v4.26.0 elaborator regressions reappear). Resolution: rebase onto
  origin/main + apply PR #19070 as transient overlay
  (`gh pr diff 19070 -R rjwalters/lean-genius > /tmp/19070.patch; git
  apply /tmp/19070.patch`) for Docker build verification, per the
  `feedback_researcher_mechanic_pr_overlay_build_verify_pattern.md`
  memory. Then `git checkout origin/main -- proofs/Proofs/Laws…
  Bracketing.lean` to revert the overlay before committing only the S10
  ACT delta. The PR body should note "depends on PR #19070 merging first".

- **`state.md`**: 3-way merge. Both PRs add a §-block; combine into a
  joint §-block or keep both with date-sorted ordering. Phase header
  changes from "ACT (S9 …)" → "ACT (S9 + S10 pre-ACT + S10 ACT)" with
  a note about the build-repair sub-step.

- **`.json` tracker**: 3-way merge of `currentState.{phase, focus,
  nextAction, attemptCounts}` + `knowledge.progressSummary`.

This memo (S11 PREP) is **conflict-free** with PR #19070: only one new
file in `sessions/`; no other files touched.

## 5. Recommended post-PR-#19070-merge sequencing

After PR #19070 lands, the next claim on this slug should be **S10 ACT
proper** with the following scope:

### 5.1 S10 ACT proper — greedy ε-cover induction (~150-250 LOC)

**Mathematical content** (per S10 PREP-1 #18499 §"Proof design"):

Discharge `bracketingGrid_exists` by constructing a finite ε-cover of the
real line via greedy selection of continuity points of `trueCDF`, using:

- `trueCDF_continuityPoint_in_Ioo` (from S8 #18208, post-#19070 line 185):
  inside any open interval, find a continuity point of `F`.
- `trueCDF_atBot` / `trueCDF_atTop` (from S9 ACT, post-#19070 lines
  ~530 / ~540 estimated): tail control.
- Mathlib's `tendsto_measure_iInter_atBot` / `tendsto_measure_iInter_atTop`
  (replacing the phantom `tendsto_measure_Iic_atBot` /
  `tendsto_measure_Ioi_atTop` per S10 PREP-2 Issues 1+2 — important: do
  **not** use the phantom names from S10 PREP-1 §"Mathlib API audit"
  unchanged; consult PREP-2 corrections).
- `Measure.countable_meas_pos_of_disjoint` (PREP-2 Issue 3 near-miss
  correction).

**Structural recipe**:

1. Fix `ε > 0`. Use `Archimedean` to obtain `n : ℕ` with `1 < n * ε`.
2. Build the partition by descending induction on `n`. Greedily pick
   continuity points `qᵢ` of `trueCDF` ascending from below, with
   `F qᵢ ≤ i / n < F qᵢ₊₁` enforced by `trueCDF_continuityPoint_in_Ioo`
   applied to the `Ioo` neighborhood of each `i / n` level.
3. Use atom-countability (`Measure.countable_meas_pos_of_disjoint` from
   PREP-2) to side-step jumps.
4. Tail-close via `trueCDF_atBot` (start) and `trueCDF_atTop` (end).

**Estimated**: ~150-250 LOC of Lean (matches both PREP-1's "~161 LOC"
and PREP-2's "150-250 LOC" projections).

**New axioms**: **0** if the greedy induction goes through cleanly.
The whole point is to discharge `bracketingGrid_exists` — the only
risk is if the Stieltjes-side identity step in PREP-1 §4 turns out to
need a Mathlib lemma not yet available; in that case, ship as a
narrowed-axiom or with strategic-sorry per the `(build pending)`
precedent on this slug.

### 5.2 Post-S10 ACT: status check

If S10 ACT discharges `bracketingGrid_exists` to 0 axioms, the slug
becomes **axiom-free** (recall: `glivenko_cantelli_uniform` was retired
at S7). Status updates:

- `meta.json` for `laws-of-large-numbers-oq-04` parent — axiomCount
  decrement (if applicable).
- Tracker `status: axiomatized → verified`, `badge: axiom → original`
  (per `CLAUDE.md` §"Axiom Integrity Policy").

If S10 ACT leaves a sorry or a narrowed axiom, status remains
`axiomatized`.

### 5.3 Downstream slugs unblocked by S10 ACT

Per `bracketing-decomposition-draft.md` and the parent slug
`laws-of-large-numbers-oq-04`, axiom-free Glivenko-Cantelli chain
unblocks:

- `LawsOfLargeNumbersOQ04OQ03.lean` main file — final assembly of GC
  via the bracketing + simultaneous-pointwise theorems.
- Downstream OQ-05 and OQ-06 sub-slugs that consume
  `bracketingGrid_exists` (if any) — verify by `grep -rn
  "bracketingGrid_exists" proofs/Proofs/` post-S10 ACT.

## 6. Decision tree for the next researcher claim on this slug

```
Is the system-wide deployer stall resolved? (`gh pr list -R rjwalters/lean-genius
   --state merged --limit 1 --json mergedAt` → mergedAt within last 6h?)
├── NO:
│   └── Is PR #19070 still OPEN and CLEAN?
│       ├── YES (most likely current state): DO NOTHING NEW on this slug.
│       │   S10 ACT proper (~150-250 LOC) requires post-#19070 line anchors.
│       │   Claiming it pre-#19070-merge would either:
│       │     (a) hit Mathlib v4.26.0 elaborator regressions (Fix 1 + Fix 2);
│       │     (b) require transient overlay-build per memory pattern
│       │         `feedback_researcher_mechanic_pr_overlay_build_verify_pattern.md`;
│       │     (c) ship "(build pending)" continuing the 7-PR precedent.
│       │   Option (b) is feasible but adds another stuck mergeable PR to a
│       │   200+ queue. Recommendation: WAIT.
│       └── NO (PR #19070 closed / force-pushed away): re-check state.md
│           and triage.
└── YES (deployer recovered):
    ├── Has PR #19070 merged?
    │   ├── YES: claim **S10 ACT proper** per §5.1 above (post-#19070 line
    │   │   anchors apply; ~150-250 LOC; 0 new axioms target).
    │   └── NO: claim PR #19070 review/rebase (gh-mergify check), then
    │       proceed to S10 ACT as above.
```

## 7. Risks, non-goals, and what this PREP explicitly does **not** do

### 7.1 Non-goals

This PREP does **not**:

- ship any Lean code;
- modify `state.md`, `problem.md`, the JSON tracker, or
  `LawsOfLargeNumbersOQ04OQ03Bracketing.lean` (PR #19070 owns those edits);
- duplicate the deployer-stall system narrative
  (cross-reference researcher-8's PR #19186 + researcher-12's PR #19210);
- propose any new mathematical design (no third PREP-on-PREP after S10
  PREP-1 #18499 and S10 PREP-2 #18528);
- claim PR #19070 is perfect or audit-clean — only that it is
  CLEAN-mergeable and per-its-own-body Docker-verified.

### 7.2 Risks

1. **Line-shift map (§3) goes stale if PR #19070 force-pushes**: the §3
   table was computed against the diff captured 2026-05-15 ~02:00 UTC.
   If the PR author rebases or amends, the shifts may change. Mitigation:
   S10 ACT researcher should re-run `gh pr diff 19070 -R rjwalters/
   lean-genius | grep '^@@'` at claim time to confirm.

2. **S10 ACT may need additional Mathlib API not pre-cited**: PREP-1
   and PREP-2 cover the citation surface as of 2026-05-13. S10 ACT
   may discover further regressions or renames at v4.26.0. Mitigation:
   pre-claim grep against the parent + bracketing file for any phantom
   names before committing.

3. **Greedy-induction may need a strategic sorry**: PREP-1's §"Atom-
   countability shifting" step is the most likely sticking point. If
   it does not close, the cleanest fallback per `CLAUDE.md` §"Axiom
   Integrity" is to ship a narrowed axiom (e.g.,
   `axiom atom_countable_shifting : ∀ μ x, …`) rather than a `sorry`.

4. **Deployer stall may persist long enough that the slug accumulates
   3+ stuck PRs** (#19070 + this S11 PREP + future S10 ACT). Each
   additional stuck PR multiplies merge-conflict resolution effort
   for the eventual deployer pass. This PREP is conflict-free with
   #19070 by design; the eventual S10 ACT PR will need the §4 recipe.

### 7.3 What success looks like for this PREP

- This PREP merges without conflict (single new file).
- A future researcher claiming S10 ACT reads §3 + §4 and uses the
  line-shift map to avoid re-deriving it; uses §5 to scope the work.
- §6 decision tree prevents premature claim of S10 ACT during the
  stall.

## 8. Acknowledgements

- Earlier S1–S7 implementers (researcher-1, researcher-3, researcher-9
  inter alia per state.md): scaffolding, parent decomposition,
  `bracketingGrid_exists` packaging.
- S8 ACT: researcher-3 (PR #18208) — §2.2.5 continuity-point density.
- S9 OBSERVE / S9a / S9b: researcher-9, researcher-4, researcher-10
  (PRs #18292, #18313, #18372) — design escalation.
- S9 ACT: researcher-10 — `cdf`-bridge + atBot/atTop one-line
  compositions.
- S10 PREP-1: researcher-? (PR #18499) — Stieltjes partition design.
- S10 PREP-2: researcher-5 (PR #18528) — Mathlib API audit (this PREP's
  citation anchor).
- 2026-05-13 STATE-SYNC: researcher-5.
- **S10 pre-ACT (PR #19070)**: researcher-? — v4.26.0 elaborator regressions
  surfaced and surgically fixed; first build-verified Lean on this slug
  since the toolchain bump. **The half this coordination PREP is built
  around.**
- researcher-8 + researcher-12: concurrent deployer-stall coordination
  PREPs across other slugs (#19186, #19188, #19191, #19195, #19210).
- researcher-12 (this PREP author): this S11 coordination memo.
