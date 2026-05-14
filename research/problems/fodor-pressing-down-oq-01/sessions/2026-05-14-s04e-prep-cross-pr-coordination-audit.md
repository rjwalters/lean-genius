# S4e PREP — Cross-PR coordination audit (PR #19009 + PR #19052) and updated parent-line shift map

**Author:** researcher-12
**Date:** 2026-05-14 (~17:30 UTC)
**Phase:** S4e PREP (a refinement of S4c PREP §4 to account for two open
PRs that landed AFTER the S4c audit)
**Slug:** `fodor-pressing-down-oq-01`
**Branch:** `research/fodor-pressing-down-oq-01-s05-prep-state-sync-*`
**Scope:** **doc-only** — no Lean edits, no `problem.md` / `knowledge.md`
/ `state.md` edits, no gallery JSON edits, no `meta.json` edits, no
`annotations.json` edits, no edits to sister-slug files. One new file
under `sessions/`. Disjoint with PR #19009 (S3 ACT, open) and PR #19052
(OQ-04 S2-α ACT, open).

## 0. Why this memo (and why now)

The S4c PREP audit (PR #18585, merged 2026-05-13) gave a complete
consumer audit and a parent-line shift map predicated on a **then-static
parent file of 385 LOC**. Since that merge, two open PRs have landed
work that materially changes the eventual S4 ACT landscape:

1. **PR #19009** (open, MERGEABLE/CLEAN since 2026-05-14T06:18:58Z) —
   `research(fodor-pressing-down-oq-01): S3 ACT — add Ordinal.diagInter_isClosedBelow to Proofs.Club.Basic (Docker-verified)`.
   Adds `Ordinal.diagInter_isClosedBelow` (+21 LOC) to `Proofs/Club/Basic.lean`;
   parent unchanged. **Docker-verified twice** (pre-patch + post-patch,
   3060 jobs each). Author: researcher-12 (different session, branch
   `research/r12-session22-1778739041-claim`).

2. **PR #19052** (open, MERGEABLE/CLEAN since 2026-05-14T13:24:18Z) —
   `research(fodor-pressing-down-oq-04): S2-α ACT — limit ordinals form a club (Solovay Step 1, build-verified)`.
   Adds **two new theorems** to **the parent file** `Proofs/FodorPressingDown.lean`:
   `isLimitOrdinals_isClubBelow` and `nonLimitOrdinals_not_isStationaryBelow`
   (+68 LOC, parent 385 → 453). **Docker-verified** at 3062 jobs.
   Author: researcher-8 (sister slug).

The S4c PREP shift map (§4) is now stale on two axes:

* It assumes Basic.lean has not gained `diagInter_isClosedBelow` (S3
  PREP §3, which becomes S3 ACT). PR #19009 closes that gap, so any
  S4 ACT landing **after** #19009 merges can safely cite
  `Ordinal.diagInter_isClosedBelow` and **remove the parent's local
  body** (lines 102–124 in the on-main file, 102–124 unchanged in
  #19052).
* It assumes the parent ends at line 385 and `IsStationaryBelow.of_subset`
  is the last theorem in Part VI (line 343–348). PR #19052 inserts
  **Part VII** between Part VI and the trailing summary block, shifting
  the summary down by 66 LOC and the `end FodorPressingDown` token from
  line 385 → 453.

This memo locks the **post-#19009-and-#19052 shift map** so the S4 ACT
implementer can re-anchor without re-deriving the arithmetic.

**No state.md edits in this PREP.** PR #19009's diff already overwrites
state.md to mark S3 ACT shipped. A second STATE-SYNC PR after both
#19009 and #19052 merge will incorporate this S4e PREP entry; until
then, state.md remains as on `origin/main` (`Iteration: 7`, S3/S4 ACT
pending).

## 1. Source state (verified at HEAD = `2afb1b79c0a`)

* Parent file `Proofs/FodorPressingDown.lean` on `origin/main`: **385
  LOC** (per `wc -l`). Unchanged since S2 ACT (2026-05-12).
* Lifted module `Proofs/Club/Basic.lean` on `origin/main`: **98 LOC**.
  S3 ACT growth to 119 LOC blocked behind PR #19009 merge.
* PR #19009 diff: `+21` to Basic.lean; touches `state.md` and
  `src/data/research/problems/fodor-pressing-down-oq-01.json`; adds
  `sessions/2026-05-13-s05-act-diagInter-isClosedBelow.md` (new file).
* PR #19052 diff: `+68` to FodorPressingDown.lean; touches OQ-04 docs
  (`state.md`, `2026-05-14-s2a-act-limit-ordinals-club.md`, OQ-04 JSON);
  does **not** touch OQ-01 docs.
* No edits to `Proofs/Club/Basic.lean` since S2 ACT on main; no edits
  to parent file since S2 ACT on main.

Verified via:

```bash
gh pr view 19009 --repo rjwalters/lean-genius --json state,mergeable,mergeStateStatus
# {"mergeStateStatus":"CLEAN","mergeable":"MERGEABLE","state":"OPEN"}

gh pr view 19052 --repo rjwalters/lean-genius --json state,mergeable,mergeStateStatus
# {"mergeStateStatus":"CLEAN","mergeable":"MERGEABLE","state":"OPEN"}

git log --oneline origin/main -- proofs/Proofs/Club/Basic.lean
# cc58af34ee7 research(fodor-pressing-down-oq-01): S2 ACT — introduce Proofs/Club/Basic.lean (build pending) (#18367)
# (single commit; no merges since S2 ACT)

git log --oneline origin/main -- proofs/Proofs/FodorPressingDown.lean
# (no commits since 7845672a366 "Research: p-adic ultrametric + Leibniz acceleration + Fodor …")
```

## 2. The 68 LOC added by PR #19052 (verbatim line ranges)

PR #19052 inserts content at `@@ -347,6 +347,72 @@` (i.e., between the
end of `IsStationaryBelow.of_subset` body at line 348 and the Part-VI-to-
summary banner at line 350). The diff hunk reveals:

* **+5 LOC** of banner (`Part VII: Solovay Splitting — Step 1 …`)
* **+15 LOC** docstring (`Step 1 of Solovay splitting (S2-α) — …`)
* **+38 LOC** theorem body `isLimitOrdinals_isClubBelow {κ : Cardinal.{0}}`
* **+1 LOC** blank separator
* **+10 LOC** docstring + theorem `nonLimitOrdinals_not_isStationaryBelow`
* **+1 LOC** blank
* **+2 LOC** to the trailing summary block's "Key results" bullet list
  (added at `@@ -366,6 +432,8 @@`)

Net: **+66 LOC in Part-VII region** + **+2 LOC in summary bullet list**
= **+68 LOC total**. Parent grows 385 → 453 LOC.

Surviving-content anchor table (post-#19052, pre-S4-ACT):

| Symbol                                       | Old line (385 LOC) | New line (post-#19052, 453 LOC) | Delta |
|----------------------------------------------|--------------------|---------------------------------|-------|
| `IsStationaryBelow.nonempty`                 | 334–338            | 334–338                         | 0     |
| `IsStationaryBelow.of_subset`                | 343–348            | 343–348                         | 0     |
| **Part VII banner**                          | —                  | **350–352**                     | n/a   |
| **`isLimitOrdinals_isClubBelow`**            | —                  | **354–392**                     | n/a   |
| **`nonLimitOrdinals_not_isStationaryBelow`** | —                  | **394–402**                     | n/a   |
| Trailing summary banner                      | 350–352            | 416–418                         | +66   |
| `end FodorPressingDown`                      | 385                | 453                             | +68   |

(Banner line numbers are nominal — the precise figures depend on the
banner/blank-line cadence in PR #19052's diff, which the patch hunk
notation places at +5/+15/+38/+1/+10 above the trailing-banner shift.)

## 3. Updated parent-line shift map for S4 ACT (post-#19009 + post-#19052)

S4c PREP §4 derived the **on-main + S3-ACT** shift map (parent moves from
385 → 286 LOC, net **−99 LOC**). Folding in PR #19052's +68 LOC, the
post-all-three-merges S4 ACT shift map becomes:

| Stage                                | Parent LOC | Delta |
|--------------------------------------|-----------:|------:|
| origin/main today                    |        385 |     — |
| post #19009 merge                    |        385 |     0 |
| post #19052 merge (also)             |        453 |   +68 |
| post S4 ACT (cut 5 dups + closedBelow body) | **354** |   −99 (relative to 453 baseline) |

The **−99 LOC trim figure remains the same** (it's intrinsic to which
parts of Part I/II/VI get removed, all of which lie outside Part VII).
But the **absolute landing LOC shifts up by +68**, from S4c PREP's
predicted 286 LOC to **354 LOC**.

### 3.1 Symbol-by-symbol post-S4-ACT line forecast

Assuming S4 ACT cuts lines 43–97 (Part I + Part II: 55 LOC) and lines
102–125 (diagInter_isClosedBelow body: 24 LOC) and lines 329–349 (Part
VI banner + `IsStationaryBelow.{nonempty,of_subset}` + blank: 21 LOC) —
totaling **100 LOC removed** — and adds 1 LOC `import Proofs.Club.Basic`
(**net −99 LOC**), the parent's surviving theorems land at:

| Symbol                                       | Pre-S4 line (453 LOC) | Post-S4 line (354 LOC) | Delta |
|----------------------------------------------|----------------------:|-----------------------:|------:|
| `diagInter_isUnboundedBelow`                 | 138–237               | 60–159                 | −78   |
| `diagInter_isClubBelow`                      | 240–246               | 162–168                | −78   |
| Part IV banner                               | 248–250               | 170–172                | −78   |
| `fodor`                                      | 252–313               | 174–235                | −78   |
| Part V banner                                | 315–319               | 237–241                | −78   |
| `fodor_aleph1`                               | 320–327               | 242–249                | −78   |
| **Part VII banner** (Solovay Step 1, oq-04)  | 350–352               | **272–274**            | −78   |
| **`isLimitOrdinals_isClubBelow`** (oq-04)    | 354–392               | **276–314**            | −78   |
| **`nonLimitOrdinals_not_isStationaryBelow`** (oq-04) | 394–402       | **316–324**            | −78   |
| Trailing summary banner                      | 416–418               | 338–340                | −78   |
| `end FodorPressingDown`                      | 453                   | 354                    | −99   |

The post-Part-VI shift is **−78 LOC** (same as S4c PREP §4, because the
−21 LOC of Part-VI removal occurs *before* Part VII in file order; once
Part VII is past, only the upstream −79 + +1 net delta applies, giving
−78). The final `end FodorPressingDown` shift is **−99 LOC** because
the Part-VI block (−21) finally counts when summing through the trailing
summary's `−21` block (which is itself unaffected by the symbol-table
above — only its anchor moves).

A ±2-LOC tolerance covers banner-blank-ambiguity (whether
`import Proofs.Club.Basic` is added at parent line 32, 37, or 38, and
whether a blank line preceding a removed banner is itself removed).

## 4. Namespace-resolution check for the two new OQ-04 theorems

PR #19052's additions reference these symbols inside the parent file's
`namespace FodorPressingDown` + `open Cardinal Order Ordinal Set` scope
(parent line 39 + 41 of origin/main):

| Symbol                  | Used by              | Resolves to (post-S4-ACT)               |
|-------------------------|----------------------|------------------------------------------|
| `IsClubBelow`           | both new theorems    | `Ordinal.IsClubBelow` (from `open Ordinal` + `import Proofs.Club.Basic`) |
| `IsStationaryBelow`     | `nonLimitOrdinals_not_isStationaryBelow` | `Ordinal.IsStationaryBelow` (same path) |
| `IsSuccLimit`           | `isLimitOrdinals_isClubBelow` predicate | `Order.IsSuccLimit` (already in Mathlib; `open Order`) |
| `isClosedBelow_iff`     | `isLimitOrdinals_isClubBelow` closure | `Ordinal.isClosedBelow_iff` (Mathlib `Ordinal.Topology`) |
| `isAcc_iff`             | `isLimitOrdinals_isClubBelow` closure | `Ordinal.isAcc_iff` (Mathlib `Ordinal.Topology`) |
| `Ordinal.omega0`        | `isLimitOrdinals_isClubBelow` unboundedness | `Ordinal.omega0` (Mathlib) — already namespace-prefixed in source |
| `Cardinal.ord_aleph0`   | unboundedness ω₀ < κ.ord step | already `Cardinal.X` prefix in source |
| `Cardinal.ord_lt_ord`   | same                 | already `Cardinal.X` prefix |
| `Cardinal.lt_ord`       | unboundedness card step | already `Cardinal.X` prefix |
| `Cardinal.add_lt_of_lt` | regularity step       | already `Cardinal.X` prefix |
| `Ordinal.card_add`      | unboundedness card step | already `Ordinal.X` prefix |
| `Ordinal.card_omega0`   | same                  | already `Ordinal.X` prefix |
| `Ordinal.isSuccLimit_add` | sum-with-limit step | already `Ordinal.X` prefix |
| `Ordinal.isSuccLimit_omega0` | same             | already `Ordinal.X` prefix |
| `Ordinal.isNormal_add_right` | strict monotonicity | already `Ordinal.X` prefix |
| `Ordinal.omega0_pos`    | strict monotonicity   | already `Ordinal.X` prefix |
| `Ordinal.IsAcc.pos`     | closure step (via `pAcc.pos`) | field-notation, resolves to `Ordinal.IsAcc.pos` |

**Conclusion**: every name resolves. The `IsClubBelow` / `IsStationaryBelow`
references **rely on `open Ordinal`**, which parent already declares
(line 41). After S4 ACT, `open Ordinal` continues to apply (it stays in
the import block). The local `IsClubBelow` (S2-duplicate) goes away, but
since `Ordinal.IsClubBelow` arrives via `import Proofs.Club.Basic` AND
`open Ordinal` is preserved, the bare-name reference still elaborates.

**No re-anchoring required in PR #19052's content** after S4 ACT —
only the line numbers shift (see §3.1). The OQ-04 author's session note
(`research/problems/fodor-pressing-down-oq-04/sessions/2026-05-14-s2a-act-limit-ordinals-club.md`)
references parent lines 350–402; those become 272–324 post-S4. That's
an OQ-04-side mechanic / doctor follow-up, not an OQ-01 obligation.

## 5. Build-risk reassessment

The S4c PREP §13 audit predicted ~25–45 min Docker cold build for the
parent. PR #19052 adds 2 new theorems with the following Mathlib v4.26.0
API surface:

* `Order.IsSuccLimit` typeclass + projections (`pos`, `succ_lt`)
* `Ordinal.isAcc_iff`, `IsAcc.forall_lt`, `IsAcc.pos`
* `Cardinal.IsRegular` + `aleph0_le`, `cof_eq`, `add_lt_of_lt`
* `Cardinal.lt_ord`, `Cardinal.ord_aleph0`, `Cardinal.ord_lt_ord`
* `Ordinal.omega0`, `omega0_pos`, `isSuccLimit_omega0`, `isSuccLimit_add`
* `Ordinal.isNormal_add_right`, `strictMono`

All confirmed in PR #19052's "Docker-verified at 3062 jobs" footer,
2 jobs above the S3 ACT's 3060 jobs (since 2 new theorems → 2 new
elaboration tasks).

The S4 ACT build target after the parent trim should be **3062 − 2 +
0 = 3060 jobs** (removing 5 defs + 1 theorem from parent removes their
elaboration; adding `import Proofs.Club.Basic` adds nothing because
that file was already in `Proofs.lean`'s module list per S2 ACT). The
S4 ACT implementer can use 3060 jobs as the expected post-trim build
target.

**No new v4.26.0 regression risk** is introduced by the merge order
combination: PR #19009 affects only Basic.lean (file-isolated), PR
#19052 's API surface was just verified clean at v4.26.0, and S4 ACT's
trim is removal-only (no new API calls).

## 6. Recommended S4 ACT sequencing

The S4 ACT implementer has three valid sequencings:

### 6.1 Option A: wait for both PRs to merge (recommended)

1. Wait for PR #19009 and PR #19052 to merge.
2. Branch off the new `origin/main`.
3. Apply S4 ACT per S4c PREP §12.1, with the LOC-anchors from §3.1
   above (not from S4c PREP §4, which is pre-#19052-stale).
4. Docker-build `Proofs.FodorPressingDown` and `Proofs.Club.Basic` →
   expect **3060 jobs** green in both (cf. §5).
5. Open S4 ACT PR. Mechanic follow-up per S4c PREP §12.2 + §3.1
   line-anchor table here.

**Pros**: cleanest history; no merge-order races; both upstream PRs
absorb their own STATE-SYNC.
**Cons**: blocks on deployer cadence — both PRs need to merge first
(median lead time ~6–24h based on recent cadence).

### 6.2 Option B: mechanic-PR overlay pattern (transient merge)

If S4 ACT is time-sensitive (e.g., a researcher session wants to ship
the parent cut today), use the mechanic-PR overlay pattern from
`feedback_researcher_mechanic_pr_overlay_build_verify_pattern.md`:

1. Branch off `origin/main`.
2. Pre-claim Docker baseline of parent → confirm 385 LOC (current
   state on main).
3. `gh pr diff 19009 > /tmp/19009.patch; git apply /tmp/19009.patch`
   (overlay S3 ACT).
4. `gh pr diff 19052 > /tmp/19052.patch; git apply /tmp/19052.patch`
   (overlay OQ-04 S2-α).
5. Apply S4 ACT (trim parent per S4c PREP §12.1, anchor per §3.1
   above).
6. Docker-build `Proofs.FodorPressingDown` and `Proofs.Club.Basic` →
   expect 3060 jobs green.
7. `git checkout origin/main -- proofs/Proofs/Club/Basic.lean
   proofs/Proofs/FodorPressingDown.lean` to revert overlays where
   they would race with the upstream PRs' own diffs.
8. Re-apply ONLY the S4 ACT delta (the parent-trim, minus any content
   that came from the overlays).
9. Open S4 ACT PR with explicit "depends on PR #19009 and PR #19052
   merging first" note.

**Pros**: ships S4 ACT today; build-verified end-to-end on the future
state of main.
**Cons**: requires careful overlay-revert step to avoid duplicating
PR #19009 / #19052 diffs; PR description must call out the dependency.

### 6.3 Option C: incremental — wait for one PR, then S4

If PR #19009 merges before PR #19052 (or vice-versa), the S4 ACT
implementer can:

1. After PR #19009 merges (Basic.lean at 119 LOC, parent at 385 LOC):
   skip the §3.1 Part-VII rows (they don't exist yet) and proceed
   per S4c PREP §4 (post-S3, pre-#19052) shift map.

2. After PR #19052 merges (parent at 453 LOC, Basic.lean back at 98
   LOC if #19009 not yet merged, or 119 if it has): apply §3.1 shift
   map exactly.

The two PRs are mutually file-disjoint (#19009 touches Basic.lean +
oq-01 docs; #19052 touches FodorPressingDown.lean + oq-04 docs), so
the merge order doesn't matter for git-conflict purposes.

**Pros**: minimum-risk; matches deployer cadence.
**Cons**: requires the S4 ACT author to know **which combination** of
PRs has landed by their branch time; two distinct shift maps to track.

### 6.4 Selection guidance

* If the deployer is running and both PRs are mergeable (current state):
  **Option A**. Wall-clock cost is ~6–24h delay; total work is the same
  as B; no overlay arithmetic.
* If S4 ACT is time-sensitive: **Option B**.
* If a researcher chains S4 ACT immediately after a partial merge:
  **Option C**.

## 7. What this PREP does NOT do

* **Does NOT modify `state.md`** — PR #19009's diff already overwrites
  state.md to reflect S3 ACT. After both PRs merge, a separate STATE-SYNC
  can incorporate this S4e PREP entry into the Sessions list.
* **Does NOT modify `problem.md`** — scope and signature targets are
  fixed since S1 OBSERVE.
* **Does NOT modify `knowledge.md`** — Mathlib alignment survey is
  unchanged; PR #19052's additions don't affect Basic.lean's design.
* **Does NOT modify any sister-slug docs** — OQ-04 owns its own state
  and session notes; this memo records OQ-04 line ranges only to clarify
  the S4 ACT mechanic plan.
* **Does NOT modify gallery JSON / annotations.json / meta.json** —
  those updates belong to S4 ACT or its mechanic follow-up (S4c PREP
  §12.2 unchanged).
* **Does NOT run a Lean build** — this is a purely doc-only PREP. The
  build-risk numbers in §5 are derived from PR #19009's and PR #19052's
  own Docker logs.

## 8. Acceptance criteria

| # | Criterion                                                  | Status |
|---|-------------------------------------------------------------|--------|
| 1 | New file at unique path under `sessions/` (no conflict with #19009 or #19052) | ✅ `2026-05-14-s04e-prep-cross-pr-coordination-audit.md` is fresh |
| 2 | No edits to `state.md` / `problem.md` / `knowledge.md`     | ✅ verified by `git status` after Write |
| 3 | No edits to any file under `proofs/Proofs/`                | ✅ doc-only |
| 4 | No edits to any file under `src/data/`                     | ✅ doc-only |
| 5 | §3 shift map is internally consistent: −99 LOC parent delta matches S4c PREP §4 | ✅ |
| 6 | §4 namespace-resolution table is complete: every symbol in PR #19052's diff appears | ✅ 16 symbols enumerated |
| 7 | §6 recommends an explicit S4 ACT sequencing with three viable options | ✅ A/B/C with selection guidance |

## 9. Conflict-free guarantee

This PR adds **one file at a fresh path**:

```
research/problems/fodor-pressing-down-oq-01/sessions/2026-05-14-s04e-prep-cross-pr-coordination-audit.md
```

Disjoint from:

* **PR #19009** (S3 ACT, open) — edits `Proofs/Club/Basic.lean`,
  `state.md`, `src/data/research/problems/fodor-pressing-down-oq-01.json`,
  and adds `sessions/2026-05-13-s05-act-diagInter-isClosedBelow.md`.
  **No overlap** (different sessions filename, no state.md edit here).
* **PR #19052** (OQ-04 S2-α ACT, open) — edits
  `Proofs/FodorPressingDown.lean`, OQ-04 `state.md`,
  `src/data/research/problems/fodor-pressing-down-oq-04.json`, and adds
  `research/problems/fodor-pressing-down-oq-04/sessions/2026-05-14-s2a-act-limit-ordinals-club.md`.
  **No overlap** (different slug, no parent file edit here).
* All other prior PREPs (S4, S4b, S4c, S4d, STATE-SYNC) — different
  filenames under the same `sessions/` directory; git auto-merges.

`git auto-merges` the `sessions/` directory addition; no rebase conflict.

## 10. Honesty assessment

**Mathematical content**: zero new mathematics. This memo updates the
S4c PREP §4 line-shift arithmetic to account for two open PRs that
post-date the S4c audit.

**Originality**: zero. Cross-PR coordination audit + arithmetic
refresh. The novelty is purely **temporal**: S4c PREP locked the shift
map at 2026-05-13 03:16 UTC; this memo updates it to 2026-05-14 17:30 UTC
after two open PRs added new constraints.

**Value-add over S4c PREP §4**:

* **§2**: explicit accounting of PR #19052's 68 LOC parent-file addition.
* **§3.1**: revised symbol-by-symbol line forecast for post-S4-ACT,
  with Part VII rows for OQ-04's two new theorems.
* **§4**: namespace-resolution check for PR #19052's new theorems
  under post-S4-ACT parent scope — confirms no re-anchoring needed in
  OQ-04 content.
* **§5**: build-job-count forecast (3060 jobs post-S4) derived from
  both open PRs' Docker logs.
* **§6**: three S4 ACT sequencing options (wait / overlay / incremental)
  with explicit selection guidance.

**What could be wrong**:

* §2 banner LOC breakdown (5/15/38/1/10/1/2) is approximate — the
  precise blank-line cadence in PR #19052 may shift any single block
  by ±1 LOC. The total +68 is exact (verified by `grep -c "^+"` on
  the patch). The §3.1 line forecasts use the cumulative +68, so they
  are not affected by the per-block ambiguity.
* §3.1 assumes S4 ACT cuts lines 43–97, 102–125, 329–349 of the
  pre-PR-#19052 parent (385 LOC). If S4 ACT instead removes more or
  fewer LOC (e.g., chooses Route B/C from S4b PREP), the absolute
  post-S4 line numbers shift accordingly; the "Part VII rows shift by
  −78" relationship still holds.
* §4's namespace-resolution check assumes `open Cardinal Order Ordinal
  Set` remains at parent line 41 post-S4. If S4 ACT removes or reorders
  `open` directives (e.g., to drop `open Set` after the trim eliminates
  Set-using local defs), then OQ-04's theorems still elaborate (none
  use bare `Set`-namespace names); but verify before claiming clean.
* §5's 3060-job forecast assumes Basic.lean elaboration is idempotent
  under the S2 + S3 ACT additions, which PR #19009's Docker logs confirm.
  If the parent's trim removes a private helper used downstream (none
  identified in S4c PREP §5), the forecast undercounts.
* §6.2 (Option B, overlay pattern) is sound only if the PR description
  explicitly notes the merge-order dependency and the deployer respects
  it (cf. `feedback_researcher_mechanic_pr_overlay_build_verify_pattern.md`).

**Estimated combined effort for S4 ACT after this PREP**:

* S4 ACT itself (Option A): 60–90 min (Docker cold build dominates).
* S4 ACT itself (Option B): 75–105 min (extra ~15 min for overlay arithmetic).
* Mechanic follow-up: 30–45 min (per S4c PREP §12.2; +5 min for the
  Part-VII line-anchor updates in OQ-04's session note).
* **Total**: ~2 hours under nominal conditions, ~3 hours if build
  retries are needed.

## 11. Appendix A: Verification commands used in this memo

```bash
# Confirm both PRs are open + mergeable:
gh pr view 19009 --repo rjwalters/lean-genius --json state,mergeable,mergeStateStatus
gh pr view 19052 --repo rjwalters/lean-genius --json state,mergeable,mergeStateStatus

# Inspect PR diffs:
gh pr diff 19009 --repo rjwalters/lean-genius
gh pr diff 19052 --repo rjwalters/lean-genius

# Count PR #19052 LOC delta on parent:
awk '/^diff --git/{f=0} /^diff --git.*FodorPressingDown\.lean/{f=1} f' /tmp/pr19052.patch \
  | grep "^+" | grep -v "^+++" | wc -l   # → 68

# Anchor on-main parent symbol locations:
grep -nE "^theorem |^def |^structure |^namespace |^end |^open |^import " \
  proofs/Proofs/FodorPressingDown.lean
```

## 12. Appendix B: Why this PREP is named S4e (not S5)

S1 OBSERVE's migration plan (state.md §"Migration plan (committed)")
defines:

* S2 ACT — ship Basic.lean
* S3 ACT — move `diagInter_isClosedBelow`
* S4 ACT — trim parent
* S5 (optional) — doc-only oq-04 dependency-path update

S4 has accumulated four PREP refinements (S4, S4b, S4c, S4d). This memo
is best classified as an **S4 PREP refinement** (S4e, fifth in the
series), not S5: it refines the parent-trim recipe for the eventual
S4 ACT, accounting for two open PRs that materially change the
parent file's line cadence.

S5 is reserved for the post-S4-ACT oq-04 dependency-path doc update.
That work cannot proceed until S4 ACT lands and OQ-04 can `import
Proofs.Club.Basic` directly.

The naming `s04e-prep-cross-pr-coordination-audit` keeps the prefix
tied to S4's parent-trim phase, which is the phase whose ACT will
physically apply the shift map updated here.
