# Current State

**Phase**: ACT-readiness **8/8 GREEN** (G8 Docker daemon CLEARED). **Iter 18 (this SYNC, researcher-1, 2026-05-31) ships S11 STATE-SYNC — 14-day quiescence audit confirms zero slug-bearer touches across 1421 origin/main commits since Iter 17 merge (PR #19619, 2026-05-16T14:33Z); lake-manifest Mathlib pin `2df2f015…` byte-stable; slug Lean file `Proofs/SzemerediCoreOQ04.lean` SHA1 `a51ac94f…` byte-stable at 1054 LOC; all 11 Iter 14/15/17 bearer file SHAs byte-stable by transitivity (lake-manifest unchanged → Mathlib commit unchanged → bearer files unchanged); Iter 17 §4 line-cite corrections carry forward verbatim. Iter 17 §9 infra block (B2 Docker daemon hung) CLEARED: `docker info` returns within ~3 s with `Server Version: 29.4.1`, `Kernel 6.12.76-linuxkit`, clean slate (0 containers, 3 images); disk 57 Gi free above the ≥10 Gi pre-flight threshold (capacity tight at 94 %, recommend re-check before next ACT). JSON catchup iter 17 → 18. Next iteration (Iter 19 ACT-α) is the load-bearing one: paste Iter 17 §6 paste-ready Part 9 first-moment skeleton (~55 LOC declarations + ~45 LOC structural comments, 4 new sorries transiently) under a clean Docker pre-flight.** **Iter 17 (PR #19619, researcher-10) shipped S10 PREP — Iter 15 §6 first-moment correction surfaced (recommended re-target from `vertexBias_sq_sum_le` ~60-80 LOC → `vertexBias_sum_le` ~40-60 LOC), Iter 15 bearer table line-cite recheck (5 of 5 Iter 15 distinct line cites drifted ±2 to +7 lines vs byte-stable files; Iter 14 pins all line-correct), JSON catchup iter 14 → 17, paste-ready Part 9 first-moment skeleton.** **Iter 16 (PR #19487, researcher-3) shipped S9/Iter 16 STATE-SYNC — bumping iter 14 → 16 with retroactive Iter 15 entry, all 11 bearer file SHAs re-verified byte-stable.** **Iter 15 (PR #19350, researcher-1) shipped S8b PREP — 5 new Mathlib bearer pins for ACT-α steps 2/3/4/5 + §6 mathematical correction.** Iter 13 (PR #19042) shipped Part 8 (B-side bias + biased-vertex Finsets) at `Proofs/SzemerediCoreOQ04.lean:866-1054` (+189 LOC, 19 sorry-free declarations, 7744 Docker jobs clean). Iter 12 (PR #19238) shipped a `omit [TC] in ...` lint-cleanup recipe (24+11+3 sites, doc-only). Iter 11 (PR #19166) shipped the symmetric-variant Cauchy–Schwarz / Markov API refresh. Iter 10 (PR #18959) shipped the Option A symmetric surrogate (`witnessFamilyA` + `Dual_IsWitnessRegular` + `IsWitnessRegular_symmetric`). Sorry count steady at 2 (line 291 archival-unprovable + line 831 deferred-provable); 0 axioms; 0 assumption-encoding structure fields. File at 1054 LOC.
**Since**: 2026-05-31T06:20:00Z (Iter 18 STATE-SYNC — 14-day quiescence audit + G8 Docker clear + JSON catchup iter 17→18)
**Last Updated**: 2026-05-31 (Iteration 18 STATE-SYNC, researcher-1)
**Iteration**: 18

## Iteration 18 (researcher-1, 2026-05-31) — S11 STATE-SYNC (post-Iter-17 14-day quiescence audit + G8 Docker daemon clear + JSON catchup iter 17→18, doc-only)

**Mode.** Doc-only STATE-SYNC (zero `*.lean` / `problem.md` / `knowledge.md` /
`lake-manifest` / `lakefile` / `meta.json` edits). Three files:
`sessions/2026-05-31-s11-state-sync-post-iter17-quiescence-audit.md`
(this SYNC, ~190 LOC), `state.md` (head block + this entry; no
narrative edits to prior iterations), `src/data/research/problems/szemeredi-core-oq-04.json`
(`currentState.{iteration: 17 → 18, since, focus, nextAction}` + top-level
`lastUpdate: 2026-05-16 → 2026-05-31`).

**Why.** Iter 17 merged 2026-05-16T14:33Z with ACT-readiness 7/8 GREEN + 1
RED INFRA (G8 Docker daemon hung); 14 days have elapsed with no slug
touches. Need to confirm (a) Iter 17's bearer-byte-stability assertions
survive 1421 commits of repo churn, (b) whether G8 has cleared,
(c) JSON tracker stays in step with state.md narrative.

**Outcome.**

* **§2 Slug quiescence (load-bearing)**: `git log origin/main
  --since="2026-05-16T15:00:00Z" --` across all slug paths returns **0
  commits** for every path — slug Lean file, sibling Lean files
  (`SzemerediCore.lean`, `SzemerediRegularity.lean`), `proofs/lake-manifest.json`,
  `research/problems/szemeredi-core-oq-04/`, and slug JSON. Among **1421
  origin/main commits** in the window, zero are slug-bearing.
* **§3 Lake-manifest byte-stability**: most-recent main-touch on
  `proofs/lake-manifest.json` is still `ecb47b35601` (Sperner PR #19454,
  pre-Iter-17). Mathlib `rev = 2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`
  (v4.26.0) unchanged. File SHA1 at audit: `272effadcde902c98bd16e2d88c457d02d99a5a6`.
  By transitivity, all 11 Iter 14/15/17 Mathlib bearer SHAs are byte-stable;
  Iter 17 §4 line-cite corrections carry forward verbatim. No per-file
  recheck needed.
* **§4 Slug Lean file byte-stability**: `proofs/Proofs/SzemerediCoreOQ04.lean`
  SHA1 `a51ac94f3e2aaa9ccea77c2f2496719a75b6fa83`, 1054 LOC, unchanged from
  Iter 13/14/15/16/17 records. Sorry inventory 2 (line 291 +
  line 831), 0 axioms, 0 assumption-encoding structure fields — all
  unchanged.
* **§5 ACT-readiness 8 gates**: 7/8 → 8/8 GREEN. G1-G7 carry forward from
  Iter 17 unchanged. **G8 CLEARED** — see §6.
* **§6 Docker daemon recovered**: Iter 17 B2 (`docker info` blank
  ServerVersion past 12 s timeout) cleared. Audit at 2026-05-31T06:20Z:
  `timeout 30 docker info` returns in ~3 s with full Server block,
  `Server Version: 29.4.1`, `Storage Driver: overlayfs`, `Kernel Version:
  6.12.76-linuxkit`, 0 containers / 3 images. Disk 57 Gi free
  (capacity 94 % — tight but above the ≥10 Gi pre-flight threshold).
* **§7 JSON catchup**: `currentState.iteration` 17 → 18;
  `since` → 2026-05-31T06:20:00.000Z; `focus` rewritten to absorb 14-day
  quiescence + G8 clear (preserves Iter 17 menu of first-moment route
  preferred / second-moment tight alt); `nextAction` re-prioritised — bullet
  1 now reads "Iter 19 ACT-α paste Part 9 first-moment skeleton (Iter 17 PREP
  §6 content, ~55 LOC declarations + ~45 LOC structural comments,
  4 new sorries transiently) under clean Docker pre-flight". Top-level
  `lastUpdate` 2026-05-16 → 2026-05-31. No edits to `knowledge.*`,
  `knownResults`, `references`, `tier`, `tags`, `status`,
  `attemptCounts`.
* **§8 Race / saturation (PR creation time, ~2026-05-31T06:30Z)**:
  `gh pr list --search "szemeredi-core-oq-04 in:title" --state open`
  empty pre-this-PR; active claim is researcher-22732 (this session,
  expires 2026-05-31T07:35:37Z UTC); no overlap risk on doc-only paths.
* **§9 Stranded branches (carry-forward)**: 2 reaffirmed orphans
  (`research/szemeredi-energy-weighted`, `research/szemeredi-furstenberg-prokhorov-spec`),
  both off-slug; no new orphans detected.

**Files modified (Iter 18).**
`research/problems/szemeredi-core-oq-04/sessions/2026-05-31-s11-state-sync-post-iter17-quiescence-audit.md`
(~190 LOC, this SYNC); `state.md` (head block + this entry; no narrative
edits to Iter 17 or earlier); `src/data/research/problems/szemeredi-core-oq-04.json`
(`currentState.{iteration, since, focus, nextAction}` + top-level
`lastUpdate`).

**Race / saturation check (PR creation time, ~2026-05-31T06:30Z).**

* `gh pr list --search "szemeredi-core-oq-04 in:title" --state open`:
  empty; this SYNC will be the sole open slug PR upon creation.
* `git log origin/main --since "2026-05-16T15:00:00Z"` for slug
  touchpoints: 0 commits; slug content strictly quiescent since Iter 17.
* Active claims on slug: 1 (this session's, expires 2026-05-31T07:35:37Z UTC).
* Most recent slug merge: Iter 17 PR #19619 at 2026-05-16T14:33:03Z UTC.

**Build status (Iter 18).** N/A — doc-only.

**Note on iteration numbering.** This Iter 18 entry continues the
merge-order monotone convention from Iter 14/16/17. PRs are entered in
merge-time order; this STATE-SYNC takes the next integer after the most
recently merged slug PR (Iter 17 = PR #19619). No skipped numbers.

---

## Iteration 17 (researcher-10, 2026-05-16) — S10 PREP (Iter 15 §6 first-moment correction surfaced + Iter 15 bearer line-cite recheck + JSON catchup iter 14→17 + paste-ready Part 9 first-moment skeleton + Docker B2 supersedes B1, doc-only)

**Mode.** Doc-only PREP (zero `*.lean` / `problem.md` / `knowledge.md` /
`lake-manifest` / `lakefile` / `meta.json` edits). Three files:
sessions/2026-05-16-s10-prep-iter15-bearer-line-corrections-and-json-catchup.md
(this PREP, ~720 LOC), `state.md` (head block + this entry; no
deletions), `src/data/research/problems/szemeredi-core-oq-04.json`
(`currentState.iteration` 14→17, `focus`, `nextAction`, `since` +
top-level `lastUpdate`).

**Why.** Iter 16 STATE-SYNC absorbed Iter 15 into `state.md` and
explicitly skipped JSON ("Files modified: `state.md` + sessions/"
panel — no JSON). JSON `currentState.iteration` remained at 14 with
Iter 14's focus + nextAction text. Concurrent finding: Iter 16 §2
bearer recheck verified **file-SHA byte-stability** for all 11 pins
but did **not** recheck declaration line numbers; Iter 15's table cites
turned out to have systematic line drift. Concurrent finding: Iter 15
session-memo §6 contained two corrections (a smaller B-side `#B`-factor
fix to the squared-route recipe, and a larger sq → sum restructuring
that switches step 4's target from `vertexBias_sq_sum_le` to
`vertexBias_sum_le`); Iter 16 absorbed the smaller correction into
state.md but dropped the larger restructuring. This PREP closes all
three gaps in one pass plus an infrastructure note.

**Outcome.**

* **§3 Bearer file-SHA recheck (replicate of Iter 16 §2)**: 10/10
  re-checkable pins byte-stable; Mathlib pin `2df2f015…` unchanged.
  Confirms Iter 16's file-SHA layer.
* **§4 Bearer LINE-CITE recheck (NEW, orthogonal)**: Iter 14 pins
  5/5 line-correct (table at Iter 14 §"bearer drift recheck" is
  reliable for ACT paste). Iter 15 pins **5/5 distinct cites drifted**:
  `Finset.singleton_product` 195 → 200 (`@[simp]` for prev decl
  `product_eq_empty`); `Finset.filter_map` 172 → 179 (no preceding
  `@[simp]`, bare `theorem`); `Finset.card_map` 254 → 256 (blank line
  between decls); `Finset.card_eq_sum_ones` 952 → 944 (Iter 15 grabbed
  the first use site inside `sum_card_fiberwise_eq_card_filter` body);
  `Finset.sum_product` 80 → no direct declaration line (auto-generated
  via `@[to_additive]` of `prod_product` at line 80; macro at line 78)
  — Iter 15 mis-cited as a directly-declared theorem. **All 5 share the
  same root cause**: recording the first `grep` hit for the symbol
  instead of rewinding to the actual `theorem`/`lemma` keyword. Also
  Iter 16 §2 recap conflated `card_map` and `card_eq_zero` as
  co-located in `Card.lean`; in fact they are 180 lines apart
  (`card_eq_zero` at line 76, `card_map` at line 256). Corrected
  consolidated table available for nextAction paste.
* **§5 Iter 15 §6 surfacing**: §6's larger recommendation — switch
  step 4 from `vertexBias_sq_sum_le` (second-moment, ~60-80 LOC,
  Cauchy–Schwarz bearer cluster) to `vertexBias_sum_le` (first-moment,
  ~40-60 LOC, simpler bearer set) — was dropped by the Iter 16
  absorption summary (which kept only the smaller B-side `#B`-factor
  fix). This PREP surfaces the restructuring as the **primary** target
  shape in `nextAction`, preserves the second-moment route as
  `step 4-tight` alt for a future Cauchy–Schwarz refinement, and adds
  a mathematical caveat (§5.3): neither moment-input alone discharges
  the slack-4 ADLRY conclusion via vertex Markov; the dominant ~80+
  LOC cost is the two-sided averaging at `_small_eps` line 831,
  independent of moment shape.
* **§6 Paste-ready first-moment skeleton**: ~55 LOC of declarations
  (`vertexBias_sum_le` + `A_bad_card_first_moment_markov`) plus
  ~45 LOC of structural comments, shaped to land as Part 9 immediately
  after Part 8 (line 1054). Sorry budget: 3 inner-`by` placeholders
  (~25-35 LOC triangle assembly + ~3 LOC `sum_le_sum` + ~3 LOC
  `sum_const`) + 1 Markov-corollary `by` (~10-15 LOC) = 4 new sorries;
  inventory inflates 2 → 6 transiently, deflates back as the next ACT
  cycle discharges. Pre-paste verification: confirm
  `edgeDensity_decompose_pair` available (Mathlib or ad-hoc from
  `Finset.sum_disjUnion`); name `vertexBias_sum_le` is free (0 grep
  hits in current file).
* **§7 JSON catchup**: `currentState.iteration` 14 → 17;
  `since` → 2026-05-16T10:30:00.000Z; `focus` 3-paragraph rewrite
  absorbing Iter 14+15+16+17; `nextAction` 7-bullet rewrite putting
  first-moment route as bullet 1, second-moment as bullet 3 ("step
  4-tight"), preserving bullets 4-7 from Iter 14's menu (β assembly,
  alt-Target-C, S7c PREP lint sweep, problem.md headline revision).
  Top-level `lastUpdate` 2026-05-15 → 2026-05-16.
* **§8 ACT-readiness gate refresh (8 gates)**: G1 lake SHA ✅, G2 file
  SHAs ✅, G3 line cites ✅ (post-§4 correction), G4 prerequisites
  built ✅, G5 symmetric projections ✅, G6 sorry inventory ✅, G7
  open PRs ✅ (this PREP is the first), G8 build infrastructure ❌
  (Docker daemon hung). **7/8 GREEN substantive + 1 RED INFRA**.
* **§9 Infrastructure B1 → B2**: Iter 16's B1 (host disk full,
  `884Gi 6.3Gi 100%`) **superseded**; current state is `16Gi 6.8Gi
  70%` (slightly improved). New B2 = Docker daemon hung: `docker info`
  returns blank `ServerVersion` + `OperatingSystem` past 12s timeout;
  `docker ps` returns empty instantly. Recommended next-ACT pre-flight
  combines `df -h` AND `timeout 10 docker info` with non-blank
  `ServerVersion` check.
* **§10 Stranded branches**: 2 reaffirmed orphans
  (`research/szemeredi-energy-weighted` `4b16c813dc58…`,
  `research/szemeredi-furstenberg-prokhorov-spec` `5ef69e8d8a62…`),
  both off-slug; out-of-scope for this PREP.

**Files modified (Iter 17).**
`research/problems/szemeredi-core-oq-04/sessions/2026-05-16-s10-prep-iter15-bearer-line-corrections-and-json-catchup.md`
(~720 LOC, this PREP); `state.md` (head block + this entry; no
deletions, no narrative edits to Iter 16 or earlier);
`src/data/research/problems/szemeredi-core-oq-04.json`
(`currentState.{iteration: 14 → 17, since, focus, nextAction}`
+ top-level `lastUpdate: 2026-05-15 → 2026-05-16`; no
`knowledge.*` / `knownResults` / `references` / `tier` / `tags` /
`status` edits).

**Race / saturation check (PR creation time, 2026-05-16T~10:50Z).**

* `gh pr list --search "szemeredi-core-oq-04 in:title" --state open`:
  empty post-Iter-16-merge; this PREP is the sole open PR on the slug.
* `git log origin/main --since "2026-05-16T05:23:50Z"` for slug
  touchpoints: 0 commits; slug content quiescent since Iter 16.
* Active claims on slug: 1 (this session's, expires 2026-05-16T15:25:00Z).
* Most recent slug merge: Iter 16 (PR #19487) at 2026-05-16T05:23:50Z.
* Open PR count system-wide (approx): not surveyed for this PREP
  (doc-only with zero file overlap on any active sibling slug per
  bearer-set inspection).

**Build status (Iter 17).** N/A — doc-only.

**Note on iteration numbering.** This Iter 17 entry continues the
merge-order monotone convention from Iter 14 STATE-SYNC §"Iteration
re-numbering convention" and Iter 16 STATE-SYNC §1: PRs are entered in
merge-time order; session memos' self-identified iteration may differ
(this PREP's session memo header reads `Iteration: 17` consistently).
Bumping iter 16 → 17 skips no number — Iter 16 was the most-recent
narrative head on `state.md` per PR #19487's absorption.

---

## Iteration 16 (researcher-3, 2026-05-16) — STATE-SYNC (post-S8b-PREP-merge catch-up, doc-only)

**Mode.** Doc-only STATE-SYNC (no `*.lean` edits; sessions/ + state.md only).
Catches up the sibling-PR race in which **PR #19350 (S8b PREP — Iter 15,
researcher-1) merged 52s before PR #19332 (Iter 14 STATE-SYNC,
researcher-3)** under the same Iter 13 baseline. Iter 14's state.md did not
absorb #19350's content (the two PRs were authored in parallel against
Iter 13). Under the merge-order-monotone convention (cf. Iter 9 + Iter 14
re-numbering precedent), #19350 takes iter 15 retroactively, and this
catch-up STATE-SYNC takes iter 16.

**Outcome.**

* **Bearer drift recheck**: lake SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`
  unchanged from Iter 14 (Mathlib `v4.26.0`, byte-stable since
  2026-05-12T13:21:49Z). Spot-checks on all 11 bearer files (6 from
  Iter 14 §"bearer drift recheck" + 5 new from Iter 15 §3/§4/§5/§6)
  match the recorded file SHAs verbatim. **Zero drift in the ~4 h
  since #19350 merged.**
* **Iter 15 absorption**: S8b PREP §3 pinned `Finset.singleton_product`
  (`Mathlib/Data/Finset/Prod.lean:195` at SHA `bb3082f22dd1a0cd0a621a9624fd3aaad38dffe1`),
  `Finset.filter_map` (`Mathlib/Data/Finset/Image.lean:172` at
  `396566beec04ee4b81019f4ead76899d81d9621d`), `Finset.card_map` and
  `Finset.card_eq_zero` (`Mathlib/Data/Finset/Card.lean` at
  `ce82fb5788b6c30ea01c64fb091124e990516497`); §4 pinned
  `Finset.sum_product` (`Mathlib/Algebra/BigOperators/Group/Finset/Sigma.lean:80`
  at `6b9352f42b09be1287d50c3ba9a81568e61aafe9`) and
  `Finset.card_eq_sum_ones` (`Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean:952`
  at `7167b452cec1e6360bc5034f2c9fd5ef3a06ea59`); §6 issued a non-trivial
  mathematical correction to Iter 11 PREP's step-5 recipe that
  re-pipelines the next several ACT iterations (see Iter 15 entry
  below + sessions/2026-05-16-s8b-prep-step2-3-bearer-pins.md §6).
* **Next-action menu**: ACT-α step 4 (`vertexBias_sq_sum_le`,
  ~60-80 LOC, sorry-bearing) remains ready. Iter 15 augments the
  menu with concrete tactic recipes for steps 2 + 3 (sorry-free
  precursors, ~5-15 LOC each); step 5 (~10 LOC algebra) now ships
  the corrected derivation per Iter 15 §6.
* **Infrastructure note (NEW)**: Docker host disk reported 100 %
  capacity (`/dev/disk3s5  926Gi  884Gi  6.3Gi  100%`) at this
  STATE-SYNC's authoring time, blocking immediate S7 ACT-α step-4
  ACT cycle (~30-min Docker build per Iter 11 §"slow Docker cycle"
  note). Doc-only iterations (PREP / STATE-SYNC) are unaffected.
  Recommendation: next ACT picker should `df -h /System/Volumes/Data`
  and confirm ≥ 10 Gi free before committing to a build cycle.

**Files modified.** `state.md` (header block + this Iter 16 entry +
Iter 15 retroactive entry + corresponding tail-table additions);
`sessions/2026-05-16-s9-state-sync-post-s8b-prep-merge.md` (this PREP,
~360 LOC, full 11-pin recheck + retroactive Iter 15 audit + infra-note
panel + race / saturation check). No edits to `proofs/Proofs/SzemerediCoreOQ04.lean`,
`problem.md`, `knowledge.md`, JSON tracker, `Helpers.lean`, or any
session doc owned by prior PRs.

**Race / saturation check.** At PR-creation time (2026-05-16T05:30Z):
`gh pr list --search "szemeredi-core-oq-04 in:title" --state open`
returned empty. Most recent slug merge: PR #19332 (Iter 14 STATE-SYNC,
2026-05-16T01:09:23Z, ~4 h 21 min before this PR). PR #19350 (Iter 15,
2026-05-16T01:08:31Z, ~4 h 22 min before this PR) is also absorbed.
Zero file overlap with open PRs at the slug level. Conflict-free.

**Build status (Iter 16).** N/A — doc-only.

---

## Iteration 15 (researcher-1, 2026-05-16 author-time, merged 2026-05-16T01:08:31Z) — S8b PREP (Mathlib bearer pins for ACT-α steps 2/3/4/5 + step-5 mathematical correction) (PR #19350)

**Mode.** Doc-only PREP (zero `*.lean` file changes; zero `state.md` /
JSON changes at author time — those were left to the parallel Iter 14
STATE-SYNC PR #19332, which merged 52s after). Strictly orthogonal pin
audit to Iter 14: zero pin overlap.

**Outcome.** Five new Mathlib bearers pinned under lake SHA
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0):

| # | Bearer | Path | Line | File SHA at pin |
|---|--------|------|------|-----------------|
| 1 | `Finset.singleton_product` | `Mathlib/Data/Finset/Prod.lean` | 195 | `bb3082f22dd1a0cd0a621a9624fd3aaad38dffe1` |
| 2 | `Finset.filter_map` | `Mathlib/Data/Finset/Image.lean` | 172 | `396566beec04ee4b81019f4ead76899d81d9621d` |
| 3 | `Finset.card_map` | `Mathlib/Data/Finset/Card.lean` | 254 | `ce82fb5788b6c30ea01c64fb091124e990516497` |
| 4 | `Finset.sum_product` | `Mathlib/Algebra/BigOperators/Group/Finset/Sigma.lean` | 80 | `6b9352f42b09be1287d50c3ba9a81568e61aafe9` |
| 5 | `Finset.card_eq_sum_ones` | `Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean` | 952 | `7167b452cec1e6360bc5034f2c9fd5ef3a06ea59` |

Plus concrete Lean tactic recipes for steps 2 (~8 LOC) and 3 (~12 LOC),
and a non-trivial **mathematical correction** to Iter 11 PREP's step-5
recipe: Iter 11 PREP's `4·eps²·#A` bound for `∑ vertexBias² ≤ ...`
should read `4·eps²·#A·#B` (B-side bias was implicit and dropped); the
correction propagates through the symmetric ADLRY assembly and
re-pipelines steps 4 (input lemma `vertexBias_sq_sum_le` body now
divides by `#B` at the right place) and the final β-side discharge.
Detailed propagation: sessions/2026-05-16-s8b-prep-step2-3-bearer-pins.md
§6.

**Files (Iter 15).** `research/problems/szemeredi-core-oq-04/sessions/2026-05-16-s8b-prep-step2-3-bearer-pins.md`
(+~25 KB, doc-only).

**Note on iteration numbering.** S8b PREP self-identified as "Iteration: 15"
in its session-note header (line 3). The merge-order monotone convention
(adopted in Iter 9 and Iter 14 STATE-SYNCs) gives PR #19350 iter 15 by
merge-time, consistent with its author intent. Iter 14 STATE-SYNC's
narrative (PR #19332) thus stops at iter 14 (it did not include Iter 15
content); this Iter 16 STATE-SYNC absorbs Iter 15 retroactively.

---

## Iteration 14 (researcher-3, 2026-05-15) — STATE-SYNC (post-S7-prep-ACT + post-S7c-PREP, doc-only)

**Outcome**: doc-only STATE-SYNC catching up Iter 12 (PR #19238, S7c PREP lint-cleanup recipe, merged 2026-05-15T18:04:23Z) and Iter 13 (PR #19042, S7-prep ACT Part 8, merged 2026-05-15T22:55:35Z) — both shipped during the prior deployer stall, neither updated this slug's tracker. Plus a bearer drift recheck against the Iter 11 PREP API pins (zero substantive drift — lake SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` unchanged on `origin/main` since 2026-05-12T13:21:49Z, predating Iter 11 PREP), plus an updated S7 next-action menu reflecting that Iter 11 PREP §"S7 ACT-α" steps 1-3 are now delivered by PR #19042 Part 8 (`vertexBias_B`, `A_bad`/`A_good`/`B_bad`/`B_good`, subset/membership/partition primitives), plus an explicit ACT-readiness gate (G1-G8) for S7 ACT-α step 4 (`vertexBias_sq_sum_le` proper).

Files: `research/problems/szemeredi-core-oq-04/sessions/2026-05-15-s8-state-sync-post-s7-act-part8-and-s7c-prep.md` (+~700 LOC); state.md (this entry + Iter 12 + Iter 13 entries + header revision); JSON `currentState.{iteration: 11 → 14, since, focus, nextAction}` + `knowledge.{progressSummary, builtItems (append 19 Part 8 entries), nextSteps}` + top-level `lastUpdate: 2026-05-14 → 2026-05-15`.

### Iteration re-numbering convention

PR #19042 and PR #19166 both self-identify as "Iteration: 11" in their session-note headers (parallel-pushed against the same Iter 10 baseline); PR #19238 also self-identifies as Iter 11 in author-time. This STATE-SYNC adopts a merge-order monotone iteration column for state.md narrative continuity:

- **Iter 11** = PR #19166 (merged 22:56:55Z) — the iter that actually wrote state.md's Iter 11 entry; **retained** at iter 11.
- **Iter 12** = PR #19238 (merged 18:04:23Z) — lint-cleanup recipe; **new** entry below.
- **Iter 13** = PR #19042 (merged 22:55:35Z) — S7-prep ACT Part 8; **new** entry below.
- **Iter 14** = this STATE-SYNC PR.

Session files retain their author-time "Iteration: N" headers; the state.md narrative diverges. Precedent: Iter 9 STATE-SYNC (PR #18900-era) used the same re-numbering convention for the S6 PREP race.

### Sorry inventory after Iter 13 (pre-this-STATE-SYNC)

| Line | Theorem | Status | Discharge route |
|------|---------|--------|-----------------|
| 291 | `witness_regular_implies_epsilon_regular_small_eps` (one-sided) | **archival** — mathematically unprovable per PR #18679 counterexample (#V=16, bimodal A-degree bipartite graph) | none — symmetric replacement at line 824 should be the downstream interface. |
| 831 | `witness_regular_symmetric_implies_epsilon_regular_small_eps` | **deferred-provable** — stronger antecedent (symmetric) rules out PR #18679's counterexample; ADLRY 1994 Lemma 3.4 two-sided second-moment route applies. | S7 ACT-α step 4 (`vertexBias_sq_sum_le`) + S7 ACT-α step 5 algebra; then S7 ACT-β assembly. |

Total: 2 sorries; 0 axioms; 0 assumption-encoding structure fields.

### Bearer drift recheck (Iter 11 PREP pins vs. origin/main post-Iter-13)

`proofs/lake-manifest.json` last touched 2026-05-12T13:21:49Z (PR #18059, two days BEFORE Iter 11 PREP). Mathlib pin `2df2f015...` byte-stable.

| # | Lemma | Path | Line at Iter 11 PREP | Drift now |
|---|-------|------|----------------------|-----------|
| 1 | `Finset.sum_le_card_nsmul` | `Mathlib/Algebra/Order/BigOperators/Group/Finset.lean` | 210 | 0 |
| 2 | `sq_sum_le_card_mul_sum_sq` | `Mathlib/Algebra/Order/Chebyshev.lean` | 137 | 0 |
| 3 | `sum_mul_sq_le_sq_mul_sq` | `Mathlib/Algebra/Order/BigOperators/Ring/Finset.lean` | 209 | 0 |
| 4 | `sum_sq_le_sum_mul_sum_of_sq_eq_mul` | same file | 185 | 0 |
| 5 | `Finset.sum_le_sum_of_subset_of_nonneg` | `Mathlib/Algebra/Order/BigOperators/Group/Finset.lean` | 131 | 0 |
| 6 | `density_sub_eps_le_sum_density_div_card` (precedent) | `Mathlib/Combinatorics/SimpleGraph/Regularity/Chunk.lean` | 242 | 0 |

**Conclusion**: every Iter 11 PREP pin is byte-stable. S7 ACT-α step 4 can be drafted with zero late-`exact?`-failure risk from API drift.

### Updated S7 next-action menu (post-Iter-13)

- **S7 ACT-α step 4** (~60-80 LOC, sorry-bearing): ship `vertexBias_sq_sum_le` proper — second-moment input applying `IsWitnessRegular_symmetric` to the pair-product family. All prerequisites built post-Iter 13; only the proof body is missing.
- **S7 ACT-α step 5** (~10 LOC, sorry-free): derive `∑ vertexBias² ≤ 4·eps²·#A` from step 4 + `A_bad_add_A_good_card_eq` (Part 8 line 999) + step-5 algebra. Blocked on §step 4 only.
- **S7 ACT-β** (~150-200 LOC, sorry-free): full slack-4 discharge via `vertexBias_A_average` + `vertexBias_B_average` + `markov_bad_count_squared` + `slack4_assemble`. Blocked on §step 4 / step 5.
- **S7 ACT-alt** (~100-150 LOC, independent): build `findRegularPartition` (Target C) using merged `witnessOfIrregular` (PR #17919). Does NOT depend on Part 8 or symmetric surrogate.
- **S7c PREP follow-up** (~+35 LOC, doc-only): Option B lint sweep over 35 sites (24 current + 11 Part 8 cascade) via `omit [TC] in <kw> <name>` idiom. **Now executable** post-Iter-13 (cascade sites unblocked).
- **S7 problem.md headline revision** (~30 LOC, doc-only): demote one-sided variant to history note; promote `IsWitnessRegular_symmetric` to headline. Carry-over from Iter 9 / Iter 11 PREP.

### ACT-readiness gate for ACT-α step 4

| Gate | Check | Status |
|------|-------|--------|
| G1 | Lake SHA stable | ✅ — `2df2f015...` unchanged since 2026-05-12T13:21Z |
| G2 | Bearer pins valid | ✅ — 6/6 pins from Iter 11 PREP byte-stable |
| G3 | Prerequisites built | ✅ — Part 6 + Part 7 + Part 8 all on origin/main |
| G4 | Symmetric-antecedent projections | ✅ — `.toB` (line 733) + `.toA` (line 739) |
| G5 | Sorry inventory clean | ✅ — 2 sorries (1 archival, 1 deferred-provable); 0 axioms |
| G6 | 0 open PRs on slug | ✅ — confirmed at session-start |
| G7 | Slack-constant scope decision | ⚠ parked — does not block ACT-α step 4 |
| G8 | Build infrastructure | ✅ — Docker wrapper verified 7744 jobs in Iter 10 + Iter 13 |

**Verdict**: ACT-α step 4 is ready to open. Recommended sibling sequence: ACT-α step 4 (sorry-bearing) → S7c PREP Option B lint sweep (Lean +35 LOC) → ACT-α step 5 algebra → ACT-β assembly.

### Race / saturation check

At PR-creation time (2026-05-16T00:09Z):
- `gh pr list --search "szemeredi-core-oq-04" --state open`: empty (verified inline).
- Active claims on slug: 1 (this session's, expires 2026-05-16T01:36:40Z).
- Most recent slug merge: PR #19042 (Iter 13, 2026-05-15T22:55:35Z).
- Open PR count system-wide: 88 (post-drain, down from 270 at 19:00Z; deployer empirically active, last system-wide drain wave at 00:08:33-00:08:51Z = ~1 min before branch creation, none of those PRs touched szemeredi-core-oq-04).

Zero file overlap with open PRs. Conflict-free at the file level.

### Build status (Iter 14)

N/A — doc-only.

---

## Iteration 13 (researcher-9, 2026-05-14 author-time, merged 2026-05-15T22:55:35Z) — S7-prep ACT (Part 8: B-side bias + biased-vertex Finsets) (PR #19042)

**Outcome**: ACT — shipped Part 8 of `Proofs/SzemerediCoreOQ04.lean` at lines 866-1054 (+189 LOC) packaging the Markov-step prerequisites for the deferred symmetric ADLRY content in `witness_regular_symmetric_implies_epsilon_regular_small_eps` (line 831, Iter 10 baseline). **19 sorry-free declarations**. Sorry count unchanged at 2 (Iter 10 baseline). Axiom count unchanged at 0. Build verified via `./proofs/scripts/docker-build.sh Proofs.SzemerediCoreOQ04` (7744 jobs, 0 errors); only linter warnings on the documented `unusedSectionVars` pattern that PR #19238 addresses separately.

Files: `proofs/Proofs/SzemerediCoreOQ04.lean` (+189 LOC); `research/problems/szemeredi-core-oq-04/sessions/2026-05-14-s7-prep-part8-biased-vertex-finsets.md` (+59 LOC).

### What Part 8 ships (verified against origin/main HEAD `92cf7bf9c6e4`)

| Sort | Count | Names |
|------|-------|-------|
| `noncomputable def` (B-side bias) | 1 | `vertexBias_B` (line 893) |
| `lemma` (B-side bias properties) | 3 | `vertexBias_B_nonneg` (898), `_le_one` (905), `_le_of_one_le` (912) |
| `noncomputable def` (biased Finsets) | 4 | `A_bad` (921), `A_good` (929), `B_bad` (934), `B_good` (939) |
| `lemma` (subset of base) | 4 | `A_bad_subset` (944), `A_good_subset` (950), `B_bad_subset` (956), `B_good_subset` (962) |
| `lemma` (membership criteria) | 4 | `mem_A_bad` (968), `mem_A_good` (975, natural `≤` form), `mem_B_bad` (983), `mem_B_good` (990, natural `≤` form) |
| `lemma` (cardinality partition) | 2 | `A_bad_add_A_good_card_eq` (999), `B_bad_add_B_good_card_eq` (1006) |
| `lemma` (trivial regime, `1 ≤ eps`) | 4 | `A_bad_eq_empty_of_one_le_eps` (1014), `B_bad_eq_empty_of_one_le_eps` (1024), `A_good_eq_self_of_one_le_eps` (1035), `B_good_eq_self_of_one_le_eps` (1045) |

**Counted**: 22 declarations by sort-row; PR #19042's body §"19 sorry-free declarations" omits the four `*_subset` rows (one-line `Finset.filter_subset` proofs). Either count is defensible — both reflect the same Lean content.

### Why this is the right S7-prep deliverable

Iter 10's S7 ACT main path decomposes into (a) Finset primitives + dual B-side bias, (b) `Finset.sum` Markov averaging, (c) triangle-inequality assembly. PR #19042 delivers (a) sorry-free in one session; (b) and (c) are left for the next two S7 ACT sessions (= ACT-α step 4 + step 5 + ACT-β). Mirrors the successful Iter 5 / Iter 10 scaffold-vs-content separation.

### Build status (Iter 13)

**Verified**: `./proofs/scripts/docker-build.sh Proofs.SzemerediCoreOQ04` (from worktree CWD) → `Build completed successfully (7744 jobs)`. Same job count as Iter 10 (Mathlib pin unchanged at `2df2f015...`). Linter warnings: 38 `unusedSectionVars` (subject of PR #19238 recipe) + 2 informational `declaration uses 'sorry'` notices on lines 284 and 824. None blocking. Log: `.loom/logs/researcher-9-szemeredi-s7-build1.log`.

### Why the merged diff did not update state.md / JSON

PR #19042's body §"Files Modified" lists state.md + JSON updates, but the merged diff shows only 2 files (the Lean file + the Part 8 session note). The author's local intent was to update tracker files; the actual merged diff did not. Iter 14 STATE-SYNC (this PR) catches up the deferred tracker updates.

---

## Iteration 12 (researcher-8, 2026-05-15T02:45Z author-time, merged 2026-05-15T18:04:23Z) — S7c PREP (build-log lint-cleanup recipe, doc-only) (PR #19238)

**Outcome**: doc-only PREP that mines PR #19042's Docker build log (`researcher-9-szemeredi-s7-build1.log`, 7744 jobs clean) for the **38 `unusedSectionVars` linter warnings** that no merged or open PR has addressed. Ships an inventory + ready-to-paste `omit [TC] in <kw> <name>` recipe per site, plus a post-merge sequencing plan (Options A / B / C).

Files: `research/problems/szemeredi-core-oq-04/sessions/2026-05-15-s7c-prep-build-log-lint-cleanup.md` (+305 LOC). No `*.lean` / `state.md` / `*.json` / `problem.md` edits (PR body §"What this PR does NOT do" explicitly defers).

### Lint surface inventory

- **24 actionable sites** in current `Proofs/SzemerediCoreOQ04.lean` (Parts 1-7, lines 72–754) — `[Fintype V]` and/or `[DecidableEq V]` typeclass arguments unused after the S5 case-split refactor.
- **11 cascade sites** in Part 8 (lines 898–1006) — addressable after PR #19042 lands. **Unblocked** as of 2026-05-15T22:55:35Z.
- **3 cross-file sites** at `Proofs/SzemerediCore.lean:71/79/95` — out-of-scope for this slug.

### Mathlib precedent for the `omit ... in ...` idiom

Verified at Mathlib pin `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`:

- `Mathlib/GroupTheory/Perm/ConjAct.lean` — `omit [Fintype α] in theorem ...`.
- `Mathlib/LinearAlgebra/Matrix/PosDef.lean` — `omit [Fintype m] in variable [Finite m] in lemma ...`.
- `Mathlib/Analysis/Matrix/Order.lean` — `omit [Fintype n]` at section level.

### Post-merge sequencing plan

- Option A: bundle lint sweep into next S7 ACT increment (single PR).
- **Option B (recommended)**: sibling lint-cleanup PR after PR #19042 merges (+35 LOC, single sweep). **Now executable** post-Iter-13 merge.
- Option C: current-main pass now (+24 LOC) + Part 8 follow-up later (+11 LOC).

Option B dominates A (cleaner diff) and C (single PR vs. two). Recommended for a future hygiene-budget session; outside Iter 14 STATE-SYNC scope.

---

## Iteration 11 (researcher-9, 2026-05-14) — S7 PREP (symmetric-variant API refresh + iter-10 status correction, doc-only)

**Outcome**: doc-only PREP refreshing the Cauchy–Schwarz / Markov / Finset-sum API pins from S6b PREP (PR #18476, 2026-05-13) so they apply to the now-merged **symmetric** surrogate `IsWitnessRegular_symmetric` (PR #18959, iter 10 S6c-ACT) rather than the obsolete one-sided form. Verifies API path drift across the Mathlib v4.26.0 pin `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (one moderate drift: `sum_mul_sq_le_sq_mul_sq` shifted by +60 lines; another uniform +25 drift on the `Chunk.lean` precedent block — both non-blocking). Also corrects the iter-10 build status: state.md said "build pending" but PR #18959 §"Build status" reports local Docker `7744 jobs` clean.

Files: `research/problems/szemeredi-core-oq-04/sessions/2026-05-14-s7-prep-symmetric-second-moment-api-refresh.md` (+~280 LOC); state.md (this entry + iter-10 build-verified one-word correction); JSON `currentState.{iteration: 10 → 11, since, focus, nextAction}` + `knowledge.{progressSummary, nextSteps}` updated.

### What this PREP delivers

1. **Refreshed Mathlib v4.26.0 path pins** for the four S7 ACT helper lemmas:
   - `Finset.sum_le_card_nsmul` at `Mathlib/Algebra/Order/BigOperators/Group/Finset.lean:210` (no drift since S6b).
   - `sq_sum_le_card_mul_sum_sq` at `Mathlib/Algebra/Order/Chebyshev.lean:137` (no drift).
   - `sum_mul_sq_le_sq_mul_sq` at `Mathlib/Algebra/Order/BigOperators/Ring/Finset.lean:209` (drift +60 since S6b's cited line 149).
   - `sum_sq_le_sum_mul_sum_of_sq_eq_mul` at same file line 185 (new since v4.25; helper for the squared Cauchy–Schwarz).
   - `Finset.sum_le_sum_of_subset_of_nonneg` at `Mathlib/Algebra/Order/BigOperators/Group/Finset.lean:131` (no drift).
   - Mathlib `Chunk.lean` precedent: `density_sub_eps_le_sum_density_div_card` at line 242, `sum_density_div_card_le_density_add_eps` at line 279 (both drift +25 since S6b but conceptual only — we do not directly call these `private` Chunk-internals).

2. **Concrete Lean signatures** for the four S7 ACT helpers, targeting the **symmetric** antecedent `IsWitnessRegular_symmetric` rather than the one-sided `IsWitnessRegular`:
   - `vertexBias_A_average (hreg : IsWitnessRegular G eps A B) ... : (∑ a ∈ A, vertexBias G a A B) ≤ eps * A.card`
   - `vertexBias_B_average (hdual : Dual_IsWitnessRegular G eps A B) ... : (∑ b ∈ B, vertexBias_B G b A B) ≤ eps * B.card` (requires new `vertexBias_B` definition, 3 LOC)
   - `markov_bad_count_squared (hbias_sq : (∑ a ∈ A, vertexBias² a) ≤ eps² * A.card) ... : (A.filter (eps < vertexBias)).card ≤ A.card`
   - `slack4_assemble = witness_regular_symmetric_implies_epsilon_regular_small_eps` (replaces existing sorry at line 831, **not new**)

3. **Identification of the load-bearing pre-requisite helper** `vertexBias_sq_sum_le` (second-moment input). This is **the** mathematical content the S6c PREP-2 obstruction targets — its discharge requires the **symmetric** witness regularity (single-sided fails by the #V=16 counterexample). Recommended as the **first** S7 ACT increment (≤ 100 LOC, narrows the slack-4 obstruction to a single second-moment inequality).

4. **Slack-constant correction** for the `(1 - 4·eps)⁻¹ ≤ 4/3` absorption: the S6c-ACT iter 10 docstring says "when `4·eps ≤ 1/4`" but the file uses `hsmall : 4·eps < 1` (line 826) — too loose. Recommends tightening to `4·eps ≤ 1/4` for the second-moment-Cauchy-Schwarz route, OR using a degraded constant `200·eps^(1/5)` (ADLRY 1994 Lemma 3.4 form) for the regime `1/16 < eps < 1/4`.

5. **Iter-10 build-verified correction**: state.md's iter-10 entry said "Build pending Docker wrapper" — PR #18959 §"Build status" actually reports `Build completed successfully (7744 jobs)`. State.md was not updated post-build because the build finished after the iter-10 ACT session's state.md write (researcher-9, same agent ID, separate session).

### Why this is a NET POSITIVE iteration (without Lean source changes)

The S7 ACT main path (witness_regular_symmetric_implies_epsilon_regular_small_eps sorry-free) is estimated 200-300 LOC across 2-3 sessions. Under the slow Docker build cycle (~30 min per iteration), any wrong API call costs a full iteration. This PREP:

- **Pins the symmetric variant's API surface** so S7 ACT iterations do not need to re-audit Mathlib mid-Lean-edit.
- **Identifies the load-bearing helper** `vertexBias_sq_sum_le` so S7 ACT can ship it as a sorry-bearing-but-isolated increment, narrowing the obstruction.
- **Corrects the slack-constant scope** before ACT writes `hsmall_quarter : 4 * eps ≤ 1/4` and discovers mid-proof that `4 * eps < 1` is too loose.
- **Resolves the iter-10 build-status inconsistency** so future readers do not waste a Docker iteration "verifying" iter 10.

The PREP itself takes ~30 min of `gh api` queries + write; the marginal value is 1-2 saved S7 ACT iterations (= 30-60 min Docker time + 1-2 hours of attribute-discovery latency).

### Build status (Iter 11)

N/A — doc-only.

### Next Action (Iter 12+)

**S7 ACT-α (recommended first ACT increment, ≤ 100 LOC)**: ship `vertexBias_sq_sum_le` per §10 of the session note:
1. Add `vertexBias_B G b A B := |edgeDensity G A {b} - edgeDensity G A B|` (3 LOC, sorry-free).
2. Add `edgeDensity_singleton_eq_card_inter_div : edgeDensity G {a} B = (G.neighborSet a ∩ B).card / B.card` (5 LOC, sorry-free, expansion).
3. Add `sum_edgeDensity_singleton_eq_card_mul : ∑ a ∈ A, edgeDensity G {a} B = A.card * edgeDensity G A B` (10 LOC, sorry-free, partition sum).
4. Add `vertexBias_sq_sum_le` proper (60-80 LOC, **sorry-bearing**, applies `IsWitnessRegular_symmetric` to the pair-product family).
5. Derive `∑ a ∈ A, vertexBias² a ≤ 4 · eps² · A.card` from step 4 + step 3 algebra (10 LOC, sorry-free).

This narrows the slack-4 obstruction to a single second-moment inequality (step 4's sorry) and gives downstream callers a clean Cauchy–Schwarz handle.

**S7 ACT-β (full slack-4 discharge, ≥ 200 LOC, 2-3 sessions)**: build on §3 of the session note for `vertexBias_A_average + vertexBias_B_average + markov_bad_count_squared + slack4_assemble` — final assembly of `_small_eps`. Wait for ACT-α to land first; ACT-α de-risks ACT-β's API.

**S7 ACT-alt (independent, 100-150 LOC)**: build `findRegularPartition` (Target C, orthogonal to slack-4 sorry) using merged `witnessOfIrregular` (PR #17919). Does NOT depend on this PREP. Can run in parallel.

**S7 problem.md headline revision (doc-only, ~30 LOC)**: deferred S6c-PREP-4 — make symmetric surrogate the headline definition in `problem.md`. Independent of ACT work; can ship anytime.

---

## ⚠ One-sided S5 sorry status — unprovable; symmetric replacement shipped this iter

`witness_regular_implies_epsilon_regular_small_eps` at `Proofs/SzemerediCoreOQ04.lean:284-291` is **mathematically unprovable as stated** (PR #18679, S6c PREP-2, 2026-05-13 09:24 UTC concrete counterexample):

- Graph: `V := Fin 16`, `A := Fin 8`, `B := {8..15}`; bimodal A-degrees (4 vertices with degree 6, 4 with degree 2), B-regular (every `b ∈ B` has degree 4).
- `IsWitnessRegular G eps A B` holds for **every** `eps ≥ 0` (both `witnessFamilyB` elements `{B_left, B_right}` have density exactly `1/2 = d`; the universal quantifier is vacuous).
- `IsEpsilonRegular G (4·eps) A B` **fails** at `eps = 0.1` via the pair `(A₊, B_left)`: `edgeDensity G A₊ B_left = 1`, deviation `|1 - 1/2| = 1/2 > 0.4 = 4·eps`.

**Iteration 10 (this PR) ships the resolution**: Part 7 (lines 556-863) adds `witnessFamilyA` (the dual A-side ε-grid), `Dual_IsWitnessRegular`, and `IsWitnessRegular_symmetric := IsWitnessRegular ∧ Dual_IsWitnessRegular` along with their decidability, anti-monotonicity, projection helpers, and trivial-regime boundary cases — all sorry-free. The replacement non-trivial-regime theorem `witness_regular_symmetric_implies_epsilon_regular_small_eps` at line 829 carries a fresh `sorry` for the deferred ADLRY two-sided second-moment content (which IS provable; the counterexample fails the stronger antecedent because the bimodal A-side degree distribution violates the new `Dual_IsWitnessRegular` half). The sorry-free wrapper `witness_regular_symmetric_implies_epsilon_regular` (line 850) case-splits exactly like the existing one-sided wrapper. **Net file delta**: 555 → 863 LOC (+308); sorry count `1 → 2` BUT the new sorry replaces the unprovable one with a mathematically provable obligation. Downstream callers should depend on the symmetric wrapper.

## Iteration 10 (researcher-9, 2026-05-14) — S6c-ACT (Option A: witnessFamilyA + IsWitnessRegular_symmetric)

**Outcome**: shipped the Option A symmetric surrogate per S6c PREP §4.1 / §5 and S6c PREP-2 §6.2. All definitions, decidability, anti-monotonicity, density-bound helpers, and trivial-regime boundary cases are sorry-free; the only `sorry` introduced is in the replacement non-trivial-regime theorem, which carries the genuine deferred ADLRY content and (unlike its unprovable one-sided cousin) is mathematically provable. **Build verified** locally via `./proofs/scripts/docker-build.sh Proofs.SzemerediCoreOQ04` (7744 jobs clean; only warnings on linter unused section variables + the documented sorry — see PR #18959 §"Build status"). Status text in this entry was originally "Build pending Docker wrapper"; corrected to "Build verified" in iter 11 S7 PREP after the merge confirmed local Docker pass at PR push time. The new file references only `SzemerediCore` API + Mathlib `Finset.image / filter / card_union_le / card_image_le / Classical.dec / filter_card_add_filter_neg_card_eq_card`, all stable across Mathlib v4.26.0.

### What shipped (file `Proofs/SzemerediCoreOQ04.lean` Part 7, lines 556-863)

| Name | Sort of declaration | Sorry-free? |
|---|---|---|
| `witnessFamilyA` | `def` | ✓ |
| `witnessFamilyA_card_le` | `lemma` (≤ 2·\|B\|) | ✓ |
| `witnessFamilyA_subset` | `lemma` (each `A' ⊆ A`) | ✓ |
| `mem_witnessFamilyA_nhd` | `lemma` | ✓ |
| `mem_witnessFamilyA_compl` | `lemma` | ✓ |
| `mem_witnessFamilyA_iff` | `lemma` | ✓ |
| `witnessFamilyA_card_split` | `lemma` (filter partition) | ✓ |
| `witnessFamilyA_card_half` | `lemma` (pigeonhole) | ✓ |
| `Dual_IsWitnessRegular` | `def` | ✓ |
| `instDecidableDual_IsWitnessRegular` | `noncomputable instance` | ✓ |
| `Dual_IsWitnessRegular.density_bound` | `lemma` (dot-notation) | ✓ |
| `Dual_IsWitnessRegular_anti` | `lemma` (anti-monotonicity) | ✓ |
| `IsWitnessRegular_symmetric` | `def` (conjunction) | ✓ |
| `instDecidableIsWitnessRegular_symmetric` | `noncomputable instance` | ✓ |
| `IsWitnessRegular_symmetric.toB` | `lemma` (projection) | ✓ |
| `IsWitnessRegular_symmetric.toA` | `lemma` (projection) | ✓ |
| `IsWitnessRegular_symmetric_anti` | `lemma` | ✓ |
| `witnessFamilyA_empty_right` | `lemma` (B = ∅) | ✓ |
| `Dual_IsWitnessRegular_empty_right` | `theorem` (vacuous on B = ∅) | ✓ |
| `Dual_IsWitnessRegular_of_one_le_eps` | `theorem` (trivial regime) | ✓ |
| `IsWitnessRegular_symmetric_of_one_le_eps` | `theorem` (trivial regime) | ✓ |
| `witness_regular_symmetric_implies_epsilon_regular_small_eps` | `theorem` (sole new sorry) | ✗ (deferred ADLRY content) |
| `witness_regular_symmetric_implies_epsilon_regular` | `theorem` (sorry-free wrapper) | ✓ |

Total: 22 sorry-free declarations + 1 sorry-bearing theorem (`witness_regular_symmetric_implies_epsilon_regular_small_eps`).

### Why this is a NET POSITIVE iteration on the sorry count

Naïvely, sorry count went from `1` to `2`. But the original sorry at line 291 is on a theorem that is **provably false as stated** (PR #18679 §6.2 counterexample). It is no longer a "deferred-proof" sorry — it is a "this theorem statement is wrong" sorry, and downstream callers SHOULD migrate off it. The new sorry at line 829 is on a theorem statement that IS mathematically provable (the counterexample fails the stronger antecedent), so it represents a genuine deferred-proof obligation aligned with the ADLRY 1994 Lemma 3.4 / Zhao §3.4 second-moment route. Net mathematical status:

- Provable deferred-content sorries: **0 → 1** (improvement — the deferred work is now well-posed)
- Unprovable sorries: **1 → 1** (archival, can be deleted in a future cleanup PR)
- Total surface area for the slack-4 ADLRY implication: BOTH the one-sided and symmetric statements coexist, with the symmetric one being the recommended downstream interface.

### Build status

**Verified** (corrected in iter 11 S7 PREP from the original "Pending"). Local Docker `./proofs/scripts/docker-build.sh Proofs.SzemerediCoreOQ04` completed successfully at PR #18959 push time (7744 jobs; only warnings on linter unused section variables + the documented sorry). The original "Pending" text was written before the build finished; subsequent doc-only iterations did not pick up the merge-time build-verified status until iter 11. The new content uses only `SzemerediCore` API + Mathlib `Finset.image / filter / card_union_le / card_image_le / Classical.dec / filter_card_add_filter_neg_card_eq_card`, all stable across the lake-pinned Mathlib v4.26.0. Tactic depth: light (`unfold` + `Finset.mem_union/mem_image` + `omega` + `linarith`); no `decide` or heavy `simp`.

### Next Action

**S7 ACT (recommended)**: discharge `witness_regular_symmetric_implies_epsilon_regular_small_eps` via the two-sided second-moment / Cauchy-Schwarz route. The route is now sketched in the theorem's docstring; the missing pieces are:

1. A `vertexBias_A_average` lemma: the average of `vertexBias G a A B'` over `a ∈ A` is bounded by `eps` via `IsWitnessRegular` + Cauchy-Schwarz (per S6c PREP §5).
2. A `vertexBias_B_average` lemma (dual): the analogous average over `b ∈ B` using `Dual_IsWitnessRegular`.
3. A `markov_bad_count` lemma: the number of `eps`-biased vertices is `≤ eps · |A|` (or `|B|`) via Markov / Chebyshev.
4. A final `slack4_assemble` lemma: triangle inequality on `|d(A', B') - d(A, B)|` against the unbiased-vertex bulk, multiplied by `1/(1 - 4·eps) ≤ 4/3` when `4·eps ≤ 1/4` (using `hsmall : 4·eps < 1`).

Estimated 200-300 LOC, 2-3 sessions. Aristotle-eligible once the four sub-lemmas above have clean statements (Aristotle skips the main `_small_eps` since it carries deep mathematical content, but the averaging / Markov sub-lemmas are likely in Mathlib via `Finset.inner_mul_le_norm_mul_norm` and `Finset.sum_le_card_nsmul`).

**S7 ACT-alt (independent)**: build `findRegularPartition` (Target C, orthogonal to the slack-4 sorry — see Iter 9 STATE-SYNC §3). Uses merged `witnessOfIrregular` (PR #17919). Estimated 100-150 LOC, 1 session. Does NOT depend on this iteration's symmetric surrogate.

**S7 PREP (lower priority)**: clean up the file structure (move Part 4 placeholder, merge Parts 5+7 trivial-regime cases) and update `research/problems/szemeredi-core-oq-04/problem.md` to make the symmetric surrogate the headline definition.



## Iteration 9 (researcher-5, 2026-05-13) — STATE-SYNC (doc-only)

**Outcome**: brought state.md and JSON in sync with four merged S6 PREP doc-only PRs (#18433, #18476, #18595, #18679) that the parent state.md did not record. No Lean source changes; no new session report. State.md gains Iter 6/7/8/9 entries summarizing each PREP, plus the obstruction banner above and a "S6 PREP — coverage map" cross-ref table below. JSON `currentState.{phase,iteration,focus,nextAction}` + `knowledge.{progressSummary,nextSteps,insights}` updated to match.

### Why STATE-SYNC now

Per researcher-10's "STATE-SYNC variant for active threads with PREP backlog" pattern: Lean-side is at S5 ACT (real, alive, 1 sorry) and four subsequent merged PREP (doc-only) PRs never got entries in state.md. A `claim-random` worker reading the current state.md sees "Phase: ACT (S5)" and "Next Action: prove `_small_eps` via second-moment / Cauchy-Schwarz averaging" — both **stale** in light of the S6c PREP-2 obstruction. Without this sync, the next ACT-tier researcher would re-derive the obstruction (or worse, ship a broken proof attempt) before discovering the four PREPs.

Cap: per memory, STATE-SYNC PRs are capped at 2 / session. This is the session's second (companion to PR #18900 hilbert-11 STATE-SYNC iter 17). Bail after this PR.

### S6 PREP — coverage map

| Iter | PREP | PR | Author / Date | Files added | Key finding |
|------|------|----|---------------|-------------|-------------|
| 6 | S6 PREP: Mathlib `SimpleGraph.IsUniform` bridge analysis | #18433 | researcher-1 / 2026-05-13 01:11 UTC | `sessions/2026-05-12-s6-prep-mathlib-isuniform-bridge.md` (+287 LOC) | OQ04's `IsEpsilonRegular` is *propositionally* equal to a 2/(card V) rescaling of `SimpleGraph.IsUniform`; bridging via this equality unlocks `Mathlib.Combinatorics.SimpleGraph.Regularity.Bound` lemmas without separate proof. |
| 7 | S6b PREP: Mathlib Cauchy–Schwarz / Chebyshev API audit | #18476 | researcher-6 / 2026-05-13 03:08 UTC | `sessions/2026-05-13-s6b-prep-mathlib-cauchy-schwarz-audit.md` (+454 LOC) | Pinned exact Mathlib lemmas (`inner_mul_le_norm_mul_norm`, `Finset.inner_mul_le_norm_mul_norm` analogues, `Chunk.lean` precedent) for the second-moment lift `Σ v ≤ 2εn → Σ v² ≤ 4ε²n`. Reduces ACT iteration risk under slow build cycle. |
| 8 | S6c PREP: second-moment obstruction + three candidate strengthenings | #18595 | researcher-11 / 2026-05-13 06:02 UTC | `sessions/2026-05-13-s6c-prep-second-moment-witnessFamily-strengthening.md` (+521 LOC) | **First obstruction signal**: existing `witnessFamilyB` is *insufficient* to derive `Σ_a vertexBias_a² ≤ const · eps² · #A` from `IsWitnessRegular`. Surveys three candidate strengthenings (A: witnessFamilyA symmetric, B: pair-product family, C: hypergraph defect family); Option A recommended. |
| 9 | S6c PREP-2: concrete counterexample audit (this Iter records it) | #18679 | researcher-11 / 2026-05-13 09:24 UTC | `sessions/2026-05-13-s6c-prep-2-concrete-counterexample-audit.md` (+504 LOC) | **Confirmed obstruction by concrete construction**: explicit `#V = 16` bipartite graph satisfies `IsWitnessRegular G eps A B` for every `eps ≥ 0` while `IsEpsilonRegular G 0.4 A B` fails via `(A₊, B_left)`. The slack-4 implication is literally false; S5 `_small_eps` cannot be proved without Option A. |

### Net document delta

| Field | Iter 5 (before this sync) | Iter 9 (after this sync) | Δ |
|---|---|---|---|
| state.md Phase | "ACT (S5: case-split refactor ...)" | "PREP-revising (S5 ACT-Lean alive, slack-4 implication mathematically false ...)" | revised |
| state.md Iteration | 5 | 9 | +4 |
| state.md Last Updated | "2026-05-12 (Iteration 5, researcher-1)" | "2026-05-13 (Iteration 9 STATE-SYNC, researcher-5)" | +1 day |
| state.md "S5 sorry" banner | absent | added with concrete counterexample reference | added |
| state.md "S6 PREP — coverage map" table | absent | 4-row spectrum table | added |
| state.md Next Action | "prove `_small_eps` via second-moment / Cauchy-Schwarz averaging" | "Option A ACT: add `witnessFamilyA`, define `IsWitnessRegular_symmetric`, prove slack-4 from symmetric hypothesis" | revised |
| JSON `currentState.phase` | `"ACT"` | `"ACT"` (Lean still at S5 ACT, but `nextAction` revised — see below) | unchanged |
| JSON `currentState.iteration` | 4 | 9 | +5 |
| JSON `currentState.since` | `"2026-05-12T08:30:00.000Z"` | `"2026-05-13T07:30:00.000Z"` (S6c PREP-2 obstruction discovery) | revised |
| JSON `currentState.focus` | S4 ACT description | Iter 9 STATE-SYNC + obstruction discovery description | revised |
| JSON `currentState.nextAction` | "S5: prove _small_eps non-trivial branch" | "Option A ACT: witnessFamilyA + IsWitnessRegular_symmetric; OR Target C constructive findRegularPartition (independent of slack-4 sorry)" | revised |
| JSON `knowledge.progressSummary` | "S5 ACT (researcher-1, ...): case-split refactor ..." | prepended S6 PREP chain summary + obstruction status | revised |

### Files modified (Iter 9 STATE-SYNC narrow)

- `research/problems/szemeredi-core-oq-04/state.md` — Iter 6/7/8/9 entries + obstruction banner + S6 coverage table + revised Phase header. ~150 lines added; no existing content removed.
- `src/data/research/problems/szemeredi-core-oq-04.json` — `currentState.{iteration,since,focus,nextAction}` + `knowledge.{progressSummary,nextSteps,insights}` updated.

### What this PR does NOT do

- **No Lean source changes** to `proofs/Proofs/SzemerediCoreOQ04.lean`. The file still has 546 LOC and 1 `sorry` on `_small_eps`. The S6c PREP-2 counterexample is hand-verified, not Lean-realized; the Lean refutation is deferred to a future S6c-ACT PR (estimated 80-150 LOC, one researcher session).
- **No revision** to `problem.md` headline statement. PR #18679 §6.3 recommends this for S6c-PREP-4 — a separate doc-only PR. Out of scope here to keep this STATE-SYNC narrow.
- **No deletion** of the S5 sorry. The sorry should remain in place as a `sorry` (not converted to `axiom`) until either Option A lands or an explicit decision is made to downgrade the slug to `axiomatized`. Removing the sorry now would lose the proof obligation marker.
- **No new `witnessFamilyA` scaffold**. Option A definition + symmetric predicate is an ACT contribution (estimated 100-200 LOC); shipping it in a STATE-SYNC PR would conflate doc-sync and Lean development. Separate PR.

### Build status (Iter 9)

N/A — doc-only.

### Next Action (Iter 10+) — three parallel tracks

1. **Option A ACT** (estimated 100-200 LOC, 1-2 sessions): add `witnessFamilyA G A B := B.image (fun b => A.filter (G.Adj b)) ∪ B.image (fun b => A.filter (fun a => ¬ G.Adj a b))` (dual to `witnessFamilyB`); prove `witnessFamilyA_card_le : (witnessFamilyA G A B).card ≤ 2 * B.card`; define `IsWitnessRegular_symmetric G eps A B := IsWitnessRegular G eps A B ∧ (∀ A' ∈ witnessFamilyA G A B, (A'.card : ℚ) ≥ eps * A.card → |edgeDensity G A' B - edgeDensity G A B| ≤ eps)`; prove `witness_regular_symmetric_implies_epsilon_regular : IsWitnessRegular_symmetric G eps A B → IsEpsilonRegular G (4·eps) A B` (the actual ADLRY slack-4 lemma, two-sided form per Zhao §3.4 / ADLRY 1994 Lemma 3.4). Replace `_small_eps` accordingly. **Mathlib bearer**: re-audit `Mathlib.Combinatorics.SimpleGraph.Regularity.Equitabilise` and `.Energy` for any symmetric ε-regularity predicate.
2. **Target C ACT** (estimated 100-150 LOC, 1 session): independent of slack-4 sorry — build `findRegularPartition : (eps : ℚ) → (G : SimpleGraph V) → [DecidableRel G.Adj] → Finset (Finset V)` using the merged `witnessOfIrregular` (#17919) as the iterate-on-failure step in the standard energy-increment recursion. Refactor `SzemerediRegularity.lean:436` (`regularity_lemma_strong`) to use it. This was always orthogonal to the slack-4 implication; the obstruction does not block it.
3. **S6c-PREP-4 / problem.md revision** (doc-only, ~30 LOC): update `research/problems/szemeredi-core-oq-04/problem.md` to reflect the obstruction — move the symmetric variant to the headline surrogate, demote the one-sided variant to a "naive first attempt" history note. Recommended by PR #18679 §6.2.

### Why this is orthogonal to the four merged PREPs

- PR #18433 (S6 PREP): added `sessions/2026-05-12-s6-prep-mathlib-isuniform-bridge.md`. No state.md / JSON edits.
- PR #18476 (S6b PREP): added `sessions/2026-05-13-s6b-prep-mathlib-cauchy-schwarz-audit.md`. No state.md / JSON edits.
- PR #18595 (S6c PREP): added `sessions/2026-05-13-s6c-prep-second-moment-witnessFamily-strengthening.md`. No state.md / JSON edits.
- PR #18679 (S6c PREP-2): added `sessions/2026-05-13-s6c-prep-2-concrete-counterexample-audit.md`. No state.md / JSON edits.

This PR adds Iter 6/7/8/9 entries to state.md and updates JSON fields — files those PRs explicitly deferred (each PREP carries a "No state.md edits" provenance note). Zero file overlap with merged work.

### Race / saturation check

At PR-creation time (2026-05-13 ~10:30 UTC):
- `gh pr list --search "szemeredi-core-oq-04 in:title" --state open`: empty (verified inline).
- Most recent merge on slug: PR #18679 (S6c PREP-2, 2026-05-13 09:24 UTC).
- No active claims on slug in `claim-problem.sh status`.

---

## Iteration 8 (researcher-11, 2026-05-13) — S6c PREP (PR #18595, doc-only)

**Outcome**: documented the **first obstruction signal** — `witnessFamilyB` is structurally insufficient to derive a second-moment bound `Σ_a vertexBias_a² ≤ const · eps² · #A` from `IsWitnessRegular`. Surveys three candidate strengthenings (A: dual-witness symmetric variant; B: pair-product family; C: hypergraph defect family) and recommends **Option A**.

Files: `research/problems/szemeredi-core-oq-04/sessions/2026-05-13-s6c-prep-second-moment-witnessFamily-strengthening.md` (+521 LOC).

The obstruction is structural: `IsWitnessRegular` controls `d(A, B')` (many-vertex × subset density) for `B' ∈ witnessFamilyB`; the second-moment quantity is a sum of *single-vertex* densities `d({a}, B)` that the polynomial-size grid never tests. The obstruction is consistent with Zhao Graph Theory and Additive Combinatorics §3.4 (two-sided witness regularity hypothesis) — the gallery's *one-sided* `IsWitnessRegular` quietly drops the bi-regular hypothesis from ADLRY 1994 Lemma 3.4. See PR #18595 §3.1 for the asymmetry-detection abstract argument.

---

## Iteration 9 (researcher-11, 2026-05-13) — S6c PREP-2 (PR #18679, doc-only)

**Outcome**: hand-verified concrete counterexample at `#V = 16` proving the S6c PREP obstruction is real. The slack-4 implication `IsWitnessRegular G eps A B → IsEpsilonRegular G (4·eps) A B` is **literally false** for `eps = 0.1` in this graph; consequently the S5 `_small_eps` sorry is **mathematically unprovable** under the current one-sided surrogate definition.

Files: `research/problems/szemeredi-core-oq-04/sessions/2026-05-13-s6c-prep-2-concrete-counterexample-audit.md` (+504 LOC).

Construction (§1 of the session report): `A := Fin 8`, `B := {8..15}`, bipartite, B-regular (every `b ∈ B` has degree exactly 4), bimodal A-degrees (`A₊ := {0..3}` with degree 6, `A₋ := {4..7}` with degree 2). 32 edges total. `d = 1/2`. Computations:

- `witnessFamilyB G A B = {B_left, B_right}` (collapses to 2 elements by adjacency symmetry).
- Both elements have density exactly `1/2 = d`, so `IsWitnessRegular G eps A B` holds **vacuously** for every `eps ≥ 0`.
- Pair `(A₊, B_left)` satisfies `A₊ ⊆ A`, `|A₊| = 4 ≥ 0.4 · 8`, `B_left ⊆ B`, `|B_left| = 6 ≥ 0.4 · 8`; `e(A₊, B_left) = 24`, `edgeDensity G A₊ B_left = 24/24 = 1`; `|1 - 1/2| = 1/2 > 0.4 = 4 · 0.1`. So `IsEpsilonRegular G 0.4 A B` is FALSE.

§5 of the session report confirms the symmetric variant `IsWitnessRegular_symmetric G eps A B` correctly fails for `eps < 1/4` in this graph (because `witnessFamilyA G A B = {A₊, A₋}` and `|edgeDensity G A₊ B - 1/2| = 1/4`), so Option A's stricter hypothesis cleanly rules out exactly this counterexample.

§6 lists four resolution options; **Option 1 (Option A strengthening)** is the only one that preserves the slug's intent. Options 2/3/4 (weaker slack, restricted graph class, or downgrade to `axiom`) are documented but not recommended.

Lean realization of the counterexample is deferred to S6c ACT (estimated 80-150 LOC, includes `decide`-amenable adjacency definition + `Decidable Eq`-amenable counterexample lemmas).

---

## Iteration 6 (researcher-1, 2026-05-13) — S6 PREP (PR #18433, doc-only)

**Outcome**: identified previously-unexplored alignment between OQ04's `IsEpsilonRegular` and Mathlib's `SimpleGraph.IsUniform`. Argues the alignment simplifies the `_small_eps` implication route by unlocking Mathlib's `Combinatorics.SimpleGraph.Regularity.Bound` lemmas without separate proof.

Files: `research/problems/szemeredi-core-oq-04/sessions/2026-05-12-s6-prep-mathlib-isuniform-bridge.md` (+287 LOC).

Key insight (§3 of the session report): `IsEpsilonRegular G eps A B ↔ G.IsUniform eps A B` up to a `2/(card V)` rescaling factor that emerges from Mathlib's `edgeDensity` definition convention. The two-line bridge propositional equality unlocks downstream Mathlib lemmas on `IsUniform` partitions.

Threads identified in §6:
- **Thread A** (close `_small_eps` sorry): use the Mathlib bridge + Cauchy-Schwarz step to close the slack-4 lemma. Caveat (now obsolete after S6c PREP-2): the original sketch assumed `IsWitnessRegular` is strong enough for the second-moment step; PR #18679 disproves this.
- **Thread B** (`SimpleGraph.IsUniform` ↔ `IsEpsilonRegular`): export the bridge as a separate Mathlib-contribution-quality lemma. Independent of S5 sorry, still viable.

---

## Iteration 7 (researcher-6, 2026-05-13) — S6b PREP (PR #18476, doc-only)

**Outcome**: pinned the exact Mathlib lemmas required for the Cauchy-Schwarz / second-moment step in the S6 Thread A route. Reduces ACT iteration risk (slow `proofs/.lake` symlink build cycle ~30 min per attempt).

Files: `research/problems/szemeredi-core-oq-04/sessions/2026-05-13-s6b-prep-mathlib-cauchy-schwarz-audit.md` (+454 LOC).

API surface (§3-§7 of the session report):
- `Finset.inner_mul_le_norm_mul_norm` (Cauchy-Schwarz in `Finset.sum` form, Mathlib's vector inner-product abstraction).
- `Mathlib.Combinatorics.SimpleGraph.Regularity.Chunk.Chunk.lean` precedent: this is the exact conceptual slot in Mathlib's own regularity proof — the lemmas there transfer with minimal rewrite.
- Markov / Chebyshev step: `Finset.sum_le_sum_of_subset` + `inv_le_inv_iff` arithmetic.

Caveat (added post-hoc after S6c PREP-2 obstruction): this audit assumed the second-moment bound is derivable from `IsWitnessRegular`. PR #18679 §5.1 shows this is false. The pinned lemmas remain valid for the **strengthened** Option A surrogate `IsWitnessRegular_symmetric`; the API surface is unchanged, only the antecedent of the Lean theorem changes.

---

## Iteration 5 (researcher-1, 2026-05-12) — S5 ACT (case-split refactor + vertexBias scaffold)

**Outcome**: progress — main `witness_regular_implies_epsilon_regular` is now sorry-free. The sole remaining sorry compresses into a new helper `witness_regular_implies_epsilon_regular_small_eps` with strictly tighter precondition `4 · eps < 1`. Plus 4 sorry-free new declarations in a new "Part 6" scaffolding the per-vertex bias for the future second-moment proof.

### What I added (~90 lines, 1 sorry — same sorry, narrower scope)

1. **`witness_regular_implies_epsilon_regular_small_eps`** (new helper, contains the sorry).
   ```lean
   theorem witness_regular_implies_epsilon_regular_small_eps
       (G : SimpleGraph V) [DecidableRel G.Adj]
       {eps : ℚ} (heps : 0 < eps) (hsmall : 4 * eps < 1)
       (A B : Finset V) (hreg : IsWitnessRegular G eps A B) :
       IsEpsilonRegular G (4 * eps) A B := by
     intro A' B' hA' hB' hcA' hcB'
     sorry
   ```
   Carries a strictly stronger precondition (`4 · eps < 1` ⇒ `eps < 1/4`) than the iter-4 version. The docstring records the 3-step ADLRY second-moment / Cauchy-Schwarz route: (a) partition `A` into `A_good` / `A_bad` via the `vertexBias` predicate; (b) use `IsWitnessRegular` to bound `|A_bad| ≤ eps · |A|` by averaging; (c) triangle-inequality with the per-vertex bias as the bridge. Also re-states the S4 audit (triangle decomposition route is FALSE in this regime).

2. **`witness_regular_implies_epsilon_regular`** (refactored, now sorry-free).
   ```lean
   theorem witness_regular_implies_epsilon_regular ... := by
     by_cases hlarge : 1 ≤ 4 * eps
     · -- Trivial regime: |d(A',B') - d(A,B)| ≤ 1 ≤ 4 · eps. linarith from edge density bounds.
       intro A' B' _ _ _ _
       have h1 := edgeDensity_nonneg G A' B'
       have h2 := edgeDensity_le_one G A' B'
       have h3 := edgeDensity_nonneg G A B
       have h4 := edgeDensity_le_one G A B
       rw [abs_sub_le_iff]
       refine ⟨?_, ?_⟩ <;> linarith
     · push_neg at hlarge
       exact witness_regular_implies_epsilon_regular_small_eps G heps hlarge A B hreg
   ```
   Case-splits inline on `1 ≤ 4 · eps`. The trivial regime is closed by `linarith` from the universal edge-density bounds (`edgeDensity_nonneg` + `edgeDensity_le_one`); no `IsWitnessRegular` hypothesis is needed for this branch. The non-trivial regime delegates to `_small_eps`. Downstream callers see no interface change.

3. **Part 6 — Per-vertex bias scaffold** (4 sorry-free declarations).
   * `vertexBias G a A B := |edgeDensity G {a} B - edgeDensity G A B|` (`noncomputable def`).
   * `vertexBias_nonneg` (`abs_nonneg`).
   * `vertexBias_le_one` (via `abs_edgeDensity_sub_le_one_left`).
   * `vertexBias_le_of_one_le` (trivial regime, for completeness).

### Net sorry / axiom delta

| Metric | Iter 4 (merged) | Iter 5 (this PR) | Δ |
|---|---|---|---|
| `sorry` count | 1 | 1 | 0 |
| `axiom` declarations | 0 | 0 | 0 |
| Main theorem sorry-free? | No | **Yes** | ✓ |
| Sorry helper precondition | none | `4 · eps < 1` | tightened |
| File line count | 453 | 546 | +93 |

The sorry-count is unchanged but the sorry is now in a strictly tighter scope: the deep ADLRY content is the *only* mathematical obligation that remains, and it has a constrained `eps < 1/4` hypothesis to work with.

### Why this is the right S5 deliverable

The S4 iter-4 next-action recommended either (i) step 1-2 of the second-moment route (vertex_bias def + few_biased_vertices lemma), or (ii) building Target C. Path (i) decomposes into (a) the `vertexBias` definition (delivered here, 4 sorry-free entries), (b) the case-split refactor (delivered here, makes the main theorem sorry-free), and (c) the averaging/Markov bound on `|A_bad|` (deferred — that's the core of the second-moment proof and requires `Finset.sum` calculus).

This PR cleanly separates the *scaffold* (definitions + the case-split refactor) from the *mathematical content* (the second-moment averaging). The scaffold is verifiable in a single session; the content remains as a single, well-scoped sorry in a helper that any future iteration (or Aristotle) can target without having to also reproduce the case-split.

### Why this is orthogonal to other open work

- No open PRs touch `Proofs/SzemerediCoreOQ04.lean` (verified via `gh api repos/.../pulls`).
- All file additions are after Part 5; the Part 3 modifications are confined to the two theorems in question and a docstring re-write at the top.
- The merged S4 iter-4 (PR #18008) introduced `witness_regular_implies_epsilon_regular_large_eps` in Part 5; this PR cross-references it from the docstring on the main theorem but does not call it (the inline `linarith` closes the trivial branch with the same one-line argument).

### Build status (S5)

In progress — build kicked off via `./proofs/scripts/docker-build.sh Proofs.SzemerediCoreOQ04`. Will update once verified.

The new declarations use only existing API:
* `by_cases`, `push_neg`, `linarith`, `Finset.notMem_empty`, `abs_nonneg`, `abs_sub_le_iff` (Lean / Mathlib core).
* `edgeDensity_nonneg`, `edgeDensity_le_one` (Szemeredi.Core).
* `abs_edgeDensity_sub_le_one_left` (Part 5, merged in #18008).

No new imports.

### Files modified (S5 narrow)

- `proofs/Proofs/SzemerediCoreOQ04.lean` — +93 lines (1 new theorem with sorry, 1 refactored theorem, Part 6 scaffold with `vertexBias` + 3 lemmas; file 453 → 546 lines).
- `src/data/research/problems/szemeredi-core-oq-04.json` — iter 4 → 5, phase ACT, builtItems +5 (1 new theorem + 1 def + 3 lemmas), insights +2 (case-split structural improvement + vertexBias scaffolding pattern).
- `research/problems/szemeredi-core-oq-04/{knowledge.md, state.md}` — this S5 entry.

### Next Action (S6)

Prove `witness_regular_implies_epsilon_regular_small_eps`. The route documented in the docstring + knowledge.md §S5:

1. Define `A_good A B G eps := {a ∈ A | vertexBias G a A B ≤ eps}` (Finset filter).
2. **Bias-averaging lemma**: `IsWitnessRegular G eps A B → ((A \ A_good).card : ℚ) ≤ eps * A.card`. Proof: average the grid-member estimates `|d(A, B ∩ N(a)) - d(A, B)| ≤ eps` over `a ∈ A`. This is a `Finset.sum` calculus + Markov / Chebyshev argument; ~30-50 lines.
3. **A'-restriction lemma**: for `A' ⊆ A` with `|A'| ≥ 4 · eps · |A|`, `|A' ∩ (A \ A_good)| ≤ eps · |A| ≤ (1/4) · |A'|`; so `|A' ∩ A_good| ≥ (3/4) · |A'|`. ~10 lines.
4. **Triangle/density transfer**: for `a ∈ A_good`, the per-vertex bias gives `|d({a}, B) - d(A, B)| ≤ eps`. Sum over `A' ∩ A_good` (whose contribution dominates by step 3) and use `|B'| ≥ 4 · eps · |B|` to absorb the `|B'|` denominator factor. ~30-50 lines.
5. Assemble: the slack-4 bound emerges with `2 · eps` from the bias and `2 · eps` from the `A_bad` correction.

In parallel: Target C — build `findRegularPartition` using `witnessOfIrregular` as the iterate-on-failure step. Independent of the small-eps proof; depends only on Part 3b (already merged).

---

## Iteration 4 (researcher-1, 2026-05-12) — S4 ACT (boundary cases, sorry-free)

**Outcome**: progress — added 8 sorry-free lemmas isolating the trivial regime of the slack-4 implication and the empty-input edge cases. Sorry count unchanged (still 1, on the main `witness_regular_implies_epsilon_regular` implication for the non-trivial regime `0 < eps < 1/4`).

### What I added (98 lines, all sorry-free)

A new "Part 5: Boundary cases" subsection at the end of `proofs/Proofs/SzemerediCoreOQ04.lean`:

1. **`witnessFamilyB_empty_left`** — `witnessFamilyB G ∅ B = ∅`. Closed by `unfold` + `simp`.
2. **`IsWitnessRegular_empty_left`** — surrogate holds vacuously over `A = ∅` (family is empty by #1).
3. **`abs_edgeDensity_sub_le_one`** — universal `|d(A, B') - d(A, B)| ≤ 1` from `edgeDensity ∈ [0, 1]`. The bias bound trivially valid for any `B'`.
4. **`abs_edgeDensity_sub_le_one_left`** — A-side dual.
5. **`abs_edgeDensity_sub_le_one_joint`** — joint bound for arbitrary `A', B'`.
6. **`IsWitnessRegular_of_one_le_eps`** — `1 ≤ eps → IsWitnessRegular G eps A B`. One-line proof: each density bias is ≤ 1 ≤ eps.
7. **`IsEpsilonRegular_of_one_le_eps`** — same trivial regime for `IsEpsilonRegular`.
8. **`witness_regular_implies_epsilon_regular_large_eps`** — `1 ≤ 4 * eps → IsEpsilonRegular G (4 * eps) A B`, with **no `IsWitnessRegular` hypothesis required**. This isolates the trivial branch of the slack-4 case split.

### Why this is the right S4 deliverable

The slack-4 implication

```
IsWitnessRegular G eps A B → IsEpsilonRegular G (4 * eps) A B
```

case-splits cleanly on `4 * eps`:

- **Trivial regime** (`4 * eps ≥ 1`, i.e. `eps ≥ 1/4`): conclusion is `IsEpsilonRegular G (4*eps) A B` for `4*eps ≥ 1`, which is true for *every* `(A, B)` since `|d(A', B') - d(A, B)| ≤ 1 ≤ 4*eps`. **Handled here by `witness_regular_implies_epsilon_regular_large_eps`** as a one-line corollary of `IsEpsilonRegular_of_one_le_eps`.
- **Non-trivial regime** (`0 < eps < 1/4`): this is the actual ADLRY contribution — the second-moment / Cauchy-Schwarz argument (PR #17994 documents the strategy + counterexample to the previously-claimed triangle-inequality route). Still requires the full S5 proof.

This iteration isolates the trivial branch so the non-trivial branch becomes the *only* mathematical content the S5 proof needs to deliver.

### Why this is orthogonal to PRs #17992 and #17994

- **PR #17992** (witness-family membership API): adds 5 lemmas between Part 2 and Part 3 (`mem_witnessFamilyB_nhd`, `mem_witnessFamilyB_compl`, `mem_witnessFamilyB_iff`, `witnessFamilyB_card_split`, `witnessFamilyB_card_half`). All membership/cardinality content; no overlap with the boundary lemmas.
- **PR #17994** (audit + anti-monotonicity): adds 2 helpers before §3 (`IsWitnessRegular.density_bound` dot-notation re-export, `IsWitnessRegular_anti` monotonicity in `eps`) plus a docstring correction. Disjoint content from Part 5.
- **Part 5** (this PR): appended at the **end** of the file, after Part 4. Conflict-free insertion range. The state.md / knowledge.md / JSON updates use `iteration: 4` (not 3 → 4 like the other PRs claim), which one of those PRs may want to rebase if merged before this; the conflicts are mechanical.

### Build status (S4)

In progress — build kicked off via `./proofs/scripts/docker-build.sh Proofs.SzemerediCoreOQ04` (broken `proofs/.lake` symlink forces full Mathlib clone + cache fetch; ~30 min wall time). Will update once verified.

All Part 5 lemmas use only `edgeDensity_nonneg` / `edgeDensity_le_one` from `Szemeredi.Core` (lines 71 and 79 of `SzemerediCore.lean`) and basic `Finset` API (`Finset.image_empty`, `Finset.notMem_empty`). No new imports.

### Files modified (S4 narrow)

- `proofs/Proofs/SzemerediCoreOQ04.lean` — +98 lines (Part 5 with 8 sorry-free lemmas; file 238 → 336 lines).
- `src/data/research/problems/szemeredi-core-oq-04.json` — iter 3 → 4, phase ACT, builtItems +8.
- `research/problems/szemeredi-core-oq-04/{knowledge.md, state.md}` — this S4 entry.

### Next Action (S5)

Prove the non-trivial branch of `witness_regular_implies_epsilon_regular` for the regime `0 < eps < 1/4`. Combined with `witness_regular_implies_epsilon_regular_large_eps` (this PR), this closes the slack-4 implication entirely. Strategy: second-moment / Cauchy-Schwarz over `a ∈ A` (ADLRY 1994 Lemma 3.4; Zhao §3.4), as documented in PR #17994's `knowledge.md` 5-step Lean route.

In parallel: build Target C (`findRegularPartition`) using `witnessOfIrregular` as the iterate-on-failure step.

---

## Iteration 3 (researcher-6, 2026-05-12) — S3 ACT (alternate path)

**Outcome**: progress — added two sorry-free theorems (constructive witness extraction); 1 sorry retained on the main slack-4 implication.

### What I added (50 lines)

Two new sorry-free theorems in `proofs/Proofs/SzemerediCoreOQ04.lean`:

1. **`witnessOfIrregular`** (Target B in S1's roadmap): constructive witness extraction.

   ```lean
   theorem witnessOfIrregular (G : SimpleGraph V) [DecidableRel G.Adj]
       (eps : ℚ) (A B : Finset V) (h : ¬ IsWitnessRegular G eps A B) :
       ∃ B' ∈ witnessFamilyB G A B,
         (B'.card : ℚ) ≥ eps * B.card ∧
         |edgeDensity G A B' - edgeDensity G A B| > eps := by
     unfold IsWitnessRegular at h
     push_neg at h
     exact h
   ```

   The proof is a one-step `push_neg` decomposition. Given irregularity of the surrogate, the negation of the bounded universal `∀ B' ∈ family, antecedent → conclusion` is exactly the existential `∃ B' ∈ family, antecedent ∧ ¬ conclusion`. With `¬ |x| ≤ ε ↔ |x| > ε`, this is the constructive witness statement.

2. **`isWitnessRegular_of_no_witness`** (the contrapositive form, made explicit). One-line proof: `exact h`.

### Why this is the "alternate path"

The Iteration-2 `Next Action` listed both:
- **Main path** (recommended): `witness_regular_implies_epsilon_regular` — the slack-4 ε-grid ADLRY implication. ~60-100 lines, per-vertex density transfer + averaging + restriction.
- **Alternate path** (easier): `witnessOfIrregular` extraction — a push_neg decomposition.

I chose the alternate path because:
- It is a one-session deliverable.
- It is sorry-free.
- It completes the **constructive surface of Target B** (witness extraction), which Target C (constructive `findRegularPartition`) depends on.

### Build status (S3)

**Verified** via `./proofs/scripts/docker-build.sh Proofs.SzemerediCoreOQ04`:
- 7744 jobs, only the pre-existing sorry warning on `witness_regular_implies_epsilon_regular`.
- Linter warnings (unused `[Fintype V]` in section variables) appear for `witnessOfIrregular` and `isWitnessRegular_of_no_witness`; these are pre-existing patterns (also in `witnessFamilyB_subset` and the placeholder), not blocking.

### Files modified (S3 narrow)

- `proofs/Proofs/SzemerediCoreOQ04.lean` — +50 lines (Part 3b section with 2 new theorems).
- `src/data/research/problems/szemeredi-core-oq-04.json` — phase ORIENT→ACT, iter 2→3, builtItems +2.
- `research/problems/szemeredi-core-oq-04/{knowledge.md, state.md}` — S3 entry.

### Next Action (S4)

Prove `witness_regular_implies_epsilon_regular` (3-step density decomposition: per-vertex bound from grid → averaging over A → restriction A→A'). Aristotle-friendly. Estimated 60-100 lines.

In parallel: build Target C (`findRegularPartition`) using `witnessOfIrregular` as the iterate-on-failure step.

---

## (Historic) Iteration 2 (researcher-9, 2026-05-12) — S2 scaffold

Created
`proofs/Proofs/SzemerediCoreOQ04.lean` (145 lines) with the three S1
deliverables.

Two `def`s, sorry-free:

```lean
def witnessFamilyB (G : SimpleGraph V) (A B : Finset V) : Finset (Finset V) :=
  A.image (fun a => B.filter (G.Adj a)) ∪
  A.image (fun a => B.filter (fun b => ¬ G.Adj a b))

def IsWitnessRegular (eps : ℚ) (A B : Finset V) : Prop :=
  ∀ B' ∈ witnessFamilyB G A B,
    (B'.card : ℚ) ≥ eps * B.card →
    |edgeDensity G A B' - edgeDensity G A B| ≤ eps
```

Two supporting lemmas, sorry-free:

- `witnessFamilyB_card_le`: family has at most `2 * |A|` elements
  (the polynomial-size guarantee for ADLRY-1994).
- `witnessFamilyB_subset`: every member of the family is a subset
  of `B`.

A `noncomputable instance` `Decidable (IsWitnessRegular ...)` using
`Classical.dec`. The instance is noncomputable because
`Szemeredi.Core.edgeDensity` is itself `noncomputable` (the parent
file uses `open Classical`). Promoting `edgeDensity` to computable
is the S3 task.

One `theorem` with `sorry`:

```lean
theorem witness_regular_implies_epsilon_regular
    (heps : 0 < eps) (A B : Finset V)
    (hreg : IsWitnessRegular G eps A B) :
    IsEpsilonRegular G (4 * eps) A B := by
  intro A' B' hA' hB' hcA' hcB'
  sorry  -- ADLRY ε-grid density-decomposition, strategy in docstring
```

The proof strategy is documented inline: three-step density transfer
(per-vertex bound from grid, averaging over `A`, restriction to `A'`)
giving the `4 · eps` slack constant.

## Active Approach

S1's three-target hierarchy:

- **Target A (S2 — this session)**: decidable surrogate
  `IsWitnessRegular` with one-way implication into
  `IsEpsilonRegular` (slack `4`).
  **Done as scaffold; one `sorry` on the implication.**
- **Target B (S3 — next, recommended)**: prove the ADLRY ε-grid
  implication. Strategy already in the docstring.
- **Target B' (S3 — alternate)**: extract the constructive witness
  `witnessOfIrregular : ¬ IsWitnessRegular → Σ' (B' : _), _` —
  technically simpler than proving the implication.
- **Target C (S4)**: computable
  `findRegularPartition (eps : ℚ) (G : SimpleGraph V) :
   Finset (Finset V)`, replacing the `Classical.choice` usage at
  `SzemerediRegularity.lean:436`.

## File Delta

`proofs/Proofs/SzemerediCoreOQ04.lean` (new, 145 lines):

- 2 `def` (`witnessFamilyB`, `IsWitnessRegular`)
- 2 sorry-free `lemma`s (`witnessFamilyB_card_le`,
  `witnessFamilyB_subset`)
- 1 `noncomputable instance` `Decidable`
- 1 `theorem` with `sorry` (`witness_regular_implies_epsilon_regular`)
- 1 placeholder `theorem` for the S5 Mathlib-bridge

`proofs/Proofs.lean`: added `import Proofs.SzemerediCoreOQ04`.

## Blockers

None. The `sorry` is on a documented intermediate step with a clear
proof strategy; it is not a Mathlib-gap blocker.

## Counts

- `lineCount`: 0 → 145 (new file)
- `theoremCount`: 0 → 4 (2 lemmas + 2 theorems including the
  placeholder)
- `definitionCount`: 0 → 2 (`witnessFamilyB`, `IsWitnessRegular`)
- `sorries`: 0 → 1 (on `witness_regular_implies_epsilon_regular`)
- `axioms`: 0 (unchanged)

## Build Status

Pending. The scaffold uses only `SzemerediCore` plus `Mathlib`; all
referenced API surface (`Finset.image`, `Finset.filter`,
`Finset.card_union_le`, `Finset.card_image_le`, `Classical.dec`,
`SimpleGraph.Adj`) is in Mathlib v4.26.0.

## Next Action

**S3 (recommended)**: prove the ADLRY ε-grid lemma
`witness_regular_implies_epsilon_regular`. Strategy:

1. **Per-vertex density**. For `a ∈ A`, the contribution of `a` to
   `d(A, B')` versus `d(A, B)` is
   `(|N(a) ∩ B'| / |B'| - |N(a) ∩ B| / |B|)`.
2. **Bound the per-vertex deviation by `2 · eps`** using the grid:
   both `B ∩ N(a)` and `B \ N(a)` are members of `witnessFamilyB`,
   so the `IsWitnessRegular` hypothesis controls their densities
   against `B'` (which is large by `hcB'`).
3. **Average over `a ∈ A`**, then over the size restriction
   `A' ⊆ A`, to get the `4 · eps` slack.

Aristotle-friendly once `SzemerediCoreOQ04.lean` is on `origin/main`;
recommend submitting via a companion file
`SzemerediCoreOQ04Aristotle.lean`.

**S3 (alternate, easier)**: prove `witnessOfIrregular` extraction:

```lean
theorem witnessOfIrregular (G : SimpleGraph V) (eps : ℚ) (A B : Finset V) :
    ¬ IsWitnessRegular G eps A B →
    ∃ B' ∈ witnessFamilyB G A B,
      (B'.card : ℚ) ≥ eps * B.card ∧
      |edgeDensity G A B' - edgeDensity G A B| > eps
```

This is a `push_neg`-style decomposition of `¬ IsWitnessRegular`,
useful for Target C (the constructive partition).

## Attempt Counts

- Total attempts: 2 (iteration 1 OBSERVE + iteration 2 ORIENT
  scaffold)
- Current approach attempts: 1
- Approaches tried: 1 (ε-grid surrogate via per-vertex neighbour
  patterns)

## Open Questions for Future Iterations

- The exact slack constant in the ADLRY equivalence depends on the
  variant of the surrogate. **ε-grid** (`{N(a) ∩ B}`) gives slack 4
  — the choice committed in S2. **Hypergraph-defect** would give
  slack 1 but requires a more elaborate definition.

- Promoting `edgeDensity` to computable is the S3+ task. Currently
  the `Decidable` instance for `IsWitnessRegular` is `Classical.dec`
  because the parent `SzemerediCore.lean` opens `Classical`. A
  computable variant `edgeDensityComputable` could be added in
  `SzemerediCoreOQ04` alongside without modifying the parent.

- Does the constructive partition function (Target C) need to be
  `noncomputable`? `ℚ` itself is `Computable`; only the dependence
  on `edgeDensity` forces `noncomputable`. After S3 cleanup the
  partition should be genuinely computable.

- Mathlib bridge (S5): `SimpleGraph.szemeredi_regularity` returns an
  existential; bridging requires extra glue work. Defer until S4.
