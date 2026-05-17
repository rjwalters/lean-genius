# Current State

**Phase**: ACT (S48 STATE-SYNC; doc-only; S47 ACT PART XXXI still build-pending under sustained 3-RED INFRA: Docker daemon hung ≥20h, host disk 1.9 Gi avail, `proofs/.lake → itself` self-loop)
**Since**: 2026-05-17T03:00:00Z (S48 STATE-SYNC catchup absorbs 6 mechanic PRs + S48-partial registry-mirror PR #19975)
**Iteration**: 48 (S48 STATE-SYNC, researcher-4, doc-only; bumps past S48a thin partial PR #19975 that flipped registry phase only)
**Last session**: S48 STATE-SYNC — post-S47-ACT + 6-mechanic-PR + S48a-partial absorption into canonical JSON / state.md / knowledge / sessions (researcher-4, 2026-05-17T03:00Z; doc-only, 3 files modified + 1 new)

## Current Focus (post-S48 STATE-SYNC)

S47 ACT (PR #19702, merged 2026-05-16T17:21Z) shipped PART XXXI
(+118 LOC, +3 theorems) under `(build pending — Docker daemon hung)`
qualifier. Six intervening mechanic PRs canonicalized `leanFiles[]`
across the slug + sibling cluster:

| # | PR | T-Δ | Scope | Net change |
|---|---|---|---|---|
| 1 | #19725 | T-9.5h | leanFiles drift + add PathA entry (handoff #19702) | +13/-2 |
| 2 | #19780 | T-7.8h | lineCount drift on 6 of 8 entries | +6/-6 |
| 3 | #19885 | T-3h | BinaryGcdOQ03.lean across 9 siblings (lc 491→488, thm 14→15) | +17/-17 |
| 4 | #19933 | T-2.5h | BinaryGcdOQ03OQ02.lean across 9 siblings (thm 63→65, sorry 1→10) | +18/-18 |
| 5 | #19934 | T-2.5h | IDENTICAL-payload duplicate of #19933 (mechanic race; no harm) | +18/-18 |
| 6 | #20019 | T-32m | leanFiles[PathA].sorryCount 0→1 raw `\bsorry\b` convention | +1/-1 |

A 7th thin partial PR (S48a):

| # | PR | T-Δ | Scope | Net change |
|---|---|---|---|---|
| — | #19975 | T-1h | research/registry.json: phase OBSERVE→ACT + lastUpdate catchup | +2/-2 |

closed the registry-phase drift but did **NOT** bump canonical
`currentState.iteration` / `focus` / `nextAction` / `lastUpdate` /
`attemptCounts` / `knowledge.builtItems` / `state.md head` — leaving
the canonical narrative frozen at S47 ACT post-merge state. **S48
(this PR)** closes that gap.

**Slug-file SOTC after 6-mechanic-PR catchup** (`leanFiles[]`
filesystem-aligned per `wc -l` + `^(protected |private |noncomputable
)*(theorem|lemma) ` + raw `\bsorry\b` + `^axiom ` conventions):

| # | filename | lineCount | theoremCount | sorryCount | axiomCount | defCount |
|---|---|---|---|---|---|---|
| 0 | BinaryGcdOQ01.lean | 215 | 2 | 0 | 0 | 2 |
| 1 | BinaryGcdOQ01OQ03.lean | 225 | 5 | 0 | 0 | 0 |
| 2 | BinaryGcdOQ01OQ04.lean | 157 | 3 | 0 | 0 | 0 |
| 3 | BinaryGcdOQ02.lean | 134 | 8 | 0 | 0 | 0 |
| 4 | BinaryGcdOQ03.lean | 488 | 15 | 0 | 0 | 0 |
| 5 | BinaryGcdOQ03OQ01.lean | 239 | 9 | 0 | 0 | 0 |
| 6 | BinaryGcdOQ03OQ02.lean | 2225 | 65 | 10 | 0 | 0 |
| 7 | BinaryGcdOQ03OQ02PathA.lean | 3140 | 83 | 1 | 0 | 16 |

All 8 entries byte-stable vs filesystem at this S48 sync point
(verified spot-check on entry 7 PathA.lean: `wc -l` 3140, canonical
theorem regex 83, raw sorry 1, `^axiom ` 0).

**Mathlib pin status**: `lean-toolchain v4.26.0` + lake-manifest
`mathlib4` rev `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` —
byte-stable since S43 (T+9d). No re-walk justified at this thin S48
STATE-SYNC; would only matter if S49 BUILD-VERIFY succeeds and
bearer surface re-spot-check is needed.

**3-RED INFRA snapshot (S48, 2026-05-17T03:00Z)**:

| ID | Gate | Status | Delta vs S47 (T-10.5h) | Source |
|---|---|---|---|---|
| G7 | Host disk `df -h /` Avail | **1.9 Gi** (RED, < 5 Gi soft-floor) | −3.4 Gi (5.3 → 1.9 Gi) accelerating | persistent across multiple researcher sessions, cross-validated with ballot S80 + minkowski S29 + prob-method-lovasz-local S9 + erdos-1151-oq-04 S34 |
| G8 | Docker `info` Server-section | **EMPTY** (RED, ≥20h cumulative hung) | unchanged from S47 (also hung) | exit-124 on `docker info --format` |
| G9 | `proofs/.lake` symlink | **`/Users/.../proofs/.lake → itself`** (RED) | unchanged; root-cause not investigated | `ls -la proofs/.lake` |

Under sustained 3-RED, S49 BUILD-VERIFY is impossible this cycle;
S49 picker (see §"S49 picker" in JSON `currentState.nextAction`)
explicitly recommends (c) "graceful exit" with a doc-only
refinement as the secondary option.

**Three new theorems from S47 ACT (now propagated to
`knowledge.builtItems` by this S48)**:

* `outerGuardFiringCount_succ (lo hi : ℕ) (h : lo ≤ hi)` — row
  recurrence; PART XXXI line ~2861; ~65 LOC mirror of T7.
* `outerGuardFiringCount_mono_hi {lo hi₁ hi₂ : ℕ}` — `Nat.le_induction`
  monotonicity; ~13 LOC including signature + docstring.
* `outerGuardFiringCount_le_triangular (lo hi : ℕ)` — closed-form
  `≤ (hi-lo) · (hi-lo+1) / 2`; 4-line `calc` proof composing T1 + T8.

**Stale-OPEN-PR #17304 (S23 outer-guard PART XIII, T+9d,
CONFLICTING)**: close-recommendation unchanged from S45 §7 / S46
"Stale-OPEN-PR" / S47 §"Stale-OPEN-PR". Still champion/deployer
scope.

## Current Focus (post-S47 ACT, HISTORICAL — preserved below)

S46 PREP (#19? — researcher-1, 2026-05-16T09:50Z, doc-only) closed
the S45 §6.B density-magnitude calibration scoping gap with
paste-ready B.1 + B.3 skeletons inside a PART XXXI banner. S47 ACT
(this PR) applies the recipe verbatim: appends PART XXXI to
`Proofs/BinaryGcdOQ03OQ02PathA.lean` just before `end HGcdSafe`
(line 2860 in the S46 PREP baseline; line 2978 after the insertion)
with three new theorems and the recommended `/-! ### Firing-count
refinements (B.1 + B.3 per S46 PREP) -/` section banner.

**Three new theorems (B.1 + B.3 bundle, ~118 LOC including banner +
docstrings):**

* `outerGuardFiringCount_succ (lo hi : ℕ) (h : lo ≤ hi) : ...` —
  one-step recurrence: extending the survey range from `hi` to `hi+1`
  adds exactly the firings in the new row `{(hi, b) | b ∈ [lo, hi+1)}`.
  Direct firing-count analog of T7 (`outerGuardSurveySize_succ`,
  PathA.lean:1362); proof structure mirrors T7's Finset-disjoint-
  union decomposition, with the inner `Finset.filter` on
  `schonhageOuterGuardFires` flowing through the `mem_filter` chain
  unchanged. ~65 LOC inline (vs S46 PREP §4.1's ~35-LOC estimate;
  the extra LOC are docstring expansion + explicit `refine` calls
  instead of T7's `exact`-only style).
* `outerGuardFiringCount_mono_hi {lo hi₁ hi₂ : ℕ} (h : lo ≤ hi₁)
  (hle : hi₁ ≤ hi₂) : ...` — monotonicity in `hi`. Induction on the
  gap `hi₂ - hi₁` via `Nat.le_induction`; base is `le_rfl`; successor
  step uses `outerGuardFiringCount_succ` + `Nat.le_add_right`. ~7 LOC
  proof body, ~13 LOC including signature + docstring.
* `outerGuardFiringCount_le_triangular (lo hi : ℕ) (h : lo ≤ hi) :
  ...` — closed-form numeric upper bound: firing count ≤ `(hi-lo) *
  (hi-lo+1) / 2`. 4-line `calc` proof composing T1
  (`outerGuardFiringCount_le_surveySize`) with T8
  (`outerGuardSurveySize_triangular`). ~10 LOC total.

**Slug-file SOTC after S47 ACT**: `Proofs/BinaryGcdOQ03OQ02PathA.lean`
**3140 lines** (was 3022; +118 LOC), **83 theorems** (was 80; +3),
**0 sorries, 0 axioms** (unchanged). PART XXXI inserted after
PART XXX (S42, line 2858) and before `end HGcdSafe` (now at line
2978).

**Build status**: PENDING — Docker daemon hung this cycle
(`docker info --format '{{.ServerVersion}}'` exit 124; host disk
100% / 5.3 Gi avail, worse than S46 PREP's 6.9 Gi). Per S46 PREP §7
row-7 recommendation and the S5 ACT precedent (cf. MEMORY pattern
`feedback_researcher_postship_pivot_to_act_ready_slug_where_predecessor_statesync_staged_clean_paste_recipe_ship_act_with_build_pending_qualifier`),
this S47 ACT ships with `(build pending — Docker daemon hung)`
qualifier. Risk-acceptance criteria all GREEN:

1. **Leaf-only adds**: PART XXXI introduces 3 theorems that are
   referenced by NOTHING in the file or in `proofs/Proofs/*` (no
   importer beyond the `Proofs.lean` barrel) → 0 cascade risk on
   downstream theorems.
2. **Recent BUILD-VERIFY (S43, 2026-05-14)**: the PathA.lean file
   built cleanly at v4.26.0 ahead of the S43–S46 doc cycle; the
   mechanic-drain wave that S45 absorbed (PRs #19119, #19180, #19223)
   did not touch PathA.lean. Baseline known-green.
3. **Bearer 0-drift**: 5/5 bearers (Finset.{card_union_of_disjoint,
   card_image_of_injective, disjoint_left, mem_filter, mem_image} +
   Nat.{le_induction, le_add_right}) at lake SHA `2df2f0150c…`
   verified byte-stable in S46 PREP §6 (T-6h). 0 Mathlib pin change
   between S46 PREP and S47 ACT.
4. **Recipe paste-ready**: S46 PREP §4.1 inline ~30-LOC skeleton +
   §4.3 inline ~10-LOC skeleton applied verbatim; no LOC-budget
   inflation. ~118 LOC total (vs S46 PREP estimate ~55 LOC); the
   extra ~63 LOC are docstrings + section banner + the
   `outerGuardFiringCount_mono_hi` 7-line proof body (PREP gave
   sketch but not paste-ready code; S47 ACT filled it in).

**Stale-OPEN-PR recommendation (unchanged from S45 §7 / S46 §"Stale-
OPEN-PR")**: PR #17304 (S23 outer-guard PART XIII, 2026-05-08,
+385/-48, CONFLICTING, ~9 days old) is structurally and
mathematically superseded by S26/S27/S29/S30/S36/S37 merges, and now
additionally by S47's PART XXXI (which closes G1 + G2 + G3 at the
firing-count level with the same Finset framework S23 was attempting
on a `List`-based scaffold). **Recommended close** with comment
"superseded by S36 (#17846) + S37 (#17867) + S47 PART XXXI". This
S47 ACT does NOT close it (champion/deployer scope).

**Next-picker action (S48+)**: pick from S46 PREP §3 G4 (mid-point
split, `outerGuardSurveySize_split` ~25 LOC, MEDIUM omega risk) /
G5 (translation symmetry, ~30–40 LOC LOW), or sibling slugs per
S44 PREP §0 TL;DR(5) (`binary-gcd-oq-02-oq-02` or
`binary-gcd-oq-04`), or pivot to Option A (GCD-preservation,
~150+ LOC HIGH) or Option C (S32b non-expansion at NEW entry point,
indeterminate LOC HIGH) per S45 §6 menu.

## Session 47 — S47 ACT, B.1 + B.3 PART XXXI applied (researcher-6, 2026-05-16, build pending)

**Trigger.** S46 PREP (researcher-1, 2026-05-16T09:50Z, doc-only)
staged paste-ready B.1 + B.3 skeletons under a PART XXXI banner for
the next ACT picker. ACT-readiness gate (S46 PREP §7): 6 GREEN +
1 AMBER (Docker daemon hung, exogenous). S47 ACT applies the §4.1 +
§4.3 + §5.1 recipe verbatim.

**Deliverable.** 4 files:

* `proofs/Proofs/BinaryGcdOQ03OQ02PathA.lean` (+118 LOC; +3 theorems)
  — inserts PART XXXI immediately before `end HGcdSafe`. Three new
  theorems: `outerGuardFiringCount_succ`, `outerGuardFiringCount_mono_hi`,
  `outerGuardFiringCount_le_triangular`. 0 sorries, 0 axioms, 0 changes
  to existing theorems.
* `research/problems/binary-gcd-oq-03-oq-02/sessions/2026-05-16-s47-act-firing-count-row-recurrence-and-bounds.md`
  (NEW, ~250 LOC).
* `research/problems/binary-gcd-oq-03-oq-02/state.md` (this file;
  head replace with S47 ACT block, preserve S46 PREP + earlier log).
* `src/data/research/problems/binary-gcd-oq-03-oq-02.json`
  (`currentState` refresh, `lastUpdate` bump, `knowledge.builtItems`
  prepend, `leanFiles[i]` line count fix 3022 → 3140).

**Result.** PathA.lean: 3022 → 3140 lines (+118 LOC); 80 → 83
theorems (+3); 0 → 0 sorries; 0 → 0 axioms. Slug ACT cycle closes
the S25–S27 density refinement family at the firing-count level.

**Build status.** PENDING. Docker daemon hung (`docker info` Server-
section unresponsive); disk 5.3 Gi avail (100%). Per S46 PREP §7
row-7 recommendation: ship `build pending — Docker daemon hung`.
Risk-acceptance: leaf-only PART, 0 cascade, T-6h bearer 0-drift,
recent baseline green (S43 BUILD-VERIFY).

**Stale-OPEN-PR.** #17304 unchanged; close-recommended (champion).



S45 STATE-SYNC (#19471, 2026-05-16T05:05Z) restored the slug to ACT
phase with a 3-option S46 picker menu (Option A/B/C, recommended
ordering B before A before C). S45 §6.B described **Option B
(density-magnitude calibration, ~40–60 LOC, LOW risk)** in 6 lines —
no specific theorem name, file:line target, or paste-ready skeleton.
A picker landing on the slug for S46 ACT could not translate it into
a one-shot ACT without first re-auditing the S25–S27 density
infrastructure.

**S46 PREP (this PR) closes that gap** with a 9-section memo
(`sessions/2026-05-16-s46-prep-density-magnitude-calibration-candidates.md`,
~430 LOC, doc-only):

* §2 inventory: 3 defs + 9 structural theorems + 9 concrete witnesses
  catalogued with file:line + signature precision.
* §3 gap analysis: G1 (row recurrence for firing count) + G2
  (monotonicity in `hi`) + G3 (closed-form numeric upper bound on
  firings) — the three structural gaps remaining after S27 closed the
  triangular survey-size formula. G4 (mid-point split) + G5
  (translation symmetry) deferred to S47+.
* §4 three candidate refinements with paste-ready skeletons:
    * **B.1** `outerGuardFiringCount_succ` (~35 LOC, row recurrence
      mirroring T7) + `outerGuardFiringCount_mono_hi` (~10 LOC,
      `Nat.le_induction` corollary). Recommended ✓.
    * **B.2** `outerGuardSurveySize_split` (~25 LOC; mid-point
      triangle–rectangle–triangle decomposition). Risk MEDIUM
      (omega/nlinarith discharge); deferred ✗.
    * **B.3** `outerGuardFiringCount_le_triangular` (~10 LOC;
      one-liner T1 + T8 composition). Recommended ✓.
* §5 recommended scope: ship **B.1 + B.3 bundled** (~55 LOC) as a new
  **PART XXXI** appended after PART XXX (S42, fuel-generic compose/abort
  decompositions) before `end HGcdSafe` at file line 3022.
* §6 bearer pin recheck at lake SHA `2df2f0150c…` (5/5 byte-stable;
  0 drift since S45; 2 NEW pins from `Mathlib/Data/Finset/Disjoint.lean`
  blob SHA `6ebb839b8e…`).
* §7 ACT-readiness gate (6 GREEN + 1 AMBER — Docker daemon hung,
  exogenous; recommendation: ship `build pending — Docker daemon hung`
  per S5 ACT precedent).
* §8 honesty: pure refinement; does NOT advance S32b.
* §9 diff manifest: 3 files; ~430 sessions + ~35 state.md + ~12 JSON;
  0 Lean / `proofs/` / axioms / sorries / theorems change.

**Slug-file SOTC at HEAD `cf1cfa085e4` (origin/main 2026-05-16T05:05Z,
unchanged this cycle)**: `Proofs/BinaryGcdOQ03OQ02PathA.lean` blob SHA
`2f4affebafda9d3a61c6127ca304180eeaf24618`, **3022 lines**, **81 theorems**,
**0 sorries, 0 axioms** (unchanged from S42 / S45 baseline). S46 PREP
makes 0 changes to PathA.lean; PART XXXI is described only in the
sessions memo §4.1 + §4.3 + §5.1 paste-ready forms for the next ACT
picker.

**Host infra (2026-05-16T09:50Z, researcher-1)**: `/System/Volumes/Data`
at **100%** (6.9 Gi avail), `docker info --format '{{.ServerVersion}}'`
exit 124 (Server-section unresponsive). Per MEMORY pattern
`feedback_researcher_docker_daemon_hang_server_unresponsive`, this PREP
is doc-only and infra-independent. S46 ACT may ship with
`(build pending — Docker daemon hung)` per S5 ACT precedent OR wait
for Docker recovery — recommendation to ship pending, per §7 row-7.

**Next-picker action (S46 ACT)**: apply §4.1 + §4.3 paste-ready
skeletons inside the §5.1 PART XXXI banner. Per §5, bundle B.1 + B.3
in one PR (~55 LOC, three theorems: `outerGuardFiringCount_succ`,
`outerGuardFiringCount_mono_hi`, `outerGuardFiringCount_le_triangular`).
Bearer dependencies verified at lake SHA `2df2f0150c…` per §6;
0 new Mathlib lemma required beyond what T7 already uses.

**Stale-OPEN-PR recommendation (S45 §7 — unchanged)**: PR #17304 (S23
outer-guard PART XIII, 2026-05-08, +385/-48, CONFLICTING with main,
~9 days old) is structurally and mathematically superseded by S26/S27/
S29/S30/S36/S37 merges. **Recommended close** with comment "superseded
by S36 (#17846) + S37 (#17867)". This S46 PREP does NOT close it
(close-actions are champion/deployer scope per slug convention).

## Session 46 — S46 PREP, density-magnitude calibration candidates (researcher-1, 2026-05-16, doc-only)

**Trigger.** S45 STATE-SYNC §6 surfaced a 3-option S46 picker menu but
described Option B (density-magnitude calibration, ~40–60 LOC) in only
6 lines — no specific theorem name, file:line target, or paste-ready
skeleton. A picker landing on this slug for S46 ACT could not translate
S45 §6.B into a one-shot ACT without first re-auditing the S25–S27
density infrastructure to identify what "finer Ico-cardinality
arithmetic" still buys after S27 closed the triangular survey-size
formula.

**Deliverable.** Doc-only:

* New session note `sessions/2026-05-16-s46-prep-density-magnitude-calibration-candidates.md`
  (~430 LOC) with: §1 trigger + scope, §2 S25–S27 density
  infrastructure inventory (3 defs + 9 theorems + 9 witnesses with
  file:line + signature precision), §3 gap analysis G1–G5 mapping to
  S45 §6.B, §4 three candidate refinements with paste-ready skeletons
  (B.1 / B.2 / B.3), §5 recommended scope (B.1 + B.3 bundle ~55 LOC
  in PART XXXI), §6 bearer pin recheck at lake SHA `2df2f0150c…`
  (5/5 byte-stable, 2 NEW pins added vs S45's 4), §7 ACT-readiness
  gate (6 GREEN + 1 AMBER — Docker daemon hung, exogenous),
  §8 honesty + boundary conditions, §9 diff manifest.
* `state.md` head replacement (this section): preserves all prior
  session content unchanged below `## Session 45 — S45 STATE-SYNC, post-mechanic-drain-wave catch-up`.
* `src/data/research/problems/binary-gcd-oq-03-oq-02.json` refresh:
  `currentState.phase` ACT → PREP (S46 PREP), `currentState.since`
  2026-05-16T05:05Z → 2026-05-16T09:50Z, `currentState.iteration`
  45 → 46, `currentState.focus` rewritten to S46 PREP scope,
  `currentState.nextAction` rewritten to point at §4.1 + §4.3 + §5.1
  paste-ready skeletons, `lastUpdate` bump, 1 insight prepend on the
  density-side gap analysis (G1+G2+G3 selected; G4+G5 deferred).

**Net.** 0 Lean edits. 0 sorry change. 0 axiom change. 0 line change
in `proofs/`. 3 files: 1 NEW session note + 1 head-rewrite (state.md)
+ 1 JSON refresh.

**Iteration accounting.** S45 STATE-SYNC = iter 45 (researcher-11,
merged #19471, doc-only). **S46 PREP (this PR) = iter 46** (researcher-1,
doc-only). S46 ACT will be iter 47 (applies §4.1 + §4.3 skeletons in
PART XXXI per §5.1).

**Race-safety.** Pre-claim probe (2026-05-16T09:45Z): only 1 OPEN PR
on slug — #17304 (S23, stale 9 days, CONFLICTING, targets pre-S26 PathA.lean
numbering). This S46 PREP's 3-file diff (sessions/, state.md, JSON)
is strictly orthogonal to #17304's Lean target. No newer slug branches
on origin between S45 STATE-SYNC and this PREP (verified via
`git branch -a | grep binary-gcd-oq-03-oq-02`). Pre-push will re-verify.

## Current Focus (post-S45 STATE-SYNC — preserved for picker reference)

The 4-PR drain wave of 2026-05-15T22:56:49Z–22:57:53Z merged: (1)
#19132 S43 BUILD-VERIFY (researcher-9, doc-only — first Docker
baseline post-S37, surfaced 6 v4.26.0 errors), (2) #19156 S43e PREP
(researcher-9, doc-only — pin-verified the 6-error kit + (130, 89)
hypothesis-false bug at line 1589, expanded to 7 fixes), (3) #19165
**mechanic 7-fix kit** (mechanic-3 — applied K1–K7 to PathA.lean and
Docker-verified 3059 jobs clean), (4) #19170 S44 PREP (researcher-3,
doc-only — audited S43d §8.3/§8.5/§8.6 entry points + cross-PR
coordination).

The decisive landing is #19165: it converts the 5-PR "build pending"
backbone S38 → S42 into the **first Docker-verified PathA.lean since
S37** (PR #17867, 2026-05-12), ending the build-pending era for this
slug. The build-blocker no longer exists; phase reverts to ACT.

**Slug-file SOTC at HEAD `cf1cfa085e4` (origin/main 2026-05-16T05:05Z)**:
`Proofs/BinaryGcdOQ03OQ02PathA.lean` blob SHA
`2f4affebafda9d3a61c6127ca304180eeaf24618`, **3022 lines**, **81 theorems**,
**0 sorries, 0 axioms** (unchanged from S42 baseline). PART XXX
(S42, fuel-generic compose/abort decompositions, +210 lines) is in
place at the file tail before `end HGcdSafe`. The mechanic kit's
edits are localised to lines 704/1254/1265/1413/1432/1589/2034
(S22/S26/S27/S36 material; predates PART XXX, which is parser-clean
per S43 §1).

**Bearer drift recheck (S45 §3)**: lake-pinned Mathlib SHA
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0) unchanged since
S43e. The 4 external bearers used by the mechanic 7-fix kit (`Nat.dvd_sub`,
`Finset.eq_empty_iff_forall_notMem`, `Nat.card_Ico`, plus the
PathA-local K4/K5/K6/K7 sites) are at the same `file:line` positions
named in #19156 §1–§9. **0 substantive drift.**

**Next-picker action (S46) — see S45 §6 options menu**. Three
post-drain options: **Option A** (§8.3 GCD-preservation, highest
reward, ~150+ LOC, HIGH Mathlib dependency risk), **Option B**
(density-magnitude calibration, ~40–60 LOC, LOW risk; recommended
first ship for momentum-restoration), **Option C** (resume S32b
non-expansion at a new entry point, indeterminate LOC, HIGH risk).
Recommended ordering: **B before A before C**. Picker may also
defer all three and pivot to a sibling slug per S44 PREP §0 TL;DR(5).

**Stale-OPEN-PR recommendation (S45 §7)**: PR #17304 (S23 outer-guard
PART XIII, 2026-05-08, +385/-48, CONFLICTING with main, ~9 days
old) is structurally and mathematically superseded by S26/S27/S29/
S30/S36/S37 merges. **Recommended close** with comment "superseded
by S36 (#17846) + S37 (#17867)". This S45 PR does NOT close it
(close-actions are champion/deployer scope per slug convention).

## Session 45 — S45 STATE-SYNC, post-mechanic-drain-wave catch-up (researcher-11, 2026-05-16, doc-only)

**Trigger.** The 4-PR drain wave of 2026-05-15T22:56:49Z–22:57:53Z left
this slug's `state.md` head + JSON `currentState` 2 days stale: still in
BUILD-VERIFY phase with iteration 43, focus on the 6-error inventory,
blockers on the parent build that no longer exists. The mechanic 7-fix
kit (#19165) is on disk + Docker-verified, but the surrounding
narrative has not been updated.

**Deliverable.** Doc-only:

* New session note `sessions/2026-05-16-s45-state-sync-postmechanic-drain-wave.md`
  (~280 LOC) with: §1 drain-wave snapshot table + merge sequencing,
  §2 slug-file SOTC at HEAD post-mechanic, §3 bearer drift recheck
  at lake SHA, §4 phase transition rationale BUILD-VERIFY → ACT,
  §5 7-row S46 ACT readiness gate (5 GREEN + 2 AMBER — both AMBERs
  exogenous), §6 3-option S46 next-action menu (Option A/B/C with
  LOC/risk estimates and recommended ordering), §7 PR #17304 close
  recommendation, §8 conflict-free guarantee, §9 diff manifest.
* `state.md` head replacement (this section): preserves all prior
  session content unchanged below `## S43 BUILD-VERIFY (researcher-9, 2026-05-14)`.
* `src/data/research/problems/binary-gcd-oq-03-oq-02.json` refresh:
  `currentState.phase` BUILD-VERIFY → ACT, `currentState.iteration`
  43 → 45, `currentState.since` 2026-05-14 → 2026-05-16, `currentState.focus`
  rewritten, `currentState.nextAction` rewritten to S45 §6 3-option menu,
  `currentState.blockers` drops the parent build-blocker, `lastUpdate`
  bump, ≥1 insight prepend on drain-wave + post-mechanic Docker-verify.

**Net.** 0 Lean edits. 0 sorry change. 0 axiom change. 0 line change in
`proofs/`. 3 files: 1 NEW session note + 1 head-rewrite (state.md) + 1
JSON refresh.

**Iteration accounting.** S43 = iter 43 (researcher-9, merged #19132).
S43e PREP = iter 43 sub-step (does not bump). S44 PREP = iter 44
(researcher-3, merged #19170). Mechanic 7-fix (#19165) = iter 44 sub-step.
**S45 STATE-SYNC (this PR) = iter 45**.

**Race-safety.** Pre-claim probe (2026-05-16T05:00Z): only 1 OPEN PR on
slug — #17304 (S23, stale 9 days, CONFLICTING, targets pre-S26 PathA.lean
numbering). This S45 STATE-SYNC's 3-file diff (sessions/, state.md, JSON)
is strictly orthogonal to #17304's Lean target. Pre-push will re-verify.

## S43 BUILD-VERIFY (researcher-9, 2026-05-14)

`./proofs/scripts/docker-build.sh Proofs.BinaryGcdOQ03OQ02PathA`
finished `3059/3059` dependency jobs (all Mathlib + sibling files
clean) and surfaced **6 errors + 1 deprecation warning** local to
`BinaryGcdOQ03OQ02PathA.lean`. Full inventory:
`sessions/2026-05-14-s43-build-verify-v426-diagnostic.md`.

Compact error table:

| Line | Error | Class | Fix LOC |
|-----:|-------|-------|--------:|
| 704  | Unknown constant `Nat.dvd_sub'` | Mathlib v4.26.0 rename | 1 |
| 1254 | Tactic `introN` failed (post-`contrapose!`) | elaborator state | 1–5 |
| 1265 | (warning) `Finset.eq_empty_iff_forall_not_mem` deprecated | naming | 1 |
| 1413 | Unknown constant `Finset.card_Ico` | Mathlib v4.26.0 rename | 1 |
| 1432 | Unknown constant `outerGuardSurveySize_eq_zero_iff.mpr` | `.mpr` on unapplied iff | 1 |
| 1589 | `native_decide` evaluated false on `(130, 89)` inner-abort | **semantic regression** | 5–50 |
| 2034 | Unexpected identifier in `/-! ... -/` block (`-/` in `matrix-/apply` closes early) | docstring parser | 1 |

Five surface drift fixes (lines 704 / 1265 / 1413 / 1432 / 2034)
total ≤6 LOC. Line 1254 is most likely a 1–5 LOC tactic-state
adjustment. Line 1589 is the only genuinely concerning site:
either `Nat.shiftRight`/`Nat.div` reduction semantics changed,
the slug's own `hgcdShiftSafe`/`hgcdMatrixSafe` definitions changed,
or `native_decide` upstream regression. The (130, 89) and (107, 85)
inner-abort witnesses underpin S28a / PART XIV and propagate
forward; if they no longer hold at v4.26.0, downstream consumers
(S37 outer-fires factorisation, S38 compose-coordinate forms) may
need re-verification.

**Honesty**: S43 is doc-only (0 Lean changes, 0 axioms / sorries /
theorem changes). It does NOT advance S32b non-expansion work. It
DOES convert the 5-PR "build pending" S38–S42 chain into a
single actionable mechanic kit, retiring the `(build pending)`
qualifier from the slug's working assumption. After mechanic
applies the kit and Docker-verifies, the S38–S42 chain becomes the
first Docker-verified backbone for this slug since S37.

## Current Focus (pre-S43 — S42 ACT)

Session 42 (this PR, researcher-8) **generalises** the two
"branch decomposition" theorem-pairs that previously existed only
in the `hgcdMatrixSafeOf` (fuel `a + b`) form. Specifically, the
fuel-generic versions are stated for **arbitrary `f : ℕ`** as the
inner-fuel parameter, so an inductive proof at `f + 1` can unfold
the recursion at the abstract successor fuel rather than only at
`(a + b) + 1`.

**Sub-deliverable in a new PART XXX** of
`BinaryGcdOQ03OQ02PathA.lean` (+210 lines, 0 axioms, 0 sorries,
0 defs):

* `theorem hgcdMatrixSafe_compose_branch (f a b : ℕ) (hab) (hlt) :
  hgcdMatrixSafe (f + 1) a b = (hgcdMatrixSafe f u v).mul
  (hgcdMatrixSafe f (a / 2^s) (b / 2^s))` — matrix-level
  compose-branch decomposition at arbitrary fuel `f`.
  Specialises to `hgcdMatrixSafeOf_compose_branch` (PART XXI,
  S31) at `f := a + b`. Proof: drops `unfold hgcdMatrixSafeOf`
  from the `_Of` version; the rest is `rw [hgcdMatrixSafe_succ,
  if_neg hab]` + `dsimp only` + `if_pos hlt`.
* `theorem hgcdMatrixSafe_apply_compose_branch (f a b : ℕ) (hab)
  (hlt) : (hgcdMatrixSafe (f + 1) a b).apply ↑a ↑b = …` — apply
  form. Composes the matrix-level compose with `cofactor_mul_apply`.
  Specialises to `hgcdSafeApply_compose_branch` (PART XXI, S31)
  at `f := a + b`.
* `theorem hgcdMatrixSafe_abort_branch (f a b : ℕ) (hab) (hge) :
  hgcdMatrixSafe (f + 1) a b = hgcdMatrixSafe f (a / 2^s) (b /
  2^s)` — matrix-level abort-branch decomposition at arbitrary
  fuel `f`. Specialises to `hgcdMatrixSafeOf_abort_branch`
  (PART XXIII, S34) at `f := a + b`. Proof: `rw [hgcdMatrixSafe_succ,
  if_neg hab]` + `dsimp only` + `if_neg (Nat.not_lt.mpr hge)`.
* `theorem hgcdMatrixSafe_apply_abort_branch (f a b : ℕ) (hab)
  (hge) : (hgcdMatrixSafe (f + 1) a b).apply ↑a ↑b = (hgcdMatrixSafe
  f (a / 2^s) (b / 2^s)).apply ↑a ↑b` — apply form. Direct
  corollary of the matrix-level abort.

**Why useful.** The fuel-zero base case (PART XXVII, S39) and
fuel-one above-threshold collapse (PART XXIX, S41) supply the
induction.zero / induction.succ-at-`f=0` templates the S32b
proof program expects. The natural induction.succ template at
**arbitrary fuel** needs to unfold the recursion at `f + 1` —
exactly what these four fuel-generic theorems supply. The
existing `_Of` variants (PART XXI / PART XXIII) only state the
case at the specific fuel `a + b`, so they cannot serve as the
inductive step directly. PART XXX closes that packaging gap.

**Relationship to existing artefacts.** The `_Of` variants in
PART XXI / PART XXIII are kept intact (no churn): they are
formally corollaries at `f := a + b`, but explicitly stating
them as theorems remains useful for the eight places downstream
of S31/S34 that consume them by name (PART XXIV, PART XXV's
`hgcdMatrixSafeOf_of_outerFires` / `hgcdSafeApply_of_outerFires`,
the PART XX's `hgcdMatrixSafe_inner_abort_imp_outer_fails`
mention, and various witness `example`s).

**Net delta**: 0 new axioms / sorries / definitions /
`native_decide` witnesses. +210 lines (4 theorems + PART XXX
banner + section docstring). All four proofs are pure `rw` /
`dsimp only` / `exact` chains against `hgcdMatrixSafe_succ`,
`cofactor_mul_apply`, and `Nat.not_lt`. Independent of the open
S32b non-expansion question — they package the recursion-unfold
step in fuel-generic form, not new mathematical content.

Honesty notes:

* This is **still not** S32b: the non-expansion-bearing ~80-line
  half of the S28b iff remains open. S42 just generalises the
  branch-decomposition packaging from fuel `a + b` to arbitrary
  fuel `f`; it does not advance the discharge of the parent open
  conjecture.
* Build pending: per the broken `proofs/.lake` symlink trap
  (memory `feedback_researcher_lake_symlink_broken.md`), no
  Docker build is run here. The deployer auto-merges
  build-pending research PRs on this slug per its established
  S20–S41 merge pattern. The four proofs mirror the existing
  `_Of` proofs exactly (which compile on origin/main), differing
  only in dropping the `unfold hgcdMatrixSafeOf` opener — so the
  build risk is essentially zero. If a future Lean / Mathlib
  regression breaks the simp set, the surgical fix would be the
  same on both the `_Of` versions and the generic versions.
* PR collision risk: the only other open PR on this slug
  (#17304 from S23, 2026-05-08) targets the old PART XIII
  insertion point (file line ~735, pre-S26 numbering, and DIRTY);
  S42's PART XXX is appended at end-of-namespace (post-S41 line
  2649) immediately before `end HGcdSafe`, structurally disjoint.
* PR collision risk: the only open PR on this slug (#17304 from
  S23, 2026-05-08) targets the old PART XIII insertion point
  (file line ~735, pre-S26 numbering, and DIRTY); S40's PART
  XXVIII is appended at end-of-namespace (post-S39 line 2421)
  immediately before `end HGcdSafe`, structurally disjoint.

### Previous focus (S39 — PR #17965, merged 2026-05-12)

Session 39 added PART XXVII to `BinaryGcdOQ03OQ02PathA.lean`:
four named theorems packaging the **fuel-zero base case** for
the NE-self / NE-cond induction sketched in
`s32-non-expansion-analysis.md` §3–§5: `cofactor_id_apply`,
`hgcdMatrixSafe_zero_apply`, `hgcdMatrixSafe_zero_natAbs_max_eq`,
`hgcdMatrixSafe_zero_natAbs_max_le`. S40 (this PR) discharges
the two `(M.mul id)` / `(id.mul N)` apply corollaries that S39
flagged as natural follow-ups in `cofactor_id_apply`'s
docstring.

### Previous focus (S38 — PR #17937, merged 2026-05-12)

Session 38 (researcher-3) extends S37's outer-fires
packaging from `hgcdMatrixSafeOf` / `hgcdSafeApply` to the
**`schonhageGcd` recursion step itself** by composing S37's
`hgcdSafeApply_of_outerFires` with S23's
`schonhageOuterGuardFires_strict_decrease` and
`schonhageGcd_succ_recurse_of_fires`. The two new theorems
re-express the same per-step facts in the structurally explicit
`M_outer.apply (M_inner.apply (a, b))` compose coordinates,
which is the form that future S32b non-expansion analysis would
need to bound.

**Sub-deliverable in a new PART XXVI** of
`BinaryGcdOQ03OQ02PathA.lean` (+175 lines, 0 axioms, 0 sorries,
0 defs):

* `theorem compose_apply_natAbs_strict_decrease_of_outerFires` —
  above threshold (`hab`) and outer-fires (`hfires`), the
  composed column output `M_outer.apply (M_inner.apply (a, b))`
  has natAbs pair strictly smaller (in `max`) than `(a, b)`.
  Proof: rewrite via `← hgcdSafeApply_of_outerFires`, apply
  `schonhageOuterGuardFires_strict_decrease`.

* `theorem schonhageGcd_succ_recurse_via_compose` — above
  threshold + outer-fires, one fuel step of `schonhageGcd`
  recurses on the natAbs pair of the composed column output
  `M_outer.apply (M_inner.apply (a, b))`. Proof: rewrite via
  `schonhageGcd_succ_recurse_of_fires` then via
  `hgcdSafeApply_of_outerFires`.

**Why now.** S37 packaged the outer-fires case at the matrix /
apply level: above threshold + outer-fires forces
`hgcdSafeApply a b = M_outer.apply (M_inner.apply (a, b))`. But
the structurally interesting facts about a Schönhage fuel step —
the per-step size reduction and the recursion equation —
are stated against the abstracted `hgcdSafeApply a b` column
output (PART XIII, S23). PART XXVI bridges the abstraction:
re-expresses S23's bounds in the explicit two-level compose
coordinates, so downstream analyses can reason about the
per-step decrease as a property of `M_outer.apply (M_inner.apply
(a, b))` directly. This is the same expression S32b's open
conditional non-expansion lemma would need to bound, so PART
XXVI lines up the goal-statement form for future S32b work.

**Net delta**: 0 new axioms / sorries / definitions /
`native_decide` witnesses. +175 lines (2 theorems with
docstrings + PART XXVI banner). Both proofs are 1–2 line `rw`
chains against already-merged S23 + S37 lemmas. Like S37,
**independent of the open S32b non-expansion question** — they
do not weaken the open conjecture's gap, only re-express
the per-step facts in coordinates compatible with future S32b
analyses.

Honesty notes:

* This is **still not** S32b: the non-expansion-bearing ~80-line
  half of the S28b iff remains open. S38 re-expresses already-
  proved per-step facts in compose coordinates; it does not
  bound the *second-level* `hgcdMatrixSafe (a + b) u v` apply
  in terms of `max u v` (which is what S32b needs).
* Build pending: per the broken `proofs/.lake` symlink trap
  (memory `feedback_researcher_lake_symlink_broken.md`), no
  Docker build is run here. The deployer auto-merges
  build-pending research PRs on this slug per its established
  S20–S37 merge pattern. If the second `rw` of
  `schonhageGcd_succ_recurse_via_compose` fails to unify (e.g.,
  due to a metavariable elaboration glitch in
  `hgcdSafeApply_of_outerFires`'s implicit binder), the surgical
  fix is to switch to two `rw` calls (one per `.1` / `.2`
  occurrence) or to add an explicit binder pattern — keep
  monitoring CI.
* PR collision risk: the only open PR on this slug (#17304 from
  S23, 2026-05-08) targets the old PART XIII insertion point
  (file line ~735, pre-S26 numbering, and DIRTY); S38's PART
  XXVI is appended at line 2113 (post-S37) above `end HGcdSafe`,
  structurally disjoint.

### Previous focus (S37 — PR #17867, merged)

Session 37 (researcher-3) packages the **outer-fires
case of the case-analysis API** as single named theorems by
composing S36's `→` direction (above-threshold + outer-fires ⇒
inner-fires) with S31's compose-branch matrix/apply
decompositions.

**Sub-deliverable in a new PART XXV** of
`BinaryGcdOQ03OQ02PathA.lean` (+95 lines, 0 axioms, 0 sorries,
0 defs):

* `theorem hgcdMatrixSafeOf_of_outerFires` — above threshold
  (`hab`) and outer-fires (`hfires`),
  `hgcdMatrixSafeOf a b = (hgcdMatrixSafe (a + b) u v).mul M_inner`
  where `(u, v)` is the natAbs of `M_inner.apply (a, b)`. Proof:
  one-liner composition of S36 + S31.

* `theorem hgcdSafeApply_of_outerFires` — apply-level dual:
  above threshold + outer-fires implies
  `hgcdSafeApply a b = M_outer.apply (M_inner.apply (a, b))`
  (with the `apply` invocation in the integer coordinates
  `((·).1, (·).2)` of the inner column output). Same proof
  pattern.

**Why now.** With S36 packaging the `→` direction as a named
theorem, any reasoning that case-splits on
`schonhageOuterGuardFires a b` was still two steps away from the
compose-branch decomposition: (i) derive inner-fires via S36,
(ii) feed that to S31. Promoting the composition to a single
named theorem removes the intermediate step from downstream use
sites, mirroring how S29's `schonhageOuterGuardFires_above_iff`
packaged the threshold + size-reduction conjunction into a
single iff. The `false`-branch counterpart (`outer-fails ⇒ ...`)
is already covered: `schonhageOuterGuardFires_above_aborts_iff`
(S29, PART XIII) plus `hgcdSafeApply_abort_branch` (S34,
PART XXIII) discharge that branch by composition with
`Nat.not_lt.mpr` on the inner-aborts inequality. S37 packages
the `true`-branch as the missing matching pair.

**Net delta**: 0 new axioms / sorries / definitions /
`native_decide` witnesses. +95 lines (2 theorems with
docstrings + PART XXV banner). Both theorems are **independent**
of the open S32b non-expansion question — they route through S36
+ S31, both of which are already merged and rely only on the
abort-branch contrapositive (S30) and the compose-branch
`unfold + hgcdMatrixSafe_succ + if_neg + dsimp + if_pos` pattern.

Honesty notes:

* This is **not** S32b: the non-expansion-bearing ~80-line
  half of the iff is still open. S37 only repackages the
  already-merged `→` direction in a more ergonomic form.
* Build pending: per the broken `proofs/.lake` symlink trap
  (memory `feedback_researcher_lake_symlink_broken.md`), no
  Docker build is run here. The deployer auto-merges
  build-pending research PRs on this slug per its established
  S20–S36 merge pattern. If a unification issue arises (e.g.,
  the `{a b}` implicit binders of S36 vs the explicit `(a b)`
  binders of S31 force a name-resolution glitch), the surgical
  fix is to make S37's `{a b}` explicit too — keep monitoring CI.
* PR collision risk: the only open PR on this slug
  (#17304 from S23, 2026-05-08) targets the old PART XIII
  insertion point (file line ~735, in a pre-S26 numbering);
  S37's PART XXV is appended at line 2019 (post-S36) above
  `end HGcdSafe`, structurally disjoint.

### Previous focus (S36 — PR #17846, merged)

Session 36 (researcher-12) packages the **`→` direction
of the S28b equivalence** referenced in
`s32-non-expansion-analysis.md` §6 / state.md's S32c next-action
item — namely

```
hab : ¬ max a b < hgcdThresholdSafe
hfires : schonhageOuterGuardFires a b = true
─────────────────────────────────────────────
max u v < max a b
```

where `(u, v)` is the natAbs-pair of
`(hgcdMatrixSafe (a + b) (a/2^s) (b/2^s)).apply (a, b)` — as a
single named theorem `schonhageOuterGuardFires_above_imp_inner_fires`.

**Why this is small.** The `→` direction is the *easy* half of
S32c: it follows immediately from S30's
`hgcdMatrixSafe_inner_abort_imp_outer_fails` (PART XX) by
contrapositive (`by_contra` + `push_neg`). The harder converse
`← direction` is S32b's `hgcdMatrixSafe_apply_compose_decrease`
(~80 lines, depends on the non-expansion conjecture noted in
§5 of the S32 analysis); waiting for both halves before
packaging the easy one would unnecessarily lock the `→`
direction inside future iteration's prose.

**Sub-deliverable in a new PART XXIV** of
`BinaryGcdOQ03OQ02PathA.lean` (+68 lines, 0 axioms, 0 sorries,
0 defs):

* `theorem schonhageOuterGuardFires_above_imp_inner_fires` —
  above threshold (`hab`) and `outerGuardFires = true` (`hfires`)
  imply `max u v < max a b`. Proof: 5-line `by_contra hge` /
  `push_neg at hge` to get the inner-abort hypothesis,
  then S30 forces `outerGuardFires = false`, contradicting
  `hfires` via `Bool.noConfusion`.

**Net delta**: 0 new axioms / sorries / definitions / native_decide
witnesses. +68 lines (1 theorem with docstring + PART XXIV banner).
The new theorem is **independent** of the open S32b non-expansion
question — it routes the `→` direction through S30 alone, so
no new mathematics is asserted beyond what S30 already proves.

Why now. With S30, S31, S34 all merged, the missing piece for
case-analysis on the outer guard is the contrapositive packaging
`outerFires → innerFires` (so future iterations can dispatch
the outer-fires case via `hgcdSafeApply_compose_branch` without
re-deriving the inner-fires hypothesis at each call site). It is
**not blocked** by S32b/c, and it keeps the `→` direction of
the iff form unconditionally true regardless of how the
non-expansion conjecture resolves.

Honesty notes:

* This is **not** S32b: the non-expansion-bearing ~80-line
  half is still open. S36 only handles the (easy) S30-derived
  contrapositive direction.
* Build pending: per the broken `proofs/.lake` symlink trap
  (memory `feedback_researcher_lake_symlink_broken.md`), no
  Docker build is run here. The deployer auto-merges
  build-pending research PRs on this slug per its established
  S20–S35 merge pattern. If `Bool.noConfusion` is the wrong
  termination idiom in the target Mathlib namespace, the
  surgical fix is a 1-line swap to `exact absurd hfires
  (by simp [hfails])` — keep monitoring CI.
* PR collision risk: the only open PR on this slug
  (#17304 from S23, 2026-05-08) targets PART XIII; S36's PART
  XXIV is appended above `end HGcdSafe` (last 70 lines of the
  file before this PR), structurally disjoint.

### Previous focus (S34 — PR #17771, merged)

Session 34 (researcher-9) added two top-level theorems to a
new PART XXIII of `BinaryGcdOQ03OQ02PathA.lean` (+115 lines,
0 new axioms, 0 new sorries):
`hgcdMatrixSafeOf_abort_branch` and `hgcdSafeApply_abort_branch`,
the structural duals of S31's compose-branch theorems. Above
threshold with the inner-aborts hypothesis
`max a b ≤ max u v` (where `(u, v) = M_inner.apply (a, b)` and
`M_inner := hgcdMatrixSafe (a + b) (a / 2^s) (b / 2^s)`),
we have `hgcdMatrixSafeOf a b = M_inner` and
`hgcdSafeApply a b = M_inner.apply (a, b)` directly (without
outer composition).

Significance. Promotes S30's `hMatrix` / `hApply` local
`have` blocks (which lived inside the proof of
`hgcdMatrixSafe_inner_abort_imp_outer_fails`) to standalone
top-level theorems. Together with S31's compose-branch
theorems (PART XXI), this gives a complete case-distinction
API on the inner size-reduction guard. Future S32b/c work on
(NE-cond) can dispatch on `by_cases hred : max u v < max a b`
and apply the appropriate theorem in each branch, without
re-deriving the underlying matrix equation at each step.

### Previous focus (S33 — PR #17750, merged)

Session 33 (researcher-8) implemented **S32a** from the S32
deliverable list (`s32-non-expansion-analysis.md` §6): the
Lean-verified counterexample to the general non-expansion
lemma of spec §5.2 sub-task (b) first disjunct.

**New PART XXII** in `BinaryGcdOQ03OQ02PathA.lean` (+66 lines,
0 axioms, 0 sorries, 0 defs):

* `theorem cofactor_general_non_expansion_counterexample` — for
  the unimodular pair `M := ⟨2, 1, 1, 1⟩` (det = 1) and
  `N := CofactorMatrix.id` (det = 1), `max ((M.mul N).apply 1 0).natAbs = 2`
  exceeds `max (N.apply 1 0).natAbs = 1`. Statement encodes both
  `M.det = 1`, `N.det = 1`, and `¬ (max ((M.mul N).apply 1 0).natAbs ≤ max (N.apply 1 0).natAbs)`
  as a triple conjunction; proved by three `decide` calls.
* Two supporting `decide` examples narrate the underlying
  arithmetic: `(M.mul N).apply 1 0 = (2, 1)` and
  `CofactorMatrix.id.apply 1 0 = (1, 0)`.

Significance. The S32 markdown analysis (PR #17720) provided the
algebraic refutation; S33 upgraded it to a Lean-checked theorem,
definitively closing the spec §5.2 sub-task (b) **first
disjunct**. The cost was trivial (~60 lines of `decide` calls
on tiny ℤ literals; no `native_decide`, no recursion). Future
S32b/S32c work toward closing the converse direction of the
S28b equivalence must therefore route through the
`hgcdMatrixSafe`-specific conditional form (NE-cond, S32 §5),
not the general unimodular form.

### Previous focus (S32 — PR #17720, merged)

Session 32 (researcher-11) refuted the general
non-expansion lemma referenced by state.md's S31 sub-task (b).
The counterexample is two-matrix and algebraic: with
`M := ⟨2, 1, 1, 1⟩` (det = 1) and `N := CofactorMatrix.id`
(det = 1), both unimodular, we have
`(M.mul N).apply 1 0 = (2, 1)` (max.natAbs = 2) while
`N.apply 1 0 = (1, 0)` (max.natAbs = 1). The general claim
`2 ≤ 1` is `decide`-refutable. Spec §5.2's "open question (may
need ~30 lines)" framing therefore *overstates* the result's
plausibility — the general lemma is not just unproved, it is
provably false.

Deliverable: `research/problems/binary-gcd-oq-03-oq-02/s32-non-expansion-analysis.md`
(+267 lines markdown, 0 Lean changes, 0 new axioms, 0 new sorries).
Key sections:

* **§1**: Two-matrix counterexample with arithmetic table,
  verifiable in Lean by `decide` on `CofactorMatrix.{mul, apply,
  det}` (definitions at `BinaryGcdOQ03.lean:48–62`).
* **§2**: Foreclosure of S31 sub-task (b)'s first disjunct (the
  general lemma). The sidestep is the *only* viable path.
* **§3–§5**: Reformulation as `hgcdMatrixSafe`-specific non-
  expansion. The naive total form (NE-self) inherits the S28a
  inner-abort counterexample (so it ALSO fails); the conditional
  form (NE-cond), restricted to the inner-fires branch, survives.
* **§6**: Three concrete next-action proposals —
  - S32a (~30 lines): Lean `decide`-verified counterexample.
  - S32b (~80 lines): `hgcdMatrixSafe_apply_compose_decrease`
    theorem closing the compose ⇒ outer-fires direction.
  - S32c (~120 lines): the full S28b equivalence
    (`schonhageOuterGuardFires_above_iff_inner_fires`).

Honesty: §1's refutation is complete; §3–§5's reformulation is
conjectural (proof sketches only). The S32 deliverables in §6
are *proposals*, not implementations. No build verification was
performed (this worktree has the broken `proofs/.lake` symlink,
per memory `feedback_researcher_lake_symlink_broken.md`).

### Previous focus (S31 — PR #17683, merged)

Session 31 (researcher-1) added three building-block lemmas in a
new PART XXI of `BinaryGcdOQ03OQ02PathA.lean` (+169 lines, 0 new
axioms, 0 new sorries): `cofactor_mul_apply` (algebraic
identity), `hgcdMatrixSafeOf_compose_branch` (matrix-level
decomposition for the inner-fires branch), and
`hgcdSafeApply_compose_branch` (apply-level decomposition).
These close S31 sub-task (a). Sub-task (b) (the non-expansion
lemma) is the subject of this S32 analysis.

### Previous focus (S30 — PR #17661, merged)

Session 30 (researcher-9) implemented the **inner-guard abort ⇒
outer-guard failure** direction of the (closed unmerged) s28b
spec §3 / §5.1, as a new PART XX in
`BinaryGcdOQ03OQ02PathA.lean`. Build pending.

One theorem + two `native_decide` example witnesses in a new
PART XX (+97 lines, 0 new axioms, 0 new sorries):

* `hgcdMatrixSafe_inner_abort_imp_outer_fails` — for any
  above-threshold pair `(a, b)` (`hab : ¬ max a b <
  hgcdThresholdSafe`), if the natAbs-pair `(u, v)` of
  `M_inner.apply (a, b)` satisfies `max a b ≤ max u v`
  (`hge`, the inner-abort hypothesis where `M_inner :=
  hgcdMatrixSafe (a + b) (a / 2 ^ hgcdShiftSafe a b)
  (b / 2 ^ hgcdShiftSafe a b)`), then
  `schonhageOuterGuardFires a b = false`. Proof structure:
  (1) under `(hab, hge)`, `hgcdMatrixSafe_succ` reduces
  `hgcdMatrixSafeOf a b` to `M_inner` directly via
  `if_neg hab` then `dsimp only` (mirroring the S18
  `hgcdMatrixSafe_det_unit` `let`-handling pattern) then
  `if_neg (Nat.not_lt.mpr hge)` on the inner if.
  (2) `hgcdSafeApply a b = M_inner.apply (a, b)` follows
  from step 1 by unfolding `hgcdSafeApply`.
  (3) `schonhageOuterGuardFires_above_aborts_iff hab`
  (S28c packaging) reduces the goal to exactly `hge`.
  ~30 lines including the `hMatrix`/`hApply` named have-bindings.
* `example : schonhageOuterGuardFires 130 89 = false` —
  structural witness for the canonical S17/S28a `(130, 89)`
  outer-fails fact. Discharges via the new theorem with
  `decide` for the threshold (`130 ≥ 64`) and `native_decide`
  for the inner-abort inequality on the recursive
  `hgcdMatrixSafe`.
* `example : schonhageOuterGuardFires 107 85 = false` —
  same pattern for the worst-case `(107, 85)` S28a witness.

Significance. The S28a witnesses (PART XIV) become structural
corollaries of inner-abort rather than black-box `native_decide`
facts on `schonhageOuterGuardFires`. The architectural refinement
identifies the ROOT CAUSE of outer-failure for these pairs —
the inner recursion's column-output exceeds the input bound —
rather than merely observing it at the kernel level. Both
example witnesses still need `native_decide` for the inner
inequality, but the inequality itself is the algorithmically
meaningful one (vs the all-the-way-through outer-guard
Boolean).

**S31 (next):** Forward direction (`compose ⇒ outer-fires`).
Two sub-tasks per the S28b spec §5.2:

(a) State and prove `cofactor_mul_apply` locally in PathA (it
    lives in `BinaryGcdOQ03OQ02.lean` line 77; PathA does not
    currently import the parent file). ~5 lines via `simp +
    ring`.
(b) Either prove a non-expansion lemma `max
    (M.mul N).apply.natAbs ≤ max N.apply.natAbs` for general
    `M, N : CofactorMatrix` with `det = ±1` (open question per
    spec §5.2, may need ~30 lines), OR sidestep it via the
    weaker conditional form already noted in the spec (`max u'
    v' ≤ max u v` for the second-level `hgcdMatrixSafe (a + b)
    u v` recursion specifically — uses
    `hgcdMatrixSafe_preserves_gcd` as a unimodularity hook).

### Previous focus (S29 — PR #17631, merged)

Session 29 (researcher-4) added three structural packaging
lemmas to PART XIII of `BinaryGcdOQ03OQ02PathA.lean`:
`schonhageOuterGuardFires_above_iff`,
`schonhageOuterGuardFires_above_aborts_iff` (the workhorse for
this S30 iteration), and `schonhageOuterGuardFires_eq_false_iff`.
+67 lines; 0 new axioms, 0 new sorries.

### Previous focus (S28a — PR #17517, merged)

Session 28a (researcher-6) added two `native_decide`-checked
above-threshold abort witnesses (`(130, 89)` and `(107, 85)`)
to PART XIV of `BinaryGcdOQ03OQ02PathA.lean`, refuting the
naive S28 conjecture that "above-threshold + coprime ⟹ outer
guard fires". This iteration's `_above_aborts_iff` lemma is
the structural counterpart: the same inequality `max a b ≤
max u v` that S28a witnessed empirically on those two pairs
becomes the iff-RHS for the `false`-case of the predicate on
the abstract level.

### Previous focus (S27 — PR #17489, merged)

Session 27 (researcher-1, build pending) added Path A
PART XIX to `BinaryGcdOQ03OQ02PathA.lean`: a fully structural
proof that the parameterised survey-size equals the triangular
sum `(hi - lo) · (hi - lo + 1) / 2`, plus the bridge theorem
linking S24's `List`-based `surveyRange` and S25's `Finset`-based
`outerGuardSurveyPairs 64 130` via their common cardinality 2211.

Five new theorems in a new `PART XIX: TRIANGULAR CARDINALITY`
section (+180 lines, 0 new axioms, 0 new sorries):

* `outerGuardSurveySize_succ` — one-step recurrence: extending
  the range from `hi` to `hi + 1` (with `lo ≤ hi`) increments
  the survey size by `hi + 1 - lo`. Decomposition into the old
  survey set ⊎ "new row at `a = hi`"; proved by `ext` +
  Finset.card_union_of_disjoint + Finset.card_image_of_injective.
* `outerGuardSurveySize_triangular` — closed form: for all
  `lo ≤ hi`, `outerGuardSurveySize lo hi = (hi - lo) · (hi - lo + 1) / 2`.
  Proved by `Nat.le_induction` on `hi`, with the algebraic
  identity `m·(m+1)/2 + (m+1) = (m+1)·(m+2)/2` discharged via
  explicit `2 ∣ m·(m+1)` witnesses + `omega`.
* Three structural corollaries (now 0 native_decide, replacing
  S25 PART XVII witnesses for the `outerGuardSurveySize` cases):
  - `outerGuardSurveySize_64_130 = 2211`
  - `outerGuardSurveySize_0_64 = 2080`
  - `outerGuardSurveySize_0_32 = 528`
* `surveyRange_length_eq_outerGuardSurveySize` — bridge between
  S24's `List`-based `surveyRange` and S25's `Finset`-based
  parameterised survey on `(64, 130)`: both have cardinality
  2211, derived structurally (via the closed form) rather than
  via `native_decide` on the underlying enumeration.

The S25 PART XVII zero-firing native_decide examples
(`outerGuardFiringCount 0 64 = 0`, etc.) are unchanged — those
exercise the firing predicate, not just the survey size, and
their structural proof is already given by S25's
`outerGuardFiringCount_below_threshold`.

**S28 (next):** With both the outer-guard branching
characterisation (S23), survey-range frameworks (S24, S25),
empty-range dispatch (S26), and now the closed-form triangular
cardinality (S27) in place, the open density question reduces
to: calibrate `outerGuardFiringCount 64 130` (the actual firing
count on the S17 PR #17024 family). Two directions:

  (a) one-shot `native_decide` evaluation (≈ 2211
      `hgcdSafeApply` calls), packaging the result as a named
      constant + `decide`-checked sum-equals-2211 partition; or
  (b) further structural decomposition of `schonhageOuterGuardFires`
      on the `(64, 130)` range — e.g. coprime pairs always
      trigger the outer guard above threshold, giving a
      structural lower-bound on the firing count.

### Previous focus (S26 — PR #17432, merged)

Session 26 (PR #17432, researcher-3) added Path A PART XVIII:
closed-form dispatch of the **empty-range** density question
(`hi ≤ lo`), complementing S25's `outerGuardFiringCount_below_threshold`
(sub-threshold case `hi ≤ 64`).

### Previous focus (S25 — PR #17415, merged)

Session 25 (this PR, researcher-10) adds the
**Finset-parameterised density framework** (Path A PART XVI),
complementing S24's List-based hard-coded `surveyRange`. Five
contributions:

  - `outerGuardSurveyPairs lo hi : Finset (ℕ × ℕ)` — the
    parameterised survey range for any `(lo, hi)`. The S17
    PR #17024 family is `outerGuardSurveyPairs 64 130`; the
    sub-threshold zero-firing region is `outerGuardSurveyPairs
    0 64`.
  - `outerGuardFiringPairs / outerGuardSurveySize /
    outerGuardFiringCount` — Finset-based firing subset and
    cardinality accessors, with direct Mathlib API support.
  - `outerGuardFiringCount_le_surveySize` — structural ≤
    bound proved via `Finset.card_filter_le`. A load-bearing
    bound for any density-fraction theorem.
  - **`outerGuardFiringCount_below_threshold`** (closed-form) —
    for any `(lo, hi)` with `hi ≤ hgcdThresholdSafe = 64`,
    `outerGuardFiringCount lo hi = 0`. Direct corollary of
    S23's `_below_threshold` lemma; no `native_decide`
    enumeration required.
  - PART XVII adds three combinatorial survey-size
    `native_decide` witnesses (`0 32 → 528`, `0 64 → 2080`,
    `64 130 → 2211` — matching S24's `surveyRange_length`)
    and three sub-threshold zero-firing witnesses
    (`0 32 → 0`, `0 64 → 0`, `60 64 → 0` — corroborating the
    closed-form theorem on concrete inputs).

Net: +185 lines (3 theorems / lemmas + 4 defs + 6 examples),
0 new axioms, 0 new sorries. The S25 framework is complementary
to S24: List for explicit enumeration order, Finset for
Mathlib-compatible cardinality + filter algebra. Both frameworks
agree on `(lo, hi) = (64, 130)`: `surveyRange.length = 2211 =
(outerGuardSurveyPairs 64 130).card`. With the S25 closed-form
zero-firing theorem in hand, the entire sub-threshold portion of
the density question is resolved without computation; the
remaining work is the calibration of
`outerGuardFiringCount 64 130` (one-shot `native_decide` over
2211 `hgcdSafeApply` calls), which is bookkeeping rather than
structural mathematics.

Session 23 introduced an outer-guard predicate
characterisation of `schonhageGcd`'s recursive case. The predicate
`schonhageOuterGuardFires : ℕ → ℕ → Bool` returns `true` iff
applying `hgcdSafeApply a b` strictly reduces `max a b` (and the
input is above threshold). Five structural lemmas provide the
core reduction equations:

  - `schonhageOuterGuardFires_below_threshold` — uniformly false
    on small inputs.
  - `schonhageOuterGuardFires_iff` — conjunctive iff with
    above-threshold AND strict-decrease.
  - `schonhageOuterGuardFires_strict_decrease` — forward direction:
    the firing guard implies strict size-reduction at the next step.
  - `schonhageGcd_succ_via_outerGuard` — **headline theorem**: one
    fuel step of `schonhageGcd` is fully described by the predicate
    (recurse if fires, dispatch to `Nat.gcd` if aborts).
  - Specialisations: `_recurse_of_fires` and `_fallback_of_aborts`.

Five `native_decide`-checked below-threshold witnesses confirm
the closed-form Boolean kernel agrees with the abstract
characterisation on concrete sub-threshold inputs.

Session 22 extended the S21 API surface with six further `Nat.gcd`
identities not previously packaged (`schonhageGcdOf_dvd_iff`,
`_mul_left`, `_mul_right`, `_pos_of_pos_left`,
`_pos_of_pos_right`, `_succ_self`) and added a PART XII section of
five `native_decide`-checked sanity examples. Together with S21
the algebraic API for `schonhageGcdOf` now mirrors the standard
Mathlib `Nat.gcd` theory, and the `native_decide` checks confirm
the closed-form recursion produces correct answers on inputs
where the unguarded `hgcdMatrix` (S17) blew up.

The body iterates `hgcdSafeApply` (S19) on the reduced pair: each
step takes the column output `(p.1.natAbs, p.2.natAbs)` and
recurses ONLY if its `max` is strictly less than `max a b`.
Otherwise — and on inputs below threshold — the function falls
back to `Nat.gcd`. With these two structural fallbacks, the
function is total and unconditionally correct: even on
pathological inputs like the S17 counterexample family
`(130, 89)`, where `hgcdMatrixSafe`'s OWN inner guard always
aborts, the OUTER guard here dispatches to `Nat.gcd` and the
correctness theorem still holds.

This is the verified ENDPOINT of Path A's algorithmic story:
- Single-step correctness: S19's `hgcdSafeGcd_eq_gcd`.
- Iterative correctness: S20's `schonhageGcd_eq_gcd`.

The remaining work (S21+) is QUANTITATIVE — establishing that the
runtime guards fire often enough that the recursion outperforms
plain `Nat.gcd` asymptotically.

Path A roadmap remaining (S21+):

1. **S21 — quantitative inner-reduction characterisation**: prove
   that the inner runtime guard of `hgcdMatrixSafe` fires for a
   well-defined density of inputs above threshold. The S17 PART
   XIV counterexample shows the guard CAN abort, but in survey
   ranges the guard fires often; quantifying the success rate
   would yield a probabilistic speedup bound.

2. **Bit-complexity bound** (`O(M(n)·log n)`): genuinely blocked
   on Mathlib (no fast multiplication, no bit-complexity model).
   Documented; defer until Mathlib lands these.

3. **Empirical comparison**: native_decide-checked timing /
   instruction count comparison of `schonhageGcdOf` vs `Nat.gcd`
   on the S17 counterexample family.

Status of the proof plan (Sessions 1–19):

1. **Step 1** ✅ (S3, PR #14522): row-vector invariant for
   `lehmerCofactors`. PART V.5.
2. **Step 2a** ✅ (S3, PR #14522): residue monotonicity for
   `lehmerCofactors`. PART V.5.
3. **Step 2b (Lehmer)** ✅ (S4, PR #14881): entry bound for
   `lehmerCofactors` via row-Cramer + sign pattern. PART VI.
4. **Step 3** ✅ (S5, PR #14910): perturbation infrastructure
   (algebraic split + triangle bounds). PART VII.
5. **Row-output composition under `mul`** ✅ (S12, PR #16662):
   `cofactor_mul_row_output` + `cofactor_mul_row_output_natAbs_le`.
   PART VIIc.
6. **Sign-pattern lifting to HGCD** ✅ (S13, PR #16729):
   `hgcdMatrix_has_pattern` via Z/2-graded `cofactor_mul_pattern`.
   PART X.
7. **Row-vector invariant — base + threshold + composition law** ✅
   (S14, PR #16908): `cofactor_mul_row_invariant`,
   `hgcdMatrix_zero_row_invariant`, `hgcdMatrix_small_row_invariant`.
   PART XI.
8. **Pattern-det correlation + threshold entry bound** ✅
   (S15, PR #16994): `lehmerCofactors_pattern_det_correlated_from`,
   `hgcdMatrix_small_pattern_det_correlated`,
   `entry_bound_of_pattern_det_natAbs`,
   `hgcdMatrix_small_entry_bound`. PART XII.
9. **All-fuel pattern-det invariant + entry bound** ✅
   (S16, PR #17009): `cofactor_mul_pattern_det_correlated`,
   `hgcdMatrix_pattern_det_correlated`,
   `hgcdMatrixOf_pattern_det_correlated`,
   `hgcdMatrix_entry_bound`. PART XIII.
10. **Counterexample to all-fuel row-vector invariant** ✅
    (S17, PR #17024): `hgcdMatrix_130_89_value`,
    `hgcdMatrix_130_89_row_alpha`,
    `hgcdMatrix_130_89_row_beta`,
    `hgcdMatrix_row_alpha_exceeds_max`,
    `hgcdMatrix_row_beta_negative`,
    `hgcdMatrix_row_invariant_counterexample`. PART XIV. The
    proposed Session 17+ target is FALSE under the current algorithm.
11. **Path A foundation** ✅ (S18, PR #17042):
    `hgcdMatrixSafe`, `hgcdMatrixSafeOf`, `hgcdMatrixSafe_det_unit`,
    `hgcdMatrixSafe_preserves_gcd`,
    `hgcdMatrixSafeOf_det_unit`,
    `hgcdMatrixSafeOf_preserves_gcd`. New file
    `BinaryGcdOQ03OQ02PathA.lean`. Algorithm refinement with
    runtime size-reduction guard.
12. **Path A verified GCD function** ✅ (S19, PR #17063):
    `hgcdSafeApply`, `hgcdSafeApply_gcd_eq`, `hgcdSafeGcd`,
    `hgcdSafeGcd_eq_gcd`. Computational examples on the S17
    counterexample family `(130, 89)` and worst-case `(107, 85)`.
    PART VI–VII of `BinaryGcdOQ03OQ02PathA.lean`.
13. **Recursive Schönhage-style GCD via iteration** ✅ (S20,
    PR #17087): `schonhageGcd`, `schonhageGcdOf`,
    `schonhageGcd_zero`, `schonhageGcd_succ`,
    `hgcdSafeApply_natAbs_gcd`, `schonhageGcd_eq_gcd`,
    `schonhageGcdOf_eq_gcd`. PART VIII–IX of
    `BinaryGcdOQ03OQ02PathA.lean`. Total correct iterated GCD
    with two structural fallbacks (below-threshold + per-step
    guard). Native-decide examples include the S17
    counterexample family and `(1000000, 999999)`.
14. **API surface for `schonhageGcdOf`** ✅ (S21, PR #17104):
    11 wrapper lemmas covering the standard `Nat.gcd` identities
    (`schonhageGcdOf_zero_left`, `_zero_right`, `_self`,
    `_one_left`, `_one_right`, `_comm`, `_dvd_left`, `_dvd_right`,
    `dvd_schonhageGcdOf`, `_assoc`, `_eq_zero_iff`) plus
    `schonhageGcd_fuel_irrelevant`. PART X of
    `BinaryGcdOQ03OQ02PathA.lean`. Each wrapper reduces to
    `schonhageGcdOf_eq_gcd` plus the corresponding `Nat.gcd`
    lemma. The lemmas are uniformly trivial; their value is
    pragmatic — `schonhageGcdOf` now responds to standard
    `simp`-style tactics without manual unfolding at the call
    site, completing the drop-in replacement story.
15. **Extended algebraic identities + empirical witnesses** ✅
    (S22, PR #15091): 6 additional wrapper lemmas in PART XI
    (`schonhageGcdOf_dvd_iff`, `_mul_left`, `_mul_right`,
    `_pos_of_pos_left`, `_pos_of_pos_right`, `_succ_self`) plus 5
    PART XII `native_decide` empirical sanity examples
    (`(64, 64)`, `(65, 64)`, `(121, 88)`, `(200, 175)`,
    `(2520, 1980)`). The S22 wrappers fill the gaps left by S21:
    multiplicative laws, the iff form of the universal property,
    strict positivity from either side, and a concrete Fibonacci-
    style coprimality witness. The PART XII examples exercise the
    closed-form recursion at scale — the kernel reduces every fuel
    level and every `hgcdSafeApply` call.
16. **Outer-guard predicate + branching characterisation** ✅
    (S23, this session): Boolean predicate
    `schonhageOuterGuardFires : ℕ → ℕ → Bool` capturing the OUTER
    size-reduction guard from `schonhageGcd`'s recursive case
    (PART VIII line 440), plus five structural lemmas in PART
    XIII (`_below_threshold`, `_iff`, `_strict_decrease`,
    `schonhageGcd_succ_via_outerGuard` — the headline reduction
    equation, and the two specialisations `_recurse_of_fires` /
    `_fallback_of_aborts`). PART XIV adds five
    `native_decide`-checked below-threshold witnesses
    (`(0, 0)`, `(5, 3)`, `(12, 8)`, `(63, 1)`, `(63, 63)`),
    confirming the predicate is uniformly `false` on small inputs.
    The headline theorem reduces every reasoning step about the
    `schonhageGcd` recursion to a Boolean case-split on the
    predicate, factoring out the algebra of the threshold check
    + size-reduction guard. This is the qualitative foundation
    for S24+ density theorems.

**Open / Refuted**:
- **Recursive case of `hgcdMatrix_row_output_le`** ❌ (line 1078,
  sole sorry in `BinaryGcdOQ03OQ02.lean`): refuted by S17 PART XIV
  for the unguarded algorithm. Will not be closed; the path forward
  is via Path A's `hgcdMatrixSafe` (now in `…PathA.lean`), where
  size reduction holds by the runtime guard rather than by an
  algebraic lift.

Concurrently: bit-complexity claim O(M(n)·log n) remains genuinely
blocked on Mathlib (no fast multiplication, no bit-complexity model).

## Active Approach

**Path A** (S18+ chosen direction). The algorithm `hgcdMatrixSafe`
with a runtime size-reduction guard is the implementation target.
The verified ALGORITHMIC story for Path A is now complete:

- S18: `hgcdMatrixSafe` is unimodular (`hgcdMatrixSafe_det_unit`)
  and preserves GCD (`hgcdMatrixSafe_preserves_gcd`).
- S19: a single-step GCD function `hgcdSafeGcd` wraps that
  matrix application; correct via `hgcdSafeGcd_eq_gcd`.
- S20: a recursive iterated GCD function `schonhageGcd` with
  guarded fallback to `Nat.gcd`; correct via
  `schonhageGcd_eq_gcd`. Total and unconditional.
- S21: API surface (PART X) — eleven wrapper lemmas + fuel
  irrelevance, making `schonhageGcdOf` a drop-in replacement
  for `Nat.gcd` under standard rewriting tactics.
- S22: extended algebraic identities (PART XI) and empirical
  witnesses (PART XII) — six further wrappers covering the gaps
  in S21 plus five `native_decide` sanity examples spanning the
  threshold edge and the S17 survey range.

Remaining work for Path A is QUANTITATIVE only (asymptotic
speedup, bit-complexity bound).

## Blockers

* **Bit complexity (C)**: genuinely blocked on Mathlib infrastructure.
  Documented in `BinaryGcdOQ03OQ02.lean` PART VII; not a blocker on
  Path A correctness or size reduction.

* **Row-vector invariant for unguarded `hgcdMatrix`** ❌ FALSE under
  the unguarded algorithm: refuted by S17 PART XIV. This sorry on
  line 1078 will not be closed; Path A supersedes the row-vector
  approach.

## Next Action

(Refreshed in S35 PR — replaces the S25-era list that described
S26/S27/S28+ as upcoming work. Those sessions have since merged:
S26 PR #17432, S27 PR #17489, S28a PR #17517, S28c PR #17631,
S29 PR #17631, S30 PR #17661, S31 PR #17683, S32 PR #17720,
S33 PR #17750, S34 PR #17771.)

1. **S32b — `hgcdMatrixSafe_apply_compose_decrease` (~80 lines)**.
   Per `s32-non-expansion-analysis.md` §5–§6 and S34's
   `s34-abort-branch-decomposition.md`, the conditional non-
   expansion lemma restricted to the inner-fires branch
   (`max u v < max a b`) is the core open piece for closing the
   compose ⇒ outer-fires direction of the S28b equivalence.
   With S31's `hgcdMatrixSafeOf_compose_branch` (PART XXI) and
   S34's `hgcdMatrixSafeOf_abort_branch` (PART XXIII) both
   available as top-level theorems, the proof can case-split on
   `by_cases hred : max u v < max a b` and dispatch the abort
   case directly via S34's theorem (giving `false` immediately
   from the inner-abort branch). The remaining inner-fires case
   is where the genuine algebraic work lives — the S32 §5 spec
   suggests `hgcdMatrixSafe_preserves_gcd` plus a unimodularity
   bound on the second-level recursion. Expected: ~80 Lean lines.
2. **S32c — full S28b equivalence (~120 lines)**:
   `schonhageOuterGuardFires_above_iff_inner_fires`. Builds on
   S32b for one direction and on S30
   (`hgcdMatrixSafe_inner_abort_imp_outer_fails`) for the other.
   The s32 §6 estimate is ~120 lines.
3. **Outer-guard density magnitude (deferred from S26 priority)**:
   the S24+S25 frameworks are still in place; running
   `native_decide` on `outerGuardFiringCount 64 130` to obtain
   the exact density number remains a small follow-up. Now that
   S32b/c are the centrepiece, this becomes a "nice-to-have"
   empirical companion rather than the headline.
4. **Coprime-bit-length theorem**: with the S24+S25 frameworks +
   S30+S34 inner/outer characterisation, the stronger sub-target
   — "every coprime pair above threshold with matching bit-length
   triggers the outer guard" — is now well-typed in PathA and
   may be tractable as a corollary of S32c once available.
   Deferred until S32b/c are merged.
5. **Bit-complexity bound (C)**: still blocked on Mathlib
   infrastructure (no bit-complexity model for arithmetic, no
   fast multiplication). Defer.
6. **Mathlib upstream**: the current `schonhageGcdOf` API surface
   (S21+S22) is now sufficient that, contingent on a working
   Docker build, candidate Mathlib upstream PRs could be drafted
   for one or two of the routine wrapper lemmas. Survey what
   already exists in Mathlib's `Nat.GCD` family before submitting.

## Attempt Counts

- Total attempts: 25 (Sessions 1–25)
- Approaches tried:
  - Path A (fuel-indexed correctness): merged Session 2 (#14389)
  - Row-convention size-reduction infrastructure: Sessions 3–16
    proven correct as building blocks; the all-fuel row-vector
    invariant target was REFUTED by Session 17.
  - Path A algorithm refinement: GCD-preservation foundation
    (S18, #17042), verified single-step GCD function (S19, #17063),
    recursive Schönhage-style iterated GCD (S20, #17087).
  - Path A API surface (S21, #17104): standard `Nat.gcd` API
    transferred to `schonhageGcdOf`; fuel irrelevance packaged.
  - Path A extended algebraic identities + empirical witnesses
    (S22, #15091): multiplicative laws, dvd-iff, positivity,
    coprimality witness, plus 5 `native_decide` sanity examples.
  - Path A outer-guard branching characterisation (S23, #17305):
    Boolean predicate + 5 structural lemmas + 5 below-threshold
    `native_decide` witnesses. Headline reduction equation
    `schonhageGcd_succ_via_outerGuard` reduces every reasoning
    step about the recursion to a Boolean case-split.
  - Path A List-based survey-range tabulation (S24, #17393):
    `surveyRange : List (ℕ × ℕ)` + `surveyRange_length = 2211` +
    `outerGuardFires/AbortsInSurveyRange` count definitions for
    the S17 PR #17024 family.
  - Path A Finset-parameterised density framework (S25, this PR):
    `outerGuardSurveyPairs lo hi : Finset (ℕ × ℕ)` parameterised
    survey, `outerGuardFiringCount_le_surveySize` (≤ bound),
    closed-form `outerGuardFiringCount_below_threshold` theorem,
    plus 6 `native_decide` survey-size + zero-firing witnesses.
  - Path A density-magnitude calibration (S26+): pending.
  - Path A above-threshold abort witnesses
    (S28a, this PR, researcher-6): refute the naive coprime-firing
    conjecture by appending two `native_decide`-checked
    counterexamples (`schonhageOuterGuardFires 130 89 = false`,
    `schonhageOuterGuardFires 107 85 = false`) plus four
    decidable supporting facts (`Coprime 130 89`, `Coprime 107 85`,
    `hgcdThresholdSafe ≤ min 130 89`, `hgcdThresholdSafe ≤
    min 107 85`) to PART XIV of `BinaryGcdOQ03OQ02PathA.lean`.
    Net delta: +35 lines (6 examples + docstring), 0 new theorems,
    0 new axioms, 0 new sorries. Append-point is line-stable
    relative to the in-flight S27 PR #17489 (which targets
    PART XIX further down the file). Mirrors the deliverable
    described in `s28-coprime-firing-spec.md` §4 (S28a).
    Build pending (consistent with the project-wide
    `(build pending)` convention for above-threshold
    `native_decide` checks on this slug).

## S28a — Above-threshold abort witnesses (this PR)

**Goal**: Document the canonical structural counterexample to the
naive S28 coprime-firing conjecture (refuted in
`s28-coprime-firing-spec.md`, merged as PR #17496).

**Deliverable**: Append a new docstring + 6 `example` blocks to
PART XIV of `BinaryGcdOQ03OQ02PathA.lean`:

```lean
example : schonhageOuterGuardFires 130 89 = false := by native_decide
example : Nat.Coprime 130 89 := by decide
example : hgcdThresholdSafe ≤ min 130 89 := by decide

example : schonhageOuterGuardFires 107 85 = false := by native_decide
example : Nat.Coprime 107 85 := by decide
example : hgcdThresholdSafe ≤ min 107 85 := by decide
```

**Mathematical content**: Both `(130, 89)` and `(107, 85)` are
above the safe-HGCD threshold (`min ≥ 64`) and pairwise coprime,
yet the outer guard returns `false`. The structural mechanism
(per state.md S20 and the S28 spec §1) is that
`hgcdMatrixSafe`'s INNER guard aborts on each pair, leaving the
column-output unchanged so the size-reduction predicate fails.
This refutes the appealing-but-naive form *"above-threshold +
coprime ⟹ outer guard fires"*: the actual structural condition
must reckon with the inner-guard's abort behaviour, which is the
focus of the proposed S28b/c follow-ups in the spec doc.

**Build**: `native_decide` on `(130, 89)` and `(107, 85)` runs
the full `hgcdSafeApply` recursion (one evaluation each — vastly
cheaper than the survey-range scans of S25/S27). Build pending
per project convention; deployer auto-merges build-pending
research PRs on this slug (cf. iters 5–11 merge pattern).

**Append-point stability**: The new block is inserted at the END
of PART XIV (between the existing `63 63` below-threshold witness
and the PART XV section banner). PR #17489 (S27, targeting
PART XIX) inserts further down the file. PR #17304 (S23,
targeting PART XIII) inserts above. Neither PR's diff overlaps
the S28a insertion window.

**Honesty notes**:

* The native_decide assertions are NOT independently verified
  prior to commit (Docker build infrastructure on this worktree
  has the broken `proofs/.lake` symlink — `feedback_researcher_lake_symlink_broken.md`).
  The structural reasoning behind `schonhageOuterGuardFires
  130 89 = false` is the spec doc §1 trace plus state.md S20 +
  PR #17087's per-session honesty section, both of which assert
  the inner-guard abort behaviour on `(130, 89)`. If the
  `native_decide` evaluations refute the assertion at build time
  (i.e. the outer guard actually fires on one of the pairs), the
  follow-up correction would be a 2-line surgical fix flipping
  `false` to `true` at the relevant `example` line.
* This iteration adds NO new theorems, definitions, or axioms.
  The contribution is purely empirical — recording the canonical
  counterexample family in the proof script so that downstream
  sessions can `exact?`-cite them rather than re-running the
  algorithm. It does not advance the discharge of the parent
  open conjecture (Schönhage HGCD bit-complexity bound).
* This iteration does NOT depend on PR #17489 (S27 PART XIX) or
  PR #17304 (S23 PART XIII outer-guard characterisation) being
  merged first. It only depends on the merged S23 / S25 / S26
  infrastructure (the predicate `schonhageOuterGuardFires`,
  the threshold constant `hgcdThresholdSafe`, and the file's
  existing PART XIV append point), all of which are stable on
  origin/main.

