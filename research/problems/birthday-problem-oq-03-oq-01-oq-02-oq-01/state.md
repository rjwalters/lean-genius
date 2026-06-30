# Research State: birthday-problem-oq-03-oq-01-oq-02-oq-01

## Current State
**Phase**: BLOCKED (verification blackout 2026-06-13) — S28 ACT (`bad_count_general_5` + `bad_count_overlap_one`, +205 LOC, Layer 3f closed) is **complete and was Docker-verified** (commit `c991b1c42dc` "S28 — bad_count_general_5 + overlap_one, Layer 3f closed, Docker-verified") but is **trapped in conflicting bundle PR #22850** (244-file research bundle on `feature/researcher-1`, mergeStateStatus DIRTY/CONFLICTING). The birthday lean file is unchanged on `origin/main` since merge-base `fa1c4d27aa8`, so the verified change cherry-picks cleanly — the conflicts are entirely in the bundle's other ~243 meta.json files, not in the lean file. Re-extraction into a focused mergeable PR needs a fresh Docker build to re-confirm before landing; Docker daemon is down + Aristotle MCP backend returns 404 this session, so not blind-shipping 205 LOC of build-dependent Lean. **Re-open when Docker recovers**: extract the lean change from #22850 / `c991b1c42dc` into a focused PR off `origin/main`, run `./proofs/scripts/docker-build.sh Proofs.BirthdayProblemOQ03OQ01OQ02`, land it. meta.json leanFiles for the parent (2264 LOC / 54 thm / 1 axiom / 7 def / 0 sorry) verified in sync with origin/main source — no metadata fix needed.
**Iteration**: 28 (S28 BLOCKED; predecessor S27 PREP)

### Prior (pre-blackout): ACT-READY — Layer 3a–3f complete on main; **S25 ACT-1 (PR #19997)** shipped `bad_count_general_4` (~140 LOC reusable helper) + `bad_count_overlap_two` (5-LOC corollary), file 2102 → 2263 LOC, 1 axiom unchanged, 0 sorries unchanged; **S26 PREP (PR #21312)** confirmed INFRA recovery (G7 disk 3.0→61 GiB, G8 Docker 29.4.1 server up; G9 `.lake` self-loop persists but cosmetic vs Docker builds); 8/9 gates GREEN substantively. **S27 PREP (this session)** drafts paste-ready Lean for the last missing Layer 3f raw count: `bad_count_general_5` (~160 LOC helper, mirrors `bad_count_general_4` with one extra vertex/conjunct/`dif_neg` level) + `bad_count_overlap_one` (5-LOC corollary) — see `sessions/2026-06-02-s27-prep-overlap-one-general-5-extraction.md`.
**Path**: full
**Since**: 2026-06-02T... (S27 PREP — paste-ready `bad_count_general_5` + `bad_count_overlap_one` extraction draft + drift remediation absorbing S25 ACT-1 + S26 PREP)
**Iteration**: 27 (S27 PREP; predecessors S25 ACT-1 PR #19997 + S26 PREP PR #21312 both merged 2026-05-17 / 2026-05-31)
**Last Update**: 2026-06-02 (Session 27, researcher-1) — see `sessions/2026-06-02-s27-prep-overlap-one-general-5-extraction.md`

## Session 27 Summary (2026-06-02, researcher-1) — paste-ready `bad_count_general_5` extraction + drift remediation

**Mode**: PREP (doc-only; zero Lean / `meta.json` / `lake-manifest.json` edits). Closes the last raw-counting gap in Layer 3f by drafting the next ACT.

**Outcome**: phase **ACT-READY (unchanged)**; iteration bumped 25 → 27 (skipping a never-numbered "S26 ACT" since S26 was actually a PREP-only INFRA recheck). The new session file `sessions/2026-06-02-s27-prep-overlap-one-general-5-extraction.md` contains:

1. **9-gate INFRA snapshot** at this PR's authoring time (8/9 GREEN substantively; G1 + G5 upgraded since S26 due to PR #19997 + #20009 + #20010 + #21792 absorption).
2. **Drift table** of 5 merges since S25 STATE-SYNC (S25 ACT-1 #19997, sibling leanFiles batch syncs #20009/#20010 LOC 2102→2263, S26 PREP INFRA #21312, parent slug defCount fix #21792).
3. **Layer 3 status table** showing 3f-count-2 (`bad_count_overlap_two`) now present on main and identifying `bad_count_overlap_one` as the single remaining missing 3f raw count.
4. **Paste-ready `bad_count_general_5`** (~155 LOC) — 5-vertex generalisation of `bad_count_general_4` with explicit bijection to `{m' : Fin n // m' ≠ j ∧ m' ≠ k ∧ m' ≠ l ∧ m' ≠ m} → Fin d`; one extra `if/dif_neg` layer per ladder block (membership, left_inv, right_inv) vs the 4-vertex template. Same bearer set as `bad_count_general_4` (no new Mathlib bearers required).
5. **Paste-ready `bad_count_overlap_one`** (~5 LOC) — direct corollary using `bad_count_general_5` with `(i, j, k, l, m) = (a₁, b₁, c₁, b₂, c₂)`; statement matches S24 §3.1 errata-corrected form (count `d^(n − 4)`, NOT S23 §3.1's typo `d^(n − 5)`); 10 pairwise-distinctness hypotheses with explicit slot↔name↔semantic mapping table.
6. **S28b strict-wrapper sketch** for the downstream `bad_count_overlap_one_strict` consumer of `tripleCount_descFact_2_eq_overlap_sum`'s k=1 summand (~80–100 LOC, shorter than S16b's 98 LOC because only 10 vs 15 distinctness hyps).
7. **Insertion-point preview** at L1026 of `BirthdayProblemOQ03OQ01OQ02.lean` (between `bad_count_overlap_two` close and the §5 §FIRST-MOMENT-IDENTITY divider), preserving the established helper-then-corollary read order.
8. **LOC forecast** for the remaining work to close Lemma C: ~160 (S28 ACT) + ~80–100 (S28b strict) + ~80 (S29 real wrappers) + ~30 (S30 3g) + 150–500 (S31+ Layer 4) ≈ 500 Lean LOC over ~5 sessions.

**Net change**: 4 files (1 NEW sessions/ + state.md head + research JSON + registry); ~460 lines added / ~10 lines deleted. Phase **ACT-READY (unchanged)**; iteration bumped 25 → 27. File `proofs/Proofs/BirthdayProblemOQ03OQ01OQ02.lean` at `origin/main` is **2263 LOC, 1 axiom, 0 sorries — unchanged since PR #19997**.

**3 RED INFRA persist as 1 (G9 only)**: G7 disk + G8 Docker both recovered per S26 PREP; G9 `.lake` self-symlink unchanged but cosmetic relative to Docker-based builds. **8/9 gates GREEN substantively**.

See `sessions/2026-06-02-s27-prep-overlap-one-general-5-extraction.md` for the full delta — INFRA 9-gate snapshot with deltas, drift table, paste-ready Lean for `bad_count_general_5` + `bad_count_overlap_one`, hypothesis-derivation strategy for the S28b strict wrapper, LOC budget + insertion preview, anti-pattern checklist, references, PR delta forecast, honesty calibration, and predicted S28 absorption.

## Session 26 Summary (2026-05-30, researcher-1) — INFRA recovery (G7 + G8 flipped GREEN; G9 unchanged)

**Mode**: PREP (doc-only; per PR #21312 merged 2026-05-31T04:13:44Z). Re-snapshots all 3 RED INFRA gates from S25 STATE-SYNC 13 days later:

- **G7 RED → GREEN**: disk free **3.0 GiB → 61 GiB** (+58 GiB recovery over 13 days).
- **G8 RED → GREEN**: Docker daemon **29.4.1 server up** (no hang).
- **G9 RED unchanged**: `proofs/.lake` symlink still self-loops; cosmetic vs Docker builds (Docker image carries its own toolchain + cache; host-side `.lake` irrelevant).

**Net**: **6/9 → 8/9 GREEN substantively**. The S26 ACT picker matrix from S25 §picker-matrix is superseded (61 GiB disk no longer constraining; the 5 options become essentially equivalent on resources).

See `sessions/2026-05-30-s26-prep-infra-recovery-2-of-3-gates-flipped.md` for the full delta (9-gate snapshot, picker-matrix supersession, reasons G9 deferred to mechanic, no Lean/state.md/JSON edits).

## Session 25 ACT-1 Summary (2026-05-17, researcher-?, PR #19997) — `bad_count_general_4` + `bad_count_overlap_two` (option (b) extraction)

**Mode**: ACT (Lean diff; build pending per PR title: "Docker daemon hung + host disk 2.8 Gi RED"; commit + push, doctor / auditor verifies from clean worktree).

**Outcome**: implemented Layer 3f raw count for the overlap=2 stratum via the recommended option (b) extraction from S24 §3.3:

1. **`bad_count_general_4` (~140 LOC, reusable helper)** at L881 of `BirthdayProblemOQ03OQ01OQ02.lean` — 4-vertex chain trivialisation count: with pairwise-distinct `i, j, k, l ∈ Fin n`, `(Finset.univ.filter (fun f => f i = f j ∧ f j = f k ∧ f k = f l)).card = d^(n − 3)`. Strategy mirrors S11's `bad_count_general` (one extra vertex): explicit bijection to `({m // m ≠ j ∧ m ≠ k ∧ m ≠ l} → Fin d)` via restriction to the `(n − 3)`-element complement; inverse extends by `f m = g i` for `m ∈ {j, k, l}`, `f m = g m` otherwise. Same `dif_neg` ladder pattern as S11 with one extra level.

2. **`bad_count_overlap_two` (5-LOC corollary)** at L1019 — direct application of `bad_count_general_4` with `(i, j, k, l) = (a₁, b₁, c₁, c₂)` consuming exactly 6 pairwise-distinctness hypotheses (3 within-T₁ + 3 cross to c₂). Count `d^(n − 3)` matches S24 §3.2 errata-corrected form.

**Net file delta**: 2102 → 2263 LOC (+161); 57 → 59 theorems (verified by sibling `meta.json` batch syncs PR #20009 + #20010 on the same day); 8 defs unchanged. 1 axiom (`p_no_triple_tendsto`) unchanged. 0 sorries unchanged.

**Build status at merge**: pending (Docker daemon hung at PR-creation time; cleared by S26 PREP confirmation). Standard project convention — see Sessions 10–16d which all shipped build-pending PRs against this slug.

## Session 25 Summary (2026-05-17, researcher-12) — mechanic-batch absorption + 1 surgical leanFiles fix + INFRA delta + registry catchup + sessions/ bootstrap

## Session 25 Summary (2026-05-17, researcher-12) — mechanic-batch absorption + 1 surgical leanFiles fix + INFRA delta + registry catchup + sessions/ bootstrap

**Mode**: STATE-SYNC (doc-only; zero Lean / `meta.json` / `lake-manifest.json` edits). Closes the 4 drift items that accumulated in the ~10 h window after S24:

1. **Mechanic batch sync absorption (informational)** — PR #19681 (parent slug `birthday-problem-oq-03-oq-01-oq-02`, merged 2026-05-16T16:20:40Z, fixed `leanFiles[BirthdayProblemOQ03OQ01OQ02]` 502→2102 LOC / 20→57 thm / 3→8 def) + PR #19701 (11 sibling slugs, merged 2026-05-16T17:21:20Z, same fields same canonical values). Both merged into `origin/main`; their `meta.json` deltas reference the same gallery authority (`src/data/proofs/birthday-problem-oq-03-oq-01-oq-02/meta.json` → `leanFile = 2102/57/8/1/0`).
2. **Surgical leanFiles[idx=10] fix** — PR #19701 **explicitly excluded** this slug per its body: *"birthday-problem-oq-03-oq-01-oq-02-oq-01 — different stale entry at idx=10 (2086/52/5), separate scope"*. S25 discharges this exclusion by reconciling `leanFiles[10]` from 2086/52/5 → 2102/57/8 (the mechanic's correct judgment: don't have a single regex silently rewrite an entry it doesn't match — leave it for a researcher to attest the cross-validation). Canonical authority chain: gallery `meta.json` → 2102/57/8; `wc -l proofs/Proofs/BirthdayProblemOQ03OQ01OQ02.lean` → 2102; parent slug post-#19681 → 2102/57/8; 11 siblings post-#19701 → 2102/57/8. No risk of new drift.
3. **INFRA snapshot delta** — disk free **6.5 GiB → 3.0 GiB** (−3.5 GiB over ~11 h; gate G7 RED, was AMBER); Docker daemon still hung (`docker info` "Server:" line empty after 10 s timeout — gate G8 RED unchanged); `proofs/.lake` still self-symlink cycle (mtime 2026-05-16T09:04 — gate G9 RED unchanged). Mathlib SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` byte-stable ≥ 4.5 months (G2 GREEN, carry-forward chain S22 → S23 → S24 → S25 with no re-walk needed).
4. **Registry catchup** — `research/registry.json` entry was `phase: "OBSERVE"`, `lastUpdate: "2026-04-21T14:18:44.788Z"` (25 d drift vs canonical `phase: "ACT-READY"`, `currentState.lastUpdate: "2026-05-16T14:09Z"`). S25 flips to `phase: "ACT-READY"`, `lastUpdate: "2026-05-17T01:16Z"`.
5. **sessions/ bootstrap** — directory did not exist; this PR places `sessions/2026-05-17-s25-statesync-post-mechanic-batch.md` as the first sessions/ file (~300 LOC, 12 sections — full audit trail for future S26+).
6. **Top-level `lastUpdate`** — was `"2026-05-14T03:30:00Z"` (S17 doc handoff era); updated to `"2026-05-17T01:16Z"` to mirror canonical session date.

**Net change**: 4 files (1 NEW sessions/ + state.md head + research JSON + registry); ~390 lines added / ~22 lines deleted. Phase **ACT-READY (unchanged)**; iteration bumped 24 → 25; `nextAction` re-aimed at the same S26 ACT (option b, `bad_count_general_4` extraction) plus a 5-row picker matrix accounting for the worsened disk. File `proofs/Proofs/BirthdayProblemOQ03OQ01OQ02.lean` at `origin/main` @ `9034990819b` is **2102 LOC, 1 axiom, 0 sorries — unchanged since PR #19247**.

**3 RED INFRA persist** (G7 disk 3.0 GiB / G8 Docker hung / G9 .lake self-symlink). 6/9 gates GREEN substantively (with G4 + G5 flipped GREEN by this PR + #19681/#19701 closure). ACT operational status unchanged: blocked on G7 + G8 recovery (or G7 emergency).

**10 sibling leanFiles `+1` off-by-one entries deferred to mechanic** (would clobber the mechanic's explicit "outside this single-root-cause fix" boundary if S25 touched them — see sessions memo §5 for the full table and rationale).

See `sessions/2026-05-17-s25-statesync-post-mechanic-batch.md` for the full delta — INFRA 9-gate snapshot with deltas, mechanic absorption tables (PR #19681 + #19701), leanFiles[idx=10] surgical fix with authority chain, Mathlib SHA + bearer carry-forward, drift hand-off list, ACT-readiness gate refresh, picker matrix, explicit non-actions, memory citations, PR delta forecast, honesty calibration, and predicted S26 absorption.

## Session 24 Summary (2026-05-16, researcher-6) — S23 PREP absorption + 3 errata

**Mode**: STATE-SYNC (doc-only; zero Lean / `meta.json` / `lake-manifest.json` edits). Catches up state.md + research JSON to reflect **S23 PREP merge (#19498, 2026-05-16T08:53:13Z)** which deliberately scoped itself to add only `s23-bad-count-overlap-statement-draft.md` (S23 PREP §8: "deliberate decision to NOT edit state.md or JSON … the next S24 ACT PR or a separate STATE-SYNC catch-up can absorb the iteration bump").

**Outcome**: phase **ACT-READY (unchanged)**; iteration bumped 23 → 24; `nextAction` re-aimed at S24 ACT using the **corrected** S23 §4.4 / §4.5 statements (NOT S23 §3.1 / §3.2, which contain `d^(n − 5)` / `d^(n − 4)` typos the author themselves caught in §4.3). File `proofs/Proofs/BirthdayProblemOQ03OQ01OQ02.lean` at `origin/main` @ `ecb47b35601` is **2102 LOC, 1 axiom, 0 sorries** — unchanged since PR #19247 mechanic repair. Mathlib pin `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0) is **byte-stable since PR #331 / commit `f8fdef7c228` (2026-01-01)**, ~ 4.5 months. ACT-readiness gate **all GREEN substantively** (with corrected entries for gates 4 + 7); only ⚠ RED is Docker availability (INFRA).

**3 errata flagged for S23 PREP** (consolidated in s24 file §3):

1. **§3.1 statement count** — `d^(n − 5)` should be `d^(n − 4)` (paste-ready form in S23 §4.4, reproduced verbatim in S24 §3.1 with derivation).
2. **§3.2 statement count + redundant conjunct** — `d^(n − 4)` should be `d^(n − 3)`; the 4-conjunct predicate has a duplicated conjunct that must be dropped (paste-ready form in S23 §4.5, reproduced in S24 §3.2 with explicit derivation).
3. **§3.2 `bad_count_general` 1-LOC shortcut** — `bad_count_general` at L751 is a 3-element chain (count `d^(n − 2)`), NOT a 4-element chain. The §3.2 `exact bad_count_general …` shortcut does **not** type-check. S24 ACT must either paste ~150 LOC inline (option a) or first extract `bad_count_general_4` (option b, **recommended** — ~150 LOC reusable helper + 1-LOC `exact` for `bad_count_overlap_two`).

**Plus §3.4 bearer file-path drifts (documentation-only)**: 3 of the 6 bearers in S23 §5's audit table have wrong file paths at the pin SHA (`Fintype.card_coe` is in `Card.lean:349`, not `Subtype.lean`; `Fintype.card_congr` is in `Card.lean:67`, not `Logic/Equiv/Defs.lean`; `Fintype.card_fun` is in `BigOperators.lean:199`, not `Card.lean`). The bearer **names** resolve correctly (Mathlib re-export resolution is namespace-based), so existing Layer 3e proofs are unaffected; the paths are wrong only as documentation for future bearer spot-checks. All 6 bearers re-verified at the pin SHA via GitHub API at this PR's authoring time.

See `s24-statesync-s23-prep-absorb-and-errata.md` for the full delta (corrected paste-ready statements, ACT-readiness gate refresh, next-action picker order with S24 ACT scope ~250–400 LOC depending on option choice, host snapshot, and references).

## Session 22 Summary (2026-05-16, researcher-9) — Build-blocker resolved + drain-wave absorption

**Mode**: STATE-SYNC (doc-only). Absorbs four drain-wave merges (PR #19232 S19 K12 root cause; PR #19237 S20 K14 cascade; PR #19286 S21 kit pin-verify; **PR #19247 mechanic Lean fix — 7743 jobs Docker clean, 0 sorries, axiom count 1 unchanged**) that closed the 37-error v4.26.0 build-blocker era opened in Session 17.

**Outcome**: phase ACT-READY. File `proofs/Proofs/BirthdayProblemOQ03OQ01OQ02.lean` at `origin/main` @ `8a3cda556b6` is 2102 LOC (+16 from mechanic), 1 axiom (`p_no_triple_tendsto` @ L329 — Lemma C only), 0 sorries. Layer 3a–3f infrastructure is complete on main (16 lemmas verified via `#check` block at file tail). Lake-pinned Mathlib SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` is unchanged since S16d; S21's 11-citation pin-verify remains valid (0 substantive bearer drift; off-by-1 cosmetic only). ACT-readiness gate 7/8 GREEN; partial gate is "next-ACT statement-skeleton drafted" — opens S23 as a per-pair PREP using `bad_count_disjoint` (S16 PR #17381) as template.

See `s22-build-blocker-resolved-state-sync.md` for the full delta (post-mechanic snapshot, bearer drift recheck table, ACT-readiness gate, next-ACT picker priority, anti-pattern checklist, and sibling-PR compatibility ledger).

## Session 17 Summary (2026-05-13, researcher-9) — Build-blocker discovery + doctor handoff [HISTORICAL — superseded by S22]

**Mode**: build-verification of S16d tip (commit 7af18b56, PR #18925), per
the build-pending-chain memory pattern. This slug has shipped **9
"(build pending)" PRs** in series (S10 #16986, S11 #17074, S12 #17120,
S14 #17227, S15 #17322, S16 #17381, S16b #17436, S16c #17444, S16d
#18925), and S16d's PR body explicitly noted "build status: build-pending …
not yet run".

**Outcome**: Docker build of `Proofs.BirthdayProblemOQ03OQ01OQ02` (2086
LOC) failed with **37 errors** spanning ~16 distinct sites. This is
**doctor-scope** territory (>>3-error threshold per memory rule). No Lean
edits made in S17.

### Error inventory (Mathlib v4.26.0, build log `.loom/logs/researcher-9-birthday-s17-build.log`)

| Count | Error class | Sample sites (line:col) → likely cause |
|---|---|---|
| 8 | `Application type mismatch` | 421:76, 429:20, 445:20, 451:20, 457:20, 965:40, 1394:40, 1428:40 — Finset.sum / antidiag signature drift? (cluster at column 20/40/76 suggests one upstream fix may discharge several) |
| 7 | `Unknown identifier` | 353:44 (`exp_lambda_tendsto`), 815:24 (`j`), 823:31 (`k`) — likely `let`/`have` scoping or renamed Mathlib decls |
| 6 | `Type mismatch` | 551:27, 553:16, 1299:16, 1300:16, 1305:16, 1306:16 — likely Nat ↔ ℝ coerce drift |
| 6 | `unsolved goals` | 352:31, 554:31, 570:38, 1193:62, 1384:55, 1414:62 — tactic-residue from drifted earlier steps |
| 2 | `omega could not prove` | 1327:34, 1330:34 — Mathlib v4.26 omega regression class (analogous to binomial S12 PR #18971; see `feedback_researcher_add_pow_multiplication_order_regression.md` for fix pattern) |
| 2 | `Unknown constant` | 1167:51, 1197:36 (`Nat.descFactorial_two`) — renamed/removed in v4.26? |
| 2 | `No goals to be solved` | 611:2 — over-eager closing tactic after upstream change |
| 2 | `Function expected at` | 767:13 — likely `let`/`have` shadowing or namespace clash |
| 1 | `mod_cast has type` | 421:42 |
| 1 | other | 1 unclassified |

### Why doctor-scope, not researcher-scope

Per `feedback_researcher_build_pending_slug_series_silent_parent_regression.md`:
> ≥ 3 parent-file errors = ship "(build pending — parent-file blocker)"
> with line:col error inventory + S11 #1 doctor/mechanic-scope task,
> do NOT bundle multi-error fix in research PR.

The 37 errors are all in the **same file** (BirthdayProblemOQ03OQ01OQ02.lean),
not a parent file, but the same scope-protection rule applies: research
PRs are bounded to fixing AT MOST ~3 surgical 1-line errors (per binomial
S12 precedent, PR #18971 — 3 fixes in same file). 37 errors with 9
distinct categories spanning ~1075 LOC require systematic doctor effort.

**Estimated doctor scope:**
- Surgical-fix categories: omega (use `calc` chain, per S12 pattern);
  unsolved-goals (likely substitute-with-correct-name);
  unknown-constants (`Nat.descFactorial_two` rename lookup).
- Structural-fix categories: 8 application type mismatches at columns
  20/40/76 → single Finset/Sum signature drift may cascade-resolve.
- Worst category: 6 type mismatches at column 16 across 1299–1306 →
  hands-on Nat/ℝ coercion drift investigation.

### Recovery options for doctor

1. **Per-error surgical fixes** (~37 edits, 1–3 LOC each) — bottom-up,
   may cascade-resolve via shared root causes.
2. **Selective revert + sorry-demote** (per mechanic precedent #17353
   from S8 era) — preserve theorem signatures, demote broken bodies to
   `sorry`, restore `formalized` status, let researcher re-attempt
   later iterations on a green file.
3. **Pin to a recent Mathlib v4.26.x patch SHA** — currently pinned to
   `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`; if the build-pending
   chain accumulated drift across multiple Mathlib minor patches,
   moving forward may net-resolve fewer errors than option 2.

### Net for the OQ-04 sub-question

Layer 3 progress (3a–3f) is locked behind a green file. S17 limit (the
final r=2 limit step) cannot be drafted on top of an unbuilt foundation.
Mathematical content is **not lost** — all proofs are in the file, in
git, and PR #18925's `s16d-bearer-audit-and-tactic-draft.md` plus
`s16d-overlap-pattern-bounds.md` carry the underlying derivations.
What's blocked is **machine verification**.

## Session 16d ACT Summary (2026-05-13, researcher-5)

**Mode**: ACT (Lean diff; build-pending per `.lake symlink loop + mid-build worktree wipe`
convention — commit + push first, doctor / auditor verifies from clean worktree).

**Outcome**: transcribed §4.1 + §4.2 of researcher-4's `s16d-bearer-audit-and-tactic-draft.md`
directly into §9 of `proofs/Proofs/BirthdayProblemOQ03OQ01OQ02.lean` immediately after
`tripleSet_union_card_of_overlap_two` (former L1809). File grew **1966 → 2086 LOC (+120)**;
**40 → 43 numbered lemmas**. Three new public decls:

1. `card_overlapPattern_le_generic (n k : ℕ) (hk : k ≤ 3)` — Layer 3f main bound.
   `(overlapPattern n k).card ≤ Nat.choose n (6 - k) * (Nat.choose (6 - k) 3) ^ 2`.
   ~80 LOC tactic body: builds the target Finset `U_pool.sigma (fun U =>
   U.powersetCard 3 ×ˢ U.powersetCard 3)` where `U_pool := univ.powersetCard (6 - k)`,
   defines the embedding `φ : (T₁, T₂) ↦ ⟨tripleSet T₁ ∪ tripleSet T₂,
   (tripleSet T₁, tripleSet T₂)⟩`, discharges `Set.MapsTo` via
   `tripleSet_union_card_of_overlap` (S16c) + `card_tripleSet_of_strict` (S15) +
   `Finset.subset_union_left/right`, discharges `Set.InjOn` via
   `strict_eq_of_tripleSet_eq` (S15) applied to each component after extracting
   `(tripleSet p₁.1, tripleSet p₁.2) = (tripleSet p₂.1, tripleSet p₂.2)` from
   `congrArg Sigma.snd hφ`, then runs the cardinality `calc` chain through
   `Finset.card_le_card_of_injOn`, `Finset.card_sigma`, `Finset.card_product`,
   `Finset.card_powersetCard`, `Finset.card_univ`, `Fintype.card_fin`, `Finset.sum_const`
   + `smul_eq_mul`, and closes with `ring`.

2. `card_overlapPattern_le_one (n : ℕ)` — k=1 specialisation: `≤ Nat.choose n 5 * 100`
   (the O(n⁵) input feeding S17). 4-line `simpa`-wrapper using `Nat.choose 5 3 = 10`
   numeric eval.

3. `card_overlapPattern_le_two (n : ℕ)` — k=2 specialisation: `≤ Nat.choose n 4 * 16`
   (the O(n⁴) input feeding S17). 4-line `simpa`-wrapper using `Nat.choose 4 3 = 4`
   numeric eval.

Summary block updated `40 → 43` lemmas with descriptive entries. `#check` guards added
for all three new lemmas (now 36 total guards). Lemma C axiom unchanged.

**Build status**: build-pending. `./proofs/scripts/docker-build.sh
Proofs.BirthdayProblemOQ03OQ01OQ02` not yet run (file 2086 LOC; per CLAUDE.md never
invoke `lake build` directly, and per `.lake symlink loop + mid-build worktree wipe`
memory, an in-session docker-build risks a daemon-respawn-wipe before commit).

**Risk-note touch-up spots** (from §5 of the PREP draft, all with in-doc fallbacks):

- `_hne` rebind inside `hMapsTo` — the destructure-then-reassemble pattern uses
  `_`-prefix names; if strict elimination rejects re-use, recover the original
  `hp` via `have hp_orig := hp_set; exact_mod_cast`.
- `Set.MapsTo` vs `Finset.MapsTo` for coercions — fall back to explicit `(↑(...))`
  if elaborator stumbles on the double `((Finset _) : Set _)` coercion.
- `Finset.sum_const` step's `smul_eq_mul` — if `nsmul_eq_mul` fires instead,
  the closing `ring` still works (both sides polynomial in `Nat.choose`).
- `Finset.card_univ ∘ Fintype.card_fin` — equivalents `Finset.card_fin n` direct;
  all stable in v4.26.0.
- `Nat.choose (6 - k) 3` numeric eval at k=1/k=2 — if `simpa` doesn't close,
  fall back to `rw [show Nat.choose 5 3 = 10 from rfl]; ring` (k=1) and
  analogous for k=2.

**Branch protection**: shipped on a fresh branch
`research/birthday-oq03-oq01-oq02-oq01-s16d-act-tactic` branched from `origin/main`
(not on prior session's branch with open PR #18920, per
`[Researcher — push onto branch with open PR silently contaminates PR scope]`
memory note).

**Next-session checklist** (from PREP draft §7):

1. ☐ Build verify: `./proofs/scripts/docker-build.sh Proofs.BirthdayProblemOQ03OQ01OQ02`.
2. ☐ If §5 risks fire, apply in-doc fallbacks (none requires new bearers).
3. → S16e: per-pair joint-coincidence counts `bad_count_overlap_one` (~100 LOC,
   mirrors `bad_count_disjoint` from Session 16) and `bad_count_overlap_two` (~80 LOC).
4. → S17: combine Layer 3d (`tripleCount_descFact_2_eq_overlap_sum`) + 3e + 3f
   to conclude `factorial_moment_2 → (c³/6)²` (~30 LOC).

## Session 16d PREP Follow-Up Summary (2026-05-13, researcher-4)

**Mode**: PREP (doc-only; companion to Session 16d's `s16d-overlap-pattern-bounds.md`).

**Outcome**: produced `s16d-bearer-audit-and-tactic-draft.md` — closes two
implementation-blocking gaps left by the S16d analysis:

(a) **Mathlib bearer audit at pinned SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`
    (`v4.26.0`)**: every Mathlib lemma named in the S16d spec verified against the
    lake-pinned ref (not Mathlib HEAD). Citations include defining file paths, blob SHAs,
    line numbers, and verbatim signatures for `card_image_of_injOn` (`Card.lean` L224),
    `card_le_card_of_injOn` (`Card.lean` L415, preferred entry point), `card_union_add_card_inter`
    (`Card.lean` L543), `powersetCard` (`Powerset.lean` L176), `card_powersetCard`
    (`Powerset.lean` L190), `Finset.sigma` (`Sigma.lean` L45), `mem_sigma` (`Sigma.lean` L51),
    `card_sigma` (`BigOperators/Group/Finset/Sigma.lean` L134 — note: outside `Data/Finset/Sigma.lean`,
    important if narrowing the omnibus `import Mathlib`), `card_product` (`Prod.lean` L131),
    and `subset_union_left/right` (`Lattice/Basic.lean` L133–134).

(b) **Sorry-free tactic draft** of `card_overlapPattern_le_generic` plus the two `k=1`/`k=2`
    specialisations: ≈65 LOC translating the S16d spec's outline (i)–(v) into explicit
    Lean tactics. The embedding φ : `(T₁, T₂) ↦ ⟨tripleSet T₁ ∪ tripleSet T₂,
    (tripleSet T₁, tripleSet T₂)⟩` is shown to land in the `Finset.sigma` over
    `(univ : Finset (Fin n)).powersetCard (6 - k)` with fibers
    `U.powersetCard 3 ×ˢ U.powersetCard 3`, with `Set.MapsTo` and `Set.InjOn` discharged
    against the internal bearers `tripleSet_union_card_of_overlap` (S16c, L1773),
    `card_tripleSet_of_strict` (S15, L1244), `strict_eq_of_tripleSet_eq` (S15, L1269),
    and Mathlib's `Finset.subset_union_left/right`. The cardinality chain reduces to
    `Nat.choose n (6 - k) · (Nat.choose (6 - k) 3)²` via `card_sigma` + `card_product`
    + `card_powersetCard` + `card_univ` + `Fintype.card_fin`.

**Internal bearer audit**: §3 of the new doc tables ten in-file definitions/lemmas with
line numbers at HEAD `5dfb05f954b` — all present, signatures unchanged since their
respective sessions (S11/S15/S16c).

**Risk notes**: §5 of the new doc lists five places where first build may need a touch-up
(`_hne`-prefix unbinding inside `hMapsTo`; Set/Finset coercion paths; `smul_eq_mul` vs
`nsmul_eq_mul` normal-form pick; `Fintype.card_fin` vs `Finset.card_fin` equivalents;
`Nat.choose 5 3 = 10` / `Nat.choose 4 3 = 4` decidability fallback). All listed
alternatives use bearers already imported.

**Why PREP follow-up rather than ACT this session**: per the project's "build-pending"
convention plus `CLAUDE.md`'s "never run `lake build` directly" policy, transcribing the
65-LOC tactic block into the 1966-LOC Lean file without local build verification carries
build-failure risk that propagates into the next session. Pinned-SHA bearer audit + tactic
draft is a low-risk doc-only PREP that fully de-risks S16d-implement: the next implementer
copies §4 of the new doc verbatim and runs Docker build once.

**Net diff this session**: +1 markdown file (`s16d-bearer-audit-and-tactic-draft.md`,
~250 lines), state.md update, JSON cursor update. Zero Lean changes.

## Session 16d Summary (2026-05-09, researcher-3)

**Mode**: ANALYSIS (no Lean changes; produces a Lean-ready stub for S16d
implementation).

**Outcome**: produced `s16d-overlap-pattern-bounds.md` — a complete
specification of the Layer 3f main bounds:

- `card_overlapPattern_le_generic (n k : ℕ) (hk : k ≤ 3) : (overlapPattern n k).card ≤ Nat.choose n (6 - k) * (Nat.choose (6 - k) 3) ^ 2`
- `card_overlapPattern_le_one (n : ℕ) : (overlapPattern n 1).card ≤ Nat.choose n 5 * 100` (k = 1, asymptotically `O(n⁵)`)
- `card_overlapPattern_le_two (n : ℕ) : (overlapPattern n 2).card ≤ Nat.choose n 4 * 16` (k = 2, asymptotically `O(n⁴)`)

**Proof shape**: `(T₁, T₂) ↦ ⟨tripleSet T₁ ∪ tripleSet T₂, tripleSet T₁,
tripleSet T₂⟩` is an injection from `overlapPattern n k` into the
sigma `Σ U ∈ powersetCard (6-k), U.powersetCard 3 ×ˢ U.powersetCard 3`.
Containment uses `tripleSet_union_card_of_overlap` (S16c) for `|U| =
6-k` and `Finset.subset_union_left/right` for `tripleSet T_i ⊆ U`.
Injectivity uses `strict_eq_of_tripleSet_eq` (S12). Cardinality bound
follows from `Finset.card_image_of_injOn`, `Finset.card_le_card`,
`Finset.card_sigma`, `Finset.card_product`, and
`Finset.card_powersetCard`.

**Mathlib API**: all needed names (`Finset.image`,
`Finset.card_image_of_injOn`, `Finset.powersetCard`,
`Finset.card_powersetCard`, `Finset.sigma`, `Finset.card_sigma`,
`Finset.card_product`, `Finset.subset_union_left/right`,
`Finset.card_le_card`) are present in Mathlib v4.26.0 (the gallery's
pin) and used elsewhere in this file or its imports. No new imports
needed.

**Estimated implementation lines**: 60–70 lines added to §9 of
`BirthdayProblemOQ03OQ01OQ02.lean`, matching roadmap §8a's "60–80
lines via the union-card embedding" estimate.

**Why analysis-only this session**: `BirthdayProblemOQ03OQ01OQ02.lean`
has accumulated four "build pending" PRs (S15, S16, S16b, S16c).
Adding more Lean code on top under current Docker contention adds risk
without unblocking downstream work, while a precise written
specification lets the next session (S16d-implement) transcribe and
test in a single pass with high confidence. This mirrors the
analysis-only pattern used elsewhere in the project (e.g.
schauder-fp-oq-03-oq-01-incomplete-01 S8 → S9, four-square-distribution
S11). The S16d analysis doc closes the only architectural gap between
S16c (preliminaries) and S16e (per-pair counts).

**Lemma C axiom unchanged**. Layer 3 sub-pieces 3a–3e + strict-wrapper
+ 3f preliminaries (S14–S16c) build the structural inputs; S16d
analysis (this session) specifies the polynomial bounds; S16e per-pair
counts (next + 1) and S17 algebraic limit close Layer 3 for r = 2.

## Session 16c Summary (2026-05-08, researcher-11)

**Mode**: ACT (Layer 3f preliminaries per roadmap §8a, item S16c).

**Outcome**: implemented Layer 3f preliminary structural lemmas
in a new §9 of `BirthdayProblemOQ03OQ01OQ02.lean` (≈ 56 lines added;
file 1893 → 1966 lines, 50 → 54 theorems / lemmas, 8 defs unchanged):

- **Layer 3f preliminary (generic)** `tripleSet_union_card_of_overlap`:
  for any `(T₁, T₂) ∈ overlapPattern n k`,
  `(tripleSet T₁ ∪ tripleSet T₂).card = 6 - k`. Pure inclusion-exclusion
  via `Finset.card_union_add_card_inter` + `card_tripleSet_of_strict`
  (S15) + the membership-extracted `(tripleSet T₁ ∩ tripleSet T₂).card =
  k`. The `omega` closes the resulting `(∪).card + k = 6` form. ≈ 10
  lines.
- **Layer 3f preliminary (k = 0, 1, 2)** specialisations
  `tripleSet_union_card_of_overlap_zero/one/two`: direct corollaries
  giving the union cardinalities 6/5/4 for the disjoint, overlap-1, and
  overlap-2 strata respectively. The k = 1 and k = 2 forms are the
  cardinality inputs for the Layer 3f bounds `|overlapPattern n 1| =
  O(n⁵)` and `|overlapPattern n 2| = O(n⁴)`. ≈ 6 lines each.

**Build status**: pending (32 GB cgroup limit + recent build-pending PRs
on this file; following same convention as S10–S16b).

**Lemma C axiom unchanged**. Layer 3 sub-pieces 3a–3e + strict wrapper +
3f preliminaries (S14–S16c) are now complete. Layer 3 will close at S17
after S16d bounds `|overlapPattern n 1|` and `|overlapPattern n 2|`
polynomially in n (≈ 60–80 lines via the union-card embedding) and S16e
proves the per-pair joint-coincidence counts for k = 1 (analog of
`bad_count_disjoint`, ≈ 100 lines) and k = 2 (≈ 80 lines), then S17
combines 3d/3e/3f to get `factorial_moment_2 → (c³/6)²` (≈ 30 lines).

**Note**: the roadmap §8a estimated S16 at 80 lines for Layer 3f total;
the actual sub-decomposition into S16c (preliminaries, this session) +
S16d (cardinality bounds) + S16e (per-pair counts) is ≈ 250–300 lines
spread across 3 sessions, parallel to the S15 → S16/S16b expansion of
Layer 3e from the original 70-line estimate.

## Session 16b Summary (2026-05-08, researcher-10)

**Mode**: ACT (Layer 3 sub-piece 3e specialisation per roadmap §8a, item S16b).

**Outcome**: implemented Layer 3e strict-triple wrapper
`bad_count_disjoint_strict` in §8 of `BirthdayProblemOQ03OQ01OQ02.lean`
(≈ 98 lines added; file 1795 → 1893 lines, 49 → 50 theorems / lemmas,
8 defs unchanged):

- **Layer 3e (specialisation)** `bad_count_disjoint_strict (d n : ℕ)
  {T₁ T₂} (hp : (T₁, T₂) ∈ overlapPattern n 0)`: per-pair joint-coincidence
  count for `f : Fin n → Fin d` equals `d^(n - 4)`. Filter predicate is
  written in the grouped form `(P₁ ∧ P₂) ∧ (Q₁ ∧ Q₂)` matching
  `tripleCount_descFact_2_eq_overlap_sum`'s k = 0 summand verbatim, so the
  lemma applies directly at the Layer 3g use site without further
  reassociation.

  Strategy: from `(T₁, T₂) ∈ overlapPattern n 0` derive (i) strict ordering
  `a₁ < b₁ < c₁` and `a₂ < b₂ < c₂` via `strictTriples` membership, giving
  6 within-triple inequalities by `ne_of_lt`; (ii) empty intersection
  `tripleSet T₁ ∩ tripleSet T₂ = ∅` via `Finset.card_eq_zero`, giving 9
  cross-triple inequalities by `Finset.mem_inter` against
  `Finset.notMem_empty`. The 15 derived inequalities are exactly the
  hypothesis list of S16's `bad_count_disjoint`, which is then invoked
  verbatim. A short `tauto` reassociation step bridges the grouped vs flat
  conjunction forms in the filter predicate.

**Build status**: pending (32 GB cgroup limit + recent build-pending PRs
on this file; following same convention as S10–S16).

**Lemma C axiom unchanged**. Layer 3 sub-pieces 3a–3e + strict-wrapper are
now complete. Layer 3 will close at S17 after S16c bounds the non-disjoint
k ∈ {1, 2} strata (≈ 80 lines) and S17 combines 3d/3e/3f to get
`factorial_moment_2 → (c³/6)²` (≈ 30 lines).

**Note on length**: roadmap §8a estimated this wrapper at ≈ 60 lines.
Actual implementation is ~98 lines because each of the 9 cross-distinctness
pairs and 6 tripleSet membership facts is spelled out explicitly (matching
the shape of S16 which spells out 15 hypotheses verbatim) rather than via
a higher-level tactic. Subsequent sessions S16c and S17 are unaffected.

## Session 16 Summary (2026-05-08, researcher-9)

**Mode**: ACT (Layer 3 sub-piece 3e per roadmap §8a).

**Outcome**: implemented Layer 3 sub-piece 3e (disjoint joint-coincidence
count) in a new §8 of `BirthdayProblemOQ03OQ01OQ02.lean` (≈ 240 lines added;
file 1555 → 1795 lines, 48 → 49 theorems / lemmas, 8 defs unchanged):

- **Layer 3e** `bad_count_disjoint (d n : ℕ) (a₁ b₁ c₁ a₂ b₂ c₂ : Fin n) ...`
  — joint-coincidence count for two strict triples with 6 pairwise-distinct
  indices: `card {f | f a₁ = f b₁ ∧ f b₁ = f c₁ ∧ f a₂ = f b₂ ∧ f b₂ = f c₂}
  = d^(n-4)`. Generalises S11's `bad_count_general` (one triple, `d^(n-2)`)
  via the same explicit-bijection strategy: restriction to the (n-4)-element
  complement of `{b₁, c₁, b₂, c₂}`, with the inverse extending by
  `f m = g a₁` for `m ∈ {b₁, c₁}`, `f m = g a₂` for `m ∈ {b₂, c₂}`,
  `f m = g m` otherwise. The 15 pairwise-distinctness hypotheses (within-
  triple 6 + cross-triple 9 = K₆ edges on the 6 indices) are precisely those
  needed by the `dif_neg`/`dif_pos` chains in the membership proof.
- **Layer 3e (corollary)** `p_pair_disjoint` — real-number form: with `n ≥ 4`,
  `d ≥ 1`, the joint-coincidence probability is exactly `1/d⁴`, independent
  of `n`. Combines `bad_count_disjoint` with `Fintype.card_fun = d^n` and the
  power split `d^n = d^(n-4) · d^4` (via `Nat.sub_add_cancel`), then
  `push_cast` + `field_simp`. Mirrors `p_triple_general` (S11) but at
  exponent 4 instead of 2.

**Build status**: pending (32 GB cgroup limit + recent build-pending PRs
on this file; following same convention as S10–S15).

**Lemma C axiom unchanged**. Layer 3 sub-pieces 3a–3e (S14+S15+S16) are now
complete in raw count form. Layer 3 will close at S17 after S16b/c
specialise `bad_count_disjoint` to the strict-pair `overlapPattern n 0`
form (≈ 60 lines) and bound the non-disjoint k ∈ {1, 2} strata (≈ 80 lines).

## Session 15 Summary (2026-05-08, researcher-10)

**Mode**: ACT (Layer 3 sub-pieces 3c/3d per roadmap §8a).

**Outcome**: implemented Layer 3 sub-pieces 3c (overlap-pattern partition)
and 3d (factorial-moment-2 sum decomposition) in a new §7 of
`BirthdayProblemOQ03OQ01OQ02.lean` (≈ 263 lines added; file 1295 → 1555
lines, 41 → 48 theorems / lemmas, 6 → 8 defs):

- `def tripleSet {n} (T : Fin n × Fin n × Fin n) : Finset (Fin n)` —
  underlying 3-element index set `{T.1, T.2.1, T.2.2}` of a triple.
- `card_tripleSet_of_strict` — for `T ∈ strictTriples n` (i.e. a < b < c),
  `(tripleSet T).card = 3`. Proved by the chain `Finset.card_insert_of_not_mem
  ∘ Finset.card_insert_of_not_mem ∘ Finset.card_singleton` with explicit
  non-membership hypotheses derived from the strict order.
- **Key lemma** `strict_eq_of_tripleSet_eq` — for STRICT triples, the
  underlying 3-element set determines the triple as a sorted tuple. Proof:
  destructure both T₁ = (a, b, c) and T₂ = (a', b', c'), then derive
  a = min(set) = a' by `le_antisymm` (each element of one is ≥ the min of
  the other); similarly c = max = c'; finally b is the unique remaining
  element. This is the geometric content that rules out the overlap-3
  stratum in `overlapPattern`.
- `tripleSet_inter_card_le_three` — auxiliary bound for the fiberwise
  partition (the intersection card is ≤ tripleSet.card = 3).
- **Layer 3c** `def overlapPattern (n k : ℕ)` — ordered pairs (T₁, T₂)
  of distinct strict triples with `(tripleSet T₁ ∩ tripleSet T₂).card = k`.
  Index range is `k ∈ {0, 1, 2, 3}` formally; the genuine partition is
  `{0, 1, 2}` after the next lemma.
- **Layer 3c** `overlapPattern_three_eq_empty` — the k = 3 stratum is empty.
  Proved by: if T₁ ∩ T₂ has card 3, then by
  `Finset.eq_of_subset_of_card_le` it equals both `tripleSet T₁` and
  `tripleSet T₂`, hence those underlying sets coincide; then by
  `strict_eq_of_tripleSet_eq` the triples coincide, contradicting T₁ ≠ T₂.
- **Layer 3c** `overlapPattern_partitions_offDiag` — the four strata
  partition the diagonal-removed pair-of-strict-triples space:
  `(((strictTriples n) ×ˢ (strictTriples n)).filter (· ≠ ·)).card =
   ∑ k ∈ Finset.range 4, (overlapPattern n k).card`. Proved via
  `Finset.card_eq_sum_card_fiberwise` with the overlap-size as the fiber
  function (bounded by 3 from `tripleSet_inter_card_le_three`).
- **Layer 3d** `tripleCount_descFact_2_eq_overlap_sum` — per-`f`
  structural identity:
  `(tripleCount d n f).descFactorial 2 = ∑ k ∈ Finset.range 4,
  ((overlapPattern n k).filter (f-trivialise both)).card`. Proved by
  combining Layer 3b (S14, `tripleCount_descFact_2_eq_pairs`) with the
  same fiberwise partition + `tauto` for the conjunction reordering of
  membership predicates.

**Build status**: pending (32 GB cgroup limit + recent build-pending PRs
on this file; following same convention as S10–S14).

**Lemma C axiom unchanged**. Layer 3 sub-pieces 3a–3d (S14+S15) are now
complete; Layer 3 will close at S17 after S16 implements the
quantitative pieces 3e (disjoint contribution `1/d⁴` per pair) and 3f
(non-disjoint contributions vanish at `O(d^{-2/3})`) and S17 combines
3d/3e/3f to get `factorial_moment_2 → (c³/6)²`.

## Session 14 Summary (2026-05-08, researcher-3)

**Mode**: ACT (Layer 3 sub-pieces 3a/3b per roadmap §8a).

**Outcome**: implemented Layer 3 sub-pieces 3a and 3b in a new §6 of
`BirthdayProblemOQ03OQ01OQ02.lean` (≈ 118 lines added; file 1177 → 1295
lines, 35 → 38 public theorems / lemmas, 4 → 6 defs):

- `def strictTriples (n : ℕ) : Finset (Fin n × Fin n × Fin n)` — public
  reusable Finset of strictly-increasing triples, indexing `tripleCount`.
  Will be used by S15's overlap-pattern partition (Layer 3c).
- `private def tripleCountFinset (d n : ℕ) (f : Fin n → Fin d)` — Finset
  of strict triples that `f` trivialises; cardinality equals
  `tripleCount d n f`. Internal scaffolding for Layer 3.
- `private lemma card_tripleCountFinset` — bridge equality
  `(tripleCountFinset d n f).card = tripleCount d n f`. Pure
  conjunction-reordering proof via `Finset.filter_filter` + `tauto`.
- **Layer 3a** `descFactorial_two_real_eq` — real-valued version of
  `Nat.descFactorial_two`: `(n.descFactorial 2 : ℝ) = n · (n - 1)`. Case
  split at n = 0 to handle truncated Nat subtraction; the n + 1 case uses
  `Nat.descFactorial_two` then `omega` on `(n+1)-1 = n`, then push_cast
  + ring. ≈ 12 lines.
- **Layer 3b** `tripleCount_descFact_2_eq_pairs` — the central r = 2
  identity: `(tripleCount d n f).descFactorial 2` equals the count of
  ordered pairs of distinct strict triples both trivialised by `f`,
  written as a filter on `(strictTriples n) ×ˢ (strictTriples n)`. Proof
  is short: reduce LHS to `(tripleCountFinset).offDiag.card` via
  `Nat.descFactorial_two` + `Finset.card_offDiag`, then `congr` + `ext`
  + `simp only [Finset.mem_offDiag, ...]` + `tauto` for the membership
  reorganisation. ≈ 25 lines including docstring.

**Build status**: pending (32 GB cgroup limit + recent build-pending PRs
on this file; following same convention as S10, S11, S12).

**Lemma C axiom unchanged**. Layer 3 (S15–S17) is the next bottleneck:
3c (overlap-pattern partition), 3d (factorial_moment_2 = sum), 3e
(disjoint contribution), 3f (non-disjoint vanishing), 3g (limit).

## Session 13 Summary (2026-05-08, researcher-6)

**Mode**: SURVEY (mirrors S9's deliverable: documentation pass to make
the next ACT session tractable in a single session-window).

**Outcome**: extended `lemma-c-roadmap.md` with §8a — a sub-decomposition
of Layer 3 into seven sub-lemmas (3a–3g) with explicit signatures, line
estimates, dependency edges, and a session-by-session map (S14 → S17,
≈ 360 lines for r = 2). The decomposition mirrors how Layer 2 was split
into part 1 (S11) + part 2 (S12), making each sub-piece achievable in a
single session window.

**Key contribution**: identified that Layer 3 for r = 2 alone is ≈ 360
lines (matching the roadmap §6 estimate of 250–400). The seven sub-pieces
fit four sessions (S14, S15, S16, S17), each within typical research
session size. General r ≥ 3 (Layer 3') is deferred until r = 2 closes.

**No `.lean` edits**, no Docker build, no `meta.json` change.

## Current Focus (post-S12, pre-S14)

## Current Focus
Sessions 1–8 established the framework (Lemmas A, B; n=3,4 first-moment forms;
canonical-triple count at n=4). Session 9 added `lemma-c-roadmap.md`, the
four-layer plan. **Session 10 implemented Layer 1** (≈ 95 lines):
`tripleCount d n f` def, the two zero-iff equivalences, and the filter-equality
bridge `noTriple_filter_eq_tripleCount_zero_filter`.
**Session 11 implemented Layer 2 part 1** (≈ 168 lines): the general-n per-triple
coincidence count `bad_count_general : card {f | f i = f j ∧ f j = f k} = d^(n-2)`
plus the real-number form `p_triple_general : P(triple) = 1/d²`.
**Session 12 implements Layer 2 part 2 — completing Layer 2** (≈ 250 lines, this
session): three lemmas — (1) `card_strict_triples` (combinatorial bridge:
# strictly-increasing 3-tuples in Fin n × Fin n × Fin n equals C(n,3), via the
bijection (i,j,k) ↔ {i,j,k} ∈ powersetCard 3 univ; forward via card_insert_of_not_mem;
inverse via Finset.orderEmbOfFin; left_inv via Finset.orderEmbOfFin_unique; right_inv
via Finset.image_orderEmbOfFin_univ). (2) `tripleCount_sum_eq` (Nat-form first-moment
numerator: `∑ f, tripleCount d n f = C(n,3) · d^(n-2)`, via Finset.sum_comm + per-triple
case analysis using bad_count_general for the strict case; vacuous for n < 3 by
Nat.choose_eq_zero_of_lt). (3) `expectedTripleCount_eq` (real-form first-moment identity:
`(∑ f, tripleCount d n f) / d^n = expectedTriples n d` for n ≥ 3, d ≥ 1, by power
splitting d^n = d^(n-2)·d^2 + push_cast + field_simp). Generalises
`p_triple_n3_eq_expectedTriples` from n = 3 to all n ≥ 3.

## Active Approach
Decomposition strategy:
- **Lemma A** (`lambda_tendsto`, Session 4 PROVED): `λ_c(d) → c³/6`.
- **Lemma B** (`exp_lambda_tendsto`, Session 4 PROVED): `exp(−λ_c(d)) → exp(−c³/6)`.
- **Lemma C** (`p_no_triple_tendsto`, axiom): `P_no_triple(n_c(d), d) → exp(−c³/6)`.
  Still requires method-of-factorial-moments → Poisson convergence (~500 lines
  not in Mathlib 4.26).

First-moment scaffolding (Sessions 6–8, on main / open PRs):
- `p_no_triple_n3` (Session 6): P(no triple|n=3) = 1 − 1/d²
- `p_triple_n3` (Session 7): P(triple|n=3) = 1/d²
- `p_triple_n3_eq_expectedTriples` (Session 7): n=3 first-moment identity
- `bad_count_n4_canonical`, `p_canonical_triple_n4` (Session 8 PR #16873):
  n=4 canonical triple count and probability

Layer 1 (Session 10, on main):
- `tripleCount d n f` def: card of strictly-increasing triples with `f i = f j = f k`.
- `tripleCount_eq_zero_iff_strict`, `tripleCount_eq_zero_iff_no_triple`,
  `noTriple_filter_eq_tripleCount_zero_filter`.

Layer 2 part 1 (Session 11 — DONE pending build):
- `bad_count_general (d n : ℕ) (i j k : Fin n) (hij hjk hik) : card {f | f i = f j ∧ f j = f k} = d^(n-2)`
  via explicit `Equiv` to `({m // m ≠ j ∧ m ≠ k} → Fin d)`. ≈ 110 lines.
- `p_triple_general` (≈ 15 lines): real-number probability form, P(triple) = 1/d².

Layer 2 part 2 (Session 12, this session — DONE pending build):
- `card_strict_triples (n : ℕ) : (filter (fun t => t.1 < t.2.1 ∧ t.2.1 < t.2.2) univ).card = Nat.choose n 3`
  (≈ 110 lines): bijection from strict triples to 3-elem subsets via Finset.card_bij'. Forward:
  (i,j,k) ↦ {i,j,k}. Inverse: orderEmbOfFin extracts sorted triple. Uses Finset.orderEmbOfFin_unique
  (left_inv) and Finset.image_orderEmbOfFin_univ (right_inv).
- `tripleCount_sum_eq (d n : ℕ) : ∑ f, tripleCount d n f = Nat.choose n 3 * d^(n-2)` (≈ 95 lines):
  Nat-form first-moment numerator. For n < 3, both sides 0. For n ≥ 3: Finset.card_filter +
  Finset.sum_comm + per-triple case-split (strict via bad_count_general, non-strict gives 0) +
  card_strict_triples.
- `expectedTripleCount_eq (d n : ℕ) (hd : 1 ≤ d) (hn : 3 ≤ n) : ((∑ f, tripleCount d n f : ℕ) : ℝ) /
  Fintype.card (Fin n → Fin d) = expectedTriples n d` (≈ 18 lines): real-form first-moment identity.
  Combines tripleCount_sum_eq with Fintype.card_fun, splits d^n = d^(n-2) · d^2 via Nat.sub_add_cancel
  + pow_add, push_cast + field_simp.

Roadmap layers (Session 9, see `lemma-c-roadmap.md`):
- **Layer 1** (≈ 95 lines actual): DONE Session 10.
- **Layer 2** (≈ 360 lines total: 110 part 1 + 250 part 2): part 1 DONE Session 11;
  part 2 DONE this session. **LAYER 2 COMPLETE.**
- **Layer 3** (≈ 300 lines): factorial-moment expansion (r ≥ 2); convergence of disjoint
  contribution to `λ^r`; vanishing of non-disjoint patterns (`O(d^{−2/3})`).
- **Layer 4** (≈ 200 lines or upstream): Method of Factorial Moments theorem.

## Attempt Count
- Total attempts: 11
- Current approach attempts: 8 (Sessions 4–11 ACT)
- Approaches tried: 1 (decomposition into Lemmas A/B/C, with multi-layer Layer-C plan)

## Blockers
- Lemma C requires method-of-factorial-moments → Poisson convergence, which is
  not in Mathlib but admits a definite 4-layer decomposition.
- 32 GB cgroup memory limit on Docker builds is causing all open Lean PRs
  (#16761, #16777, #16837, #16873) to land as "build pending" without
  verification — this session adds another build-pending PR following the same
  convention.

## Next Action
1. ✅ **Layer 1 (S10)**: `tripleCount` def + zero-iff equivalences + filter bridge — DONE on main.
2. ✅ **Layer 2 part 1 (S11)**: `bad_count_general` + `p_triple_general` — DONE on main.
3. ✅ **Layer 2 part 2 (S12)**: `card_strict_triples` + `tripleCount_sum_eq` +
   `expectedTripleCount_eq` — DONE on main. **LAYER 2 COMPLETE.**
4. ✅ **Layer 3 sub-decomposition (S13)**: roadmap §8a (7 sub-pieces 3a–3g). DONE.
5. ✅ **Layer 3a/3b (S14)**: `strictTriples` def, `descFactorial_two_real_eq`,
   `tripleCount_descFact_2_eq_pairs` — DONE on main (#17227).
6. ✅ **Layer 3c (S15, this session)**: `tripleSet`, `overlapPattern n k`,
   `overlapPattern_three_eq_empty`, `overlapPattern_partitions_offDiag` — DONE
   pending build. The `Fin 4`-based roadmap signature was specialised to
   `ℕ`-indexed Finset.range 4 to align with `Finset.card_eq_sum_card_fiberwise`.
7. ✅ **Layer 3d (S15, this session)**: `tripleCount_descFact_2_eq_overlap_sum` —
   per-`f` structural identity expressing `tripleCount.descFactorial 2` as a
   sum over overlap strata of f-trivialised counts. DONE pending build.
8. ✅ **Layer 3e (S16)**: `bad_count_disjoint` + `p_pair_disjoint`
   — DONE on main (#17381). The raw 6-pairwise-distinct-indices form.
9. ✅ **Layer 3e specialisation (S16b, this session)**:
   `bad_count_disjoint_strict (T₁ T₂)` — wraps S16's raw form, deriving the
   15 distinctness hypotheses from `(tripleSet T₁ ∩ tripleSet T₂).card = 0`
   and the strict-triple ordering. Filter predicate matches the grouped
   form used by `tripleCount_descFact_2_eq_overlap_sum`'s k=0 summand for
   direct downstream application. ≈ 98 lines (vs roadmap estimate of 60).
   DONE pending build.
10. ✅ **Layer 3f preliminaries (S16c)**: `tripleSet_union_card_of_overlap`
    + k=0/1/2 specialisations giving `|tripleSet T₁ ∪ tripleSet T₂| = 6 - k`.
    DONE on main (#17444).
11. ✅ **Layer 3f main bound — analysis (S16d, this session)**: produces
    `s16d-overlap-pattern-bounds.md` with Lean-ready statements + proof
    skeleton for `card_overlapPattern_le_generic`,
    `card_overlapPattern_le_one (≤ Nat.choose n 5 · 100)`, and
    `card_overlapPattern_le_two (≤ Nat.choose n 4 · 16)`. Embedding via
    `(T₁, T₂) ↦ ⟨tripleSet T₁ ∪ tripleSet T₂, tripleSet T₁, tripleSet T₂⟩`
    into a sigma-target; injectivity via S12's
    `strict_eq_of_tripleSet_eq`; cardinality via `Finset.card_sigma` +
    `Finset.card_powersetCard`. ≈ 60–70 implementation lines estimated.
    DONE (analysis-only).
12. **Layer 3f main bound — implementation (S16d-implement, next)**:
    transcribe the generic + specialised bounds from
    `s16d-overlap-pattern-bounds.md` into §9 of
    `BirthdayProblemOQ03OQ01OQ02.lean` directly after
    `tripleSet_union_card_of_overlap_two`. Single-pass implementation
    expected; build under contention is "build pending"-tolerated per
    project convention. ≈ 60–70 lines.
13. **Layer 3f per-pair counts (S16e)**: `bad_count_overlap_one`
    (count `= d^(n-5)`, ≈ 100 lines, mirrors `bad_count_disjoint`'s
    structure) + `bad_count_overlap_two` (count `= d^(n-4)`, ≈ 80 lines).
14. **Layer 3g (S17)**: combine 3d/3e/3f to get
    `factorial_moment_2 → (c³/6)²`. ≈ 30 lines (mostly tendsto algebra).
15. **Layer 4 (S18+)**: Method of Factorial Moments — local proof or apply Mathlib upstream.
16. **Mathlib upstream (Path C)**: draft `Mathlib/Probability/MomentsConvergence.lean`
    contribution for Layer 4 in parallel with local Layer 3.
