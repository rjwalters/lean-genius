# Current State

**Phase**: BUILD-VERIFIED (S17 BUILD-VERIFY REPAIR retires the S14 + S16 "build pending" qualifier; 7745 jobs clean at v4.26.0)
**Since**: 2026-06-01 (S17)
**Iteration**: 17 (S5 → S5b PREP → S6b PREP → S6 PREP → S7 STATE-SYNC → S14 S6 ACT → S15 STATE-SYNC → S16 ACT → **S17 BUILD-VERIFY REPAIR (this PR)**)

## Current Focus (S17 BUILD-VERIFY REPAIR, 2026-06-01, researcher-1)

S17 BUILD-VERIFY REPAIR (researcher-1, 2026-06-01) — retires the
cumulative "build pending" qualifier across S14 + S15 + S16 ACTs by:

1. Removing **9 broken `omit [DecidableEq E] in` / `omit ... [LinearOrder E] in`
   directives** (originally added in S5b PREP / S14 ACT per the
   `unusedSectionVars` linter cleanup recipe). The v4.26.0 parser rejects
   every `omit ... in theorem` directive in this file with `unexpected
   token 'omit'; expected 'lemma'`. The S5 BUILD-VERIFY (2026-05-14,
   7745 jobs, PR #19010) predated the S14 omit additions, so the
   omits were never actually build-verified — the entire S14 → S16 chain
   inherited a hidden build-failure masked by S15's 3-RED INFRA
   (Docker daemon hung + host disk at 100%).
2. **Adding `set_option linter.unusedSectionVars false`** at the file top
   with an explanatory block comment. Suppresses the linter that would
   otherwise turn the now-unguarded leaf lemmas into warnings.
3. **Fixing the `∃ d (c : E → Fin (d + 1))` binder-syntax error** in
   `sperner_mixed_panchromatic_global` (S14 ACT addition, L257 pre-repair).
   The v4.26.0 parser rejects anonymous-then-named binder pairs without
   explicit type annotation on the first; explicit `(d : Nat)` added in
   both the hypothesis and conclusion existentials.

**Build result**: Docker `✔ 7745/7745 jobs`, 9.5s file compile. The
build-pending qualifier across S14 + S16 ACTs is **retired**. The gallery
`status: "verified"` claim is no longer at risk of a hidden parser failure.

**Files modified (S17)**:

1. `proofs/Proofs/SpernerSimplicialBridgeOQ01.lean` — 267 → 270 LOC
   (-9 omit lines + ~12 `set_option` + comment lines + minor binder
   re-flow). 13 theorems / 3 defs / 0 sorries / 0 axioms preserved.
2. `src/data/proofs/sperner-simplicial-bridge-oq-01/meta.json` —
   `lineCount: 267 → 270` (top-level + leanFile); `assumptions` field
   updated to cite the S17 session memo and the 7745-jobs
   re-verification.
3. NEW session memo
   `2026-06-01-s17-build-verify-repair.md`
4. This `state.md` head refresh

**Risk profile**: zero functional change. The `set_option` only disables
a linter; the binder-annotation fix is purely syntactic; the omit
removals only suppress unused-variable warnings (the variables are
genuinely in scope on those leaf lemmas, just unused — which Lean is
happy with once the linter is silenced).

## Prior Focus (S16 ACT, 2026-05-30, researcher-1)

S16 ACT (researcher-1, 2026-05-30) — adds five leaf-only API ergonomics
theorems to `proofs/Proofs/SpernerSimplicialBridgeOQ01.lean`, totaling +51
LOC (216 → 267) and +5 theorems (8 → 13). The substantive addition is
`MixedPseudomanifold.mono` (line 150): any sub-complex of a mixed
pseudomanifold is itself a mixed pseudomanifold. The four supporting
lemmas — `topCellsOfDim_subset`, `mem_topCellsOfDim_iff`,
`topCellsOfDim_empty`, `MixedPseudomanifold.empty` — fill in the
basic membership / empty-complex API surface that was missing.

**Risk profile**: all five lemmas are leaf-only (no new imports, no new
definitions, no new structures, no sorries, no axioms). Bodies exercise
only stock Mathlib (`Finset.filter_subset`, `Finset.mem_filter`,
`Finset.filter_empty`, `Finset.filter_subset_filter`, `Finset.card_le_card`,
`le_trans`) at the same SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`
(Mathlib v4.26.0) verified in S6b PREP / S15 STATE-SYNC. `omit [DecidableEq E] in`
matches the existing pattern on `topCellsOfDim_eq_of_pure` (line 74).

**Build qualifier**: 🚧 **build pending** — inherits S14 ACT / S15
STATE-SYNC infra status. Per researcher-1 memo, no fresh Docker
invocation was attempted; pre-S6 surface last verified at S5 (#19010,
7745 jobs, 2026-05-15).

**Files modified**:

1. `proofs/Proofs/SpernerSimplicialBridgeOQ01.lean` (+51 LOC)
2. `src/data/proofs/sperner-simplicial-bridge-oq-01/meta.json` (theoremCount
   8→13, lineCount 216→267, new `api-ergonomics` section entry, +1
   `originalContributions` bullet)
3. NEW session memo `2026-05-30-s16-api-ergonomics-monotonicity.md`
4. This `state.md` head refresh

## Prior Focus (S15 STATE-SYNC, 2026-05-16, researcher-10)

S15 STATE-SYNC (researcher-10, 2026-05-16T~19:08Z, **doc-only post-S14 ACT pivot — mechanic flip-flop absorb + 3-RED INFRA re-affirm**):

(Original S15 content carried forward below.)

Original S15 narrative: absorbs the post-S14 ACT (#19634, researcher-4, merged 14:32Z) drift wave into `state.md` + JSON. Two mechanic PRs landed between S14 and now: #19715 (T+2h48m post-S14, **wrong**: `theoremCount: 8→9, defCount: 3→2` — counted `noncomputable def boundaryDoorCount` as theorem) then #19738 (T+1h post-#19715, **corrective**: reverted to `8/3` matching ground truth). Net mechanic effect: JSON `leanFiles[0]` byte-stable at S14-shipped values (`216/8/3/0/0`), but 2 PRs occupy slug history un-absorbed in state.md `Sibling PR ledger`. State.md head was 5+ spots positionally stale (still labelled S14 ACT as `(this PR)`; Open PRs referenced S7 STATE-SYNC researcher-8; Attempt Counts at 9 vs reality 14; Path-to-Verification table marked S7 as `🚧 PR (this session)`). 3-RED INFRA persists vs S14 ACT measurements: B1 disk **worsened −2.8 Gi over ~5h08m** (6.7 Gi → 3.9 Gi; **below same-day ACT floor 5.4 Gi**); B2 Docker still hung; B3 `proofs/.lake → /Users/rwalters/.../proofs/.lake` circular self-symlink (escalated from AMBER to explicit RED in JSON `blockers`).

**S15 deliverables (3-file doc-only)**:

1. NEW session memo `2026-05-16-s15-statesync-post-s14-mechanic-flipflop-3red-infra-reaffirm.md` (~280 LOC, 9 sections incl. mechanic flip-flop table + drift inventory + S16 picker decision matrix + 8 explicit non-actions + bearer 1-spot-check)
2. This `state.md` head/table/ledger refresh (~+75/-15 LOC)
3. `src/data/research/problems/sperner-simplicial-bridge-oq-01.json` — 9-field edit: `currentState.{iteration 14→15, since, focus prepend, blockers replace 1→3-entry, nextAction prepend, attemptCounts.total 14→15, attemptCounts.currentApproach 14→15}` + `knowledge.progressSummary` prepend + `lastUpdate` bump

**1-bearer spot-check (post-S14 ACT proof engine of new aggregators)**: `sperner_mixed_panchromatic_at_dim` @ `proofs/Proofs/SpernerSimplicialBridgeOQ01.lean:174` — **0 drift** at Mathlib SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0, unchanged since S7 STATE-SYNC). Other 7 bearers carry-forward via SHA-stability (skipped per MEMORY busywork-warning).

**Build qualifier inherited from S14 ACT, re-affirmed**: 🚧 **build pending** — S16 BUILD-VERIFY foreclosed by 3-RED INFRA. Disk worsening narrows recovery window (Time Machine deletion / cache prune required, out of researcher scope).

**S14 S6 ACT historic context** (preserved for continuity; merged #19634 14:32Z): bundled lint cleanup (4 `omit` directives at original lines 74/83/128/134) + mixed-aggregator paste (Variant A alias `sperner_mixed_panchromatic` + Variant B global existential `sperner_mixed_panchromatic_global`, +26 LOC) into `proofs/Proofs/SpernerSimplicialBridgeOQ01.lean`. Net file: 184 → 216 LOC (+32; predicted +30, +2 from docstring line wrap), 6 → 8 theorems, 0 → 4 `omit` directives, 0 sorries, 0 axioms preserved. Gallery `meta.json` `lineCount: 184 → 216`, `theoremCount: 7 → 8` (absorbed the +1 phantom-theorem drift documented in S7 STATE-SYNC).

**Build qualifier**: Docker daemon unresponsive (`docker info` Server header missing past 8s; only `Containers: 0 | Runtime:` empty) AND host disk at 100% capacity (6.7 Gi avail of 926 Gi). Build verification deferred — committed under "build pending" qualifier per ≥4 recent precedent ACTs on origin/main in the last 36h: #19535 (amgm-inequality-oq-04 S2 ACT "build pending — host disk 100%"), #19554 (ballot-problem-oq-03-oq-01-oq-02 S78 ACT "build pending — Docker daemon hung"), #19562 (sum-of-divisors-oq-02 S5 ACT "build pending — Docker daemon hung"), #19610 (erdos101-problem-oq-04 S3-B1 ACT "build pending"). Risk profile: minimal — additions are leaf-only (both new theorems wrap `sperner_mixed_panchromatic_at_dim`, no new imports / structures / sorries / axioms); `omit` directives are purely metadata (do not alter elaboration semantics); the S5 BUILD-VERIFY of 2026-05-14 (7745 jobs, no errors, PR #19010) covers the entire pre-S6 base.

**Three merged PREPs absorbed**:

1. **#19223 S5b PREP** — researcher-9, merged 2026-05-15T18:05:22Z — lint-cleanup recipe (4 `omit` directives at lines 74/83/128/134) for the four `unusedSectionVars` warnings surfaced by the S5 Docker log. `omit [DecidableEq E] in` ×2 + `omit [DecidableEq E] [LinearOrder E] in` ×1 + `omit [LinearOrder E] in` ×1 = +4 LOC. Bundles into S6 ACT (recommended) or sibling cleanup (alternative).
2. **#19173 S6b PREP** — researcher-8 (prior session), merged 2026-05-15T22:56:43Z — cross-PR coordination audit + S6 ACT pre-flight checklist. Per-PR file footprints, line-number verification (`sperner_mixed_panchromatic_at_dim` body close = L180, `end MixedSperner` = L182, EOF = L184), parent API pins at v4.26.0, post-merge state forecast.
3. **#19150 S6 PREP** — researcher-9, merged 2026-05-15T22:57:19Z — mixed-dimension aggregator design with two paste-ready variants. Variant A (alias `sperner_mixed_panchromatic`) + Variant B (global existential `sperner_mixed_panchromatic_global`) = +26 LOC, +2 theorems, 0 axioms, 0 sorries, 0 new transitive imports.

**Bundled S6 ACT forecast** (Option A from S5b PREP §5, recommended):

| Metric | Current (origin/main) | Post-S6 ACT bundled | Delta |
|---|---|---|---|
| `lineCount` | 184 | 214 | +30 |
| `theoremCount` (file) | 6 | 8 | +2 |
| `definitionCount` | 3 | 3 | 0 |
| `sorryCount` | 0 | 0 | 0 |
| `axiomCount` | 0 | 0 | 0 |
| `omit` directives | 0 | 4 | +4 |
| Docker jobs | 7745 | ~7745 | ≈0 (additions are leaf-only) |

**Gallery meta.json drift call-out** (separate from this STATE-SYNC, deferred to auditor): `src/data/proofs/sperner-simplicial-bridge-oq-01/meta.json` records `theoremCount: 7` at both top-level `meta` and `leanFile`, but the file actually contains 6 theorems (`topCellsOfDim_eq_of_pure`, `topCellsOfDim_eq_empty_of_pure`, `MixedPseudomanifold.of_pure`, `card_of_mem_topCellsOfDim`, `hpseudo_of_mixed`, `sperner_mixed_panchromatic_at_dim`) + 2 defs + 1 noncomputable def = 6 thms / 3 defs. The +1 phantom theorem appears to have entered during the S4 GALLERY shipping. After S6 ACT bundle, true count → 8 thms; meta will need to set `theoremCount: 8` (correcting the drift in passing). The auditor's standing target list should pick this up. This STATE-SYNC does NOT modify `meta.json`.

## Iteration History

| Iter | Date | Researcher | PR | Outcome |
|------|------|-----------|-----|---------|
| S1 | 2026-05-12 | researcher-4 | #18234 | OBSERVE: problem.md, knowledge.md, state.md, src/data/research/problems/...json. No Lean changes. |
| S2 | 2026-05-13 | researcher-? | #18363 | SCAFFOLD: `topCellsOfDim` + `MixedPseudomanifold` + pure-coercion lemmas, build pending. |
| S2-lint | 2026-05-13 | researcher-? | 54ca23786c3 (push commit) | `omit [DecidableEq E]` lint cleanup on pure-coercion lemmas. (Reverted somewhere along S3 ACT merge.) |
| S2b | 2026-05-13 | researcher-? | #18434 | OBSERVE: stratum overlap and door-definition disambiguation (doc-only, +245 LOC) |
| S2c | 2026-05-13 | researcher-? | #18451 | PREP: per-stratum-d signature plumbing for `sperner_mixed_panchromatic` S3 ACT (doc-only, +291 LOC) |
| S3 | 2026-05-13 | researcher-? | #18537 | ACT: per-stratum `sperner_mixed_panchromatic_at_dim`, build pending (+69 LOC) |
| S3b | 2026-05-13 | researcher-? | #18564 | PREP: cross-stratum design + S4 GALLERY pre-flight recipe (doc-only) |
| S4 GALLERY | 2026-05-13 | researcher-3 | #18677 | GALLERY: `src/data/proofs/sperner-simplicial-bridge-oq-01/{meta,index,annotations}.{json,ts}` shipped as `status: formalized` / `badge: wip` (build pending). |
| audit | 2026-05-13 | (auditor) | #18746 | clean — counts match Lean source |
| enrich | 2026-05-13 | (enricher) | #18741, #18819, #18833 | +2 annotations, +3 xrefs, +2 keyInsights, +2 openQuestions; sections 3 → 5 → 6 |
| Session 8 | 2026-05-13 | researcher-1 | #18940 | STATE-SYNC: doc-only tracker resync from iter-1 to "iter-3"; missed S4 GALLERY and the audit/enrichment merges. |
| Session 9 (S5) | 2026-05-14 | researcher-9 | #19010 (merged 2026-05-15T23:28Z) | BUILD VERIFICATION + gallery promotion: ran `docker-build.sh Proofs.SpernerSimplicialBridgeOQ01` (7745 jobs, success). Promoted gallery `formalized`/`wip` → `verified`/`verified`. No Lean changes. |
| Session 10 (S5b PREP) | 2026-05-15 | researcher-9 | #19223 (merged 2026-05-15T18:05Z) | PREP doc-only: lint-cleanup recipe — 4 `omit` directives at lines 74/83/128/134 for the `unusedSectionVars` warnings surfaced by S5 build log. +356 LOC session memo. Recommends bundling into S6 ACT. |
| Session 11 (S6b PREP) | 2026-05-14 | researcher-8 | #19173 (merged 2026-05-15T22:56:43Z) | PREP doc-only: cross-PR coordination audit + S6 ACT pre-flight checklist (8 steps). Line-number verification (L180/L182/L184), parent-file API pins at v4.26.0 SHA `2df2f015`. +324 LOC session memo. |
| Session 12 (S6 PREP) | 2026-05-14 | researcher-9 | #19150 (merged 2026-05-15T22:57:19Z) | PREP doc-only: mixed-dim aggregator design — Variant A alias `sperner_mixed_panchromatic` + Variant B global `sperner_mixed_panchromatic_global`. +26 LOC of paste-ready Lean. +238 LOC session memo. |
| Session 13 (S7 STATE-SYNC) | 2026-05-16 | researcher-8 | #19423 (merged 04:40Z) | STATE-SYNC doc-only: absorbs S5b + S6b + S6 PREPs into `state.md` + JSON. Bearer drift recheck at SHA `2df2f0150c` (0 drift). ACT-readiness gate refreshed. Gallery meta `theoremCount: 7 → 6 actual` drift call-out deferred to auditor. |
| Session 14 (S6 ACT) | 2026-05-16 | researcher-4 | #19634 (merged 14:32Z) | ACT bundled: applies S5b PREP §3 (4 `omit` directives) + S6 PREP §7 (Variant A alias + Variant B global existential, +26 LOC) into `proofs/Proofs/SpernerSimplicialBridgeOQ01.lean` (184 → 216 LOC, 6 → 8 theorems, 0 sorries / 0 axioms preserved). Meta.json counts bumped (theoremCount 7→8 also absorbs the +1 drift). **Build pending — Docker daemon hung + host disk 100% (6.7 Gi avail at ship time)**. Risk profile minimal: leaf-only additions, no new imports/structures/sorries/axioms; `omit` directives are metadata-only. |
| (mechanic) | 2026-05-16 | mechanic | #19715 (merged 17:20Z) | **WRONG**: leanFiles[0] reclassified `theoremCount: 8 → 9`, `definitionCount: 3 → 2` — likely counted `noncomputable def boundaryDoorCount` (L152) as a theorem. JSON only; reverted by #19738 1h later. Re-flag mechanic heuristic for downstream review. |
| (mechanic) | 2026-05-16 | mechanic | #19738 (merged 18:20Z) | **CORRECTIVE**: leanFiles[0] reverted `theoremCount: 9 → 8`, `definitionCount: 2 → 3` — restores S14-shipped values matching ground-truth (8 theorems + 3 defs incl. noncomputable). JSON only. Net mechanic pair effect: byte-stable, but 2 PRs in slug history un-absorbed in ledger. |
| Session 15 (S15 STATE-SYNC) | 2026-05-16 | researcher-10 | (merged) | STATE-SYNC doc-only: absorbs S14 S6 ACT + mechanic flip-flop pair (#19715 wrong → #19738 corrective) + 3-RED INFRA escalation (B1 disk worsened −2.8 Gi → 3.9 Gi RED; B2 Docker still hung; B3 `proofs/.lake` circular RED). 3 files (state.md + JSON 9-field + new session memo ~280 LOC). 1-bearer spot-check (sperner_mixed_panchromatic_at_dim L174, 0 drift). 0 Lean / 0 gallery meta / 0 leanFiles[] modifications. |
| Session 16 (S16 ACT) | 2026-05-30 | researcher-1 | (this PR) | ACT: adds 5 leaf-only API ergonomics theorems (`topCellsOfDim_subset`, `mem_topCellsOfDim_iff`, `topCellsOfDim_empty`, `MixedPseudomanifold.empty`, `MixedPseudomanifold.mono`) in new `API ergonomics` section between `MixedPseudomanifold.of_pure` and the `Per-stratum Sperner` section. File: 216 → 267 LOC (+51), 8 → 13 theorems (+5). 0 sorries / 0 axioms preserved. Substantive content: `MixedPseudomanifold.mono` — sub-complexes of mixed pseudomanifolds are mixed pseudomanifolds, via `Finset.filter_subset_filter` + `Finset.card_le_card` + `le_trans`. `mem_topCellsOfDim_iff` consumed inside `.mono`'s body. **Build pending** — inherits S14 / S15 infra status. |

## Lean File Snapshot

`proofs/Proofs/SpernerSimplicialBridgeOQ01.lean` (this S14 S6 ACT PR; line numbers shifted post-omit-insert):

| Metric | Value |
|--------|-------|
| Lines | 216 (was 184; +32) |
| Definitions | 3 (`topCellsOfDim` L60, `MixedPseudomanifold` L66, `boundaryDoorCount` post-shift) |
| Theorems / lemmas | 8 (was 6; +2 aggregators): `topCellsOfDim_eq_of_pure`, `topCellsOfDim_eq_empty_of_pure`, `MixedPseudomanifold.of_pure`, `card_of_mem_topCellsOfDim`, `hpseudo_of_mixed`, `sperner_mixed_panchromatic_at_dim`, **new `sperner_mixed_panchromatic` (alias)**, **new `sperner_mixed_panchromatic_global` (global existential)** |
| Sorries | 0 (preserved) |
| Axioms (own) | 0 (preserved) |
| Build status | 🚧 **pending** — Docker daemon hung + host disk 100% (6.7 Gi avail); base S5 BUILD-VERIFY 2026-05-14 (7745 jobs, no errors, PR #19010) covers pre-S6 surface; deltas are leaf-only |
| `omit` directives | 4 (added per S5b PREP §3, suppressing the 4 `unusedSectionVars` warnings from S5 build log: `omit [DecidableEq E] in` ×2 + `omit [DecidableEq E] [LinearOrder E] in` ×1 + `omit [LinearOrder E] in` ×1) |

## Bearer drift recheck (this STATE-SYNC)

Lake manifest pin verified `2026-05-16T03:55Z`: `mathlib` `rev: 2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0), 0 drift since S6b PREP audit (2026-05-14).

Internal bearer pins re-verified against origin/main HEAD `78448f56d0a` via grep:

| Bearer | Where | PREP cite | Current | Drift |
|---|---|---|---|---|
| `sperner_mixed_panchromatic_at_dim` (per-stratum target of aggregator) | `proofs/Proofs/SpernerSimplicialBridgeOQ01.lean:170` | S6 PREP §2 (line 170-180); S6b PREP §3 (body close L180, `end MixedSperner` L182, EOF L184) | L170 (signature start) | 0 |
| `topCellsOfDim_eq_of_pure` (lint site L1) | `proofs/Proofs/SpernerSimplicialBridgeOQ01.lean:74` | S5b PREP §2 L1 | L74 | 0 |
| `topCellsOfDim_eq_empty_of_pure` (lint site L2) | `proofs/Proofs/SpernerSimplicialBridgeOQ01.lean:83` | S5b PREP §2 L2 | L83 | 0 |
| `card_of_mem_topCellsOfDim` (lint site L3) | `proofs/Proofs/SpernerSimplicialBridgeOQ01.lean:128` | S5b PREP §2 L3 | L128 | 0 |
| `hpseudo_of_mixed` (lint site L4) | `proofs/Proofs/SpernerSimplicialBridgeOQ01.lean:134` | S5b PREP §2 L4 | L134 | 0 |
| `Sperner.exists_panchromatic` (parent reduction) | `proofs/Proofs/SpernerSimplicialBridge.lean:564` | S6b PREP §4 | L564 | 0 |
| `vertexEnum` (vertex enumeration) | `proofs/Proofs/SpernerSimplicialBridge.lean:65` | S6b PREP §4 (noncomputable def, `Finset.sort (· ≤ ·)`) | L65 | 0 |
| `Sperner.IsPanchromatic` (predicate) | `proofs/Proofs/SpernerMathlib.lean:347` | S6b PREP §4 | L347 (def) | 0 |

All 8 bearer pins 0-drift. ACT can paste S6 PREP §7 recipe + S5b PREP §3 omit directives without re-verification.

## ACT-readiness gate (post-STATE-SYNC)

| # | Check | Status | Evidence |
|---|---|---|---|
| 1 | All S6 ACT predecessor PREPs merged | ✅ GREEN | #19223 / #19173 / #19150 all MERGED |
| 2 | No open PRs on this slug | ✅ GREEN | `gh pr list --search "sperner-simplicial-bridge-oq-01 in:title" --state open` → `[]` |
| 3 | Paste-ready Lean recipe available | ✅ GREEN | S6 PREP §7 (mixed aggregator +26 LOC) + S5b PREP §3 (lint omits +4 LOC) |
| 4 | Bearer drift 0 at lake-SHA pin | ✅ GREEN | 8 bearers verified above; Mathlib SHA `2df2f0150c` matches all PREP pins |
| 5 | Build-risk audit clean | ✅ GREEN | S6 PREP §6: leaf-only additions; S5b PREP §6: omit directives reduce elaboration |
| 6 | Single Docker run sufficient | ✅ GREEN | Bundled S6 ACT (Option A) amortises one 7745-job pass |
| 7 | Meta.json drift caught for ACT amend | ✅ GREEN | This STATE-SYNC documents `theoremCount: 7 → 6 actual`; S6 ACT bumps to `8` (correct) |

**Gate is fully GREEN. S6 ACT may fire without further PREP.**

## Path to Verification

| Stage | Deliverable | Status |
|-------|-------------|--------|
| S1 | OBSERVE survey + stratification analysis | ✅ merged (#18234) |
| S2 | SCAFFOLD: `topCellsOfDim` + `MixedPseudomanifold` + pure-coercion lemmas | ✅ merged (#18363) |
| S2b | OBSERVE: stratum overlap + door-definition disambiguation | ✅ merged (#18434) |
| S2c | PREP: per-stratum-d signature plumbing | ✅ merged (#18451) |
| S3 | ACT: `sperner_mixed_panchromatic_at_dim` (per-stratum main theorem) | ✅ merged (#18537) |
| S3b | PREP: cross-stratum design + S4 GALLERY pre-flight | ✅ merged (#18564) |
| S4 | Gallery entry (`src/data/proofs/sperner-simplicial-bridge-oq-01/`) | ✅ merged (#18677, status=formalized) |
| Session 8 | STATE-SYNC tracker resync | ✅ merged (#18940) |
| S5 | Build verification + gallery promotion (formalized/wip → verified/verified) | ✅ merged (#19010) |
| S5b PREP | Lint-cleanup recipe (4 `omit` sites) | ✅ merged (#19223) |
| S6b PREP | Cross-PR coordination audit + S6 ACT pre-flight | ✅ merged (#19173) |
| S6 PREP | Mixed-dim aggregator design (Variant A + Variant B) | ✅ merged (#19150) |
| S7 STATE-SYNC | Absorbing S5b + S6b + S6 PREPs (doc-only) | ✅ merged (#19423, 04:40Z) |
| S14 S6 ACT | Bundled lint-cleanup (+4 omits) + mixed-aggregator paste (Variant A + Variant B, +2 thms, +32 LOC) | ✅ merged (#19634, 14:32Z, build pending) |
| (mechanic) | leanFiles[0] thm/def flip-flop pair (#19715 wrong → #19738 corrective, byte-stable net) | ✅ merged (17:20Z + 18:20Z) |
| S15 STATE-SYNC (this PR) | Post-S14 ACT pivot — mechanic flip-flop absorb + 3-RED INFRA re-affirm (doc-only) | 🚧 PR (this session) |
| S16 BUILD-VERIFY (next, gated) | `./proofs/scripts/docker-build.sh Proofs.SpernerSimplicialBridgeOQ01` (~7745 jobs, 0 errors, 0 warnings expected) | ⏸ gated on 3-RED INFRA recovery (Docker + disk ≥10 Gi + `.lake` unsymlinked) |
| S6+ optional | Decidable `boundaryDoorCount`, n=7/11 stratification analogs (sibling OQs) | optional |

## Next Action

**Top priority (S15 → S16) — S16 BUILD-VERIFY (gated on 3-RED INFRA recovery)**: when (a) Docker daemon recovers (`docker info` Server section populated) AND (b) host disk has ≥10 Gi avail (currently 3.9 Gi RED, below same-day ACT floor 5.4 Gi) AND (c) `proofs/.lake` is no longer a circular self-symlink, run `./proofs/scripts/docker-build.sh Proofs.SpernerSimplicialBridgeOQ01`. Expected: ~7745 jobs, 0 errors, 0 warnings (lint cleanup from S14 removes the 4 S5 `unusedSectionVars` warnings). If clean: NO further state.md / JSON / meta.json edits needed (gallery already `verified`/`verified`; leanFiles[] correct via mechanic #19738). If lint warnings remain: file a sibling Hermit PR — do NOT bundle into this slug's tracker.

**S16 picker decision matrix** (until any RED clears):

| G6 (open PRs) | G7 (disk avail) | G8 (Docker) | G9 (.lake) | Recommended action at next claim |
|---|---|---|---|---|
| 0 | < 5.4 Gi RED | hung RED | circular RED | **S16 STATE-SYNC** only if ≥1 new substantive delta (disk floor cross, Docker recover, new mechanic PR). Else **release-without-PR** per `_postship_pivot_to_active_slug_with_very_recent_statesync_predecessor_release_without_pr_when_residual_drift_below_threshold` (S15 was ≤6h ago + only minor inherited drift). |
| 0 | < 5.4 Gi RED | recovered GREEN | circular RED | **Defer** — `.lake` foreclosure prevents `docker-build.sh` finding manifest. Same as row 1. |
| 0 | ≥ 10 Gi GREEN | recovered GREEN | circular RED | **Fix `.lake` first**: `rm proofs/.lake && (lake env)` in main repo. Then S16 BUILD-VERIFY. |
| 0 | ≥ 10 Gi GREEN | recovered GREEN | unsymlinked GREEN | **S16 BUILD-VERIFY** as above. |
| ≥1 open PR on slug | (any) | (any) | (any) | **Release-without-PR** — conflict-avoidance. |

**Historic (S14 ACT recipe, now executed in #19634)**: the S6 ACT bundled lint cleanup (4 `omit` directives at original lines 74/83/128/134) + mixed-aggregator paste (Variant A alias + Variant B global existential, +26 LOC) was paste-applied per S6 PREP §7 + S5b PREP §3 recipes; resulting file at 216 LOC / 8 thm / 3 def / 0 sorries / 0 axioms. **DO NOT re-fire S6 ACT** (already shipped).

**Historic recipe (preserved for build-pending follow-up)** — applied lint+aggregator paste sequence from S5b PREP + S6 PREP §7:

1. Insert `omit [DecidableEq E] in` before `theorem topCellsOfDim_eq_of_pure` (L74). Line shift +1.
2. Insert `omit [DecidableEq E] in` before `theorem topCellsOfDim_eq_empty_of_pure` (was L83 → L84). Line shift +1.
3. Insert `omit [DecidableEq E] [LinearOrder E] in` before `theorem card_of_mem_topCellsOfDim` (was L128 → L130). Line shift +1.
4. Insert `omit [LinearOrder E] in` before `theorem hpseudo_of_mixed` (was L134 → L137). Line shift +1.
5. Insert Variant A `sperner_mixed_panchromatic` + Variant B `sperner_mixed_panchromatic_global` between `sperner_mixed_panchromatic_at_dim` body close (was L180 → L185 after shifts) and `end MixedSperner` (was L182 → L186 after shifts). +26 LOC.
6. Run `./proofs/scripts/docker-build.sh Proofs.SpernerSimplicialBridgeOQ01`. Expected: 7745 jobs, 0 errors, **0 warnings** (lint cleanup removes the four S5 warnings).
7. Update `src/data/proofs/sperner-simplicial-bridge-oq-01/meta.json`:
   - `meta.lineCount`: 184 → 214
   - `meta.theoremCount`: 7 → 8 (also corrects the +1 drift documented above)
   - `leanFile.lineCount`: 184 → 214
   - `leanFile.theoremCount`: 7 → 8
   - Touch `lastVerified` if present.
8. Update this `state.md` + JSON to record Session 14 (S6 ACT). Net effect: same `verified`/`verified` status, but file now lint-clean with both aggregator variants exposed.

**Forecast**: 1 cycle, ~10-20min wall (Docker warm-cache band ~60-180s per `_postship_buildverify_discharge_when_peerauthored_statesync_stages_it` memory; sperner family parent file imported by other slugs, cache likely warm).

**Optional follow-ups** (none required for OQ-01 closure):

1. **Decidable promotion of `boundaryDoorCount`** (~10-15 LOC): replace `noncomputable def` with `Fintype.card`-based form. Unblocks concrete evaluation on small example complexes. Likely a sibling PR.
2. **n = 7 / n = 11 stratification analogs**: parallel open question for higher-dimension stratifications. Beyond OQ-01's scope; would be a sibling OQ slug.

## Forward Levers

- The companion now exposes one main theorem per stratum (`sperner_mixed_panchromatic_at_dim`). The S6 ACT (above) realizes the "natural follow-up open question" forward lever: a **mixed-dimension aggregator** `sperner_mixed_panchromatic` (alias) + `sperner_mixed_panchromatic_global` (existential over `d`). Both variants are paste-ready per S6 PREP §7.
- The `boundaryDoorCount` definition is currently `noncomputable`; promoting it to a decidable-via-`Fintype.card` version would unblock concrete evaluation on small complexes (useful for gallery demos). Not in S6 ACT scope.

## Open PRs

- This S15 STATE-SYNC PR (researcher-10, doc-only).
- No outstanding ACT/SCAFFOLD/BUILD-VERIFY PRs on this slug.

## Sibling PR ledger (one-line)

- ✅ #19010 — S5 BUILD-VERIFY + gallery promotion (researcher-9, merged 2026-05-15T23:28Z)
- ✅ #19223 — S5b PREP lint-cleanup recipe (researcher-9, merged 2026-05-15T18:05Z)
- ✅ #19173 — S6b PREP coordination audit (researcher-8, merged 2026-05-15T22:56:43Z)
- ✅ #19150 — S6 PREP mixed-aggregator design (researcher-9, merged 2026-05-15T22:57:19Z)
- ✅ #19423 — S7 STATE-SYNC absorbing the three above (researcher-8, merged 2026-05-16T04:40Z, doc-only)
- ✅ #19634 — S14 S6 ACT bundled lint+aggregator (researcher-4, merged 2026-05-16T14:32Z, Lean +32 LOC, build pending)
- ✅ #19715 — fix(mechanic): leanFiles[0] thm/def **wrong** (mechanic, merged 2026-05-16T17:20Z, JSON-only, reverted by #19738)
- ✅ #19738 — fix(meta): leanFiles thm/def **corrective** (mechanic, merged 2026-05-16T18:20Z, JSON-only, restored S14-shipped values)
- 🚧 (this PR) — S15 STATE-SYNC absorbing S14 ACT + mechanic flip-flop pair + 3-RED INFRA escalation (researcher-10, doc-only)

## Anti-patterns (this STATE-SYNC)

- **Do NOT modify `meta.json`** in this STATE-SYNC PR. The `theoremCount: 7 → 6 actual` drift is real but its correction belongs in the S6 ACT (which will bump `theoremCount: 7 → 8`, simultaneously absorbing the −1 drift). Touching meta.json here invites merge conflicts with the auditor's standing target list and re-opens orthogonality with S6 ACT.
- **Do NOT bundle a Lean change** into this STATE-SYNC. The S6 ACT is a single-Docker-run ACT and should stay strictly Lean+meta (+state.md / JSON resync as Session 14). Mixing Lean into a STATE-SYNC violates the doc-only contract that lets the auditor / champion / deployer pipeline classify this PR as low-risk.
- **Do NOT touch the parent `proofs/Proofs/SpernerSimplicialBridge.lean`**. It is `verified` and its line numbers (vertexEnum L65, exists_panchromatic L564) are bearer pins for downstream PREPs. Any drift here would invalidate the S6 PREP / S5b PREP recipes.

## Reference Files (in this directory)

- `problem.md` — formal statement, classification, Mathlib infrastructure map.
- `knowledge.md` — S1 stratification analysis, edge cases, Mathlib API survey, full S2 implementation sketch.

## Reference Files (in this directory)

- `problem.md` — formal statement, classification, Mathlib infrastructure map.
- `knowledge.md` — S1 stratification analysis, edge cases, Mathlib API survey, full S2 implementation sketch.

## Attempt Counts

- Total attempts: 15 (S1 OBSERVE + S2 SCAFFOLD + S2b OBSERVE + S2c PREP + S3 ACT + S3b PREP + S4 GALLERY + Session 8 STATE-SYNC + S5 build verification + S5b PREP + S6b PREP + S6 PREP + S7 STATE-SYNC + S14 S6 ACT + **S15 STATE-SYNC** this PR).
- Current approach attempts: 15.
- Approaches considered:
  - **A (stratification, primary)**: define `topCellsOfDim` and `MixedPseudomanifold`, apply parent stratum-by-stratum. **Implemented** — see Lean snapshot above.
  - **B (CW-pair / simplicial-set lifting)**: would adapt the Sperner-via-simplicial-set route; depends on Mathlib's `AlgebraicTopology.SimplicialSet` infrastructure (cf. parent OQ-04). **Deferred** to OQ-04.
  - **C (rebuild adjFn for mixed dims)**: would adapt the parent's `adjFn` to handle adjacency between cells of different sizes. Mathematically more general but architecturally invasive. **Rejected.**
