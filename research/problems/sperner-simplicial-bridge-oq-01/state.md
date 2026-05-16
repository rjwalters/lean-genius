# Current State

**Phase**: REFINEMENT (gallery `verified`/`verified`; OPTIONAL S6 ACT now PASTE-READY: mixed-dim aggregator + 4 lint omits, +30 LOC, 1 Docker run)
**Since**: 2026-05-16T03:55:00Z
**Iteration**: 13 (S5 → S5b PREP → S6b PREP → S6 PREP → **S7 STATE-SYNC (this PR)**)

## Current Focus

S7 STATE-SYNC (researcher-8, 2026-05-16, **doc-only post-PREP-drain catch-up**): three doc-only PREPs landed in a single drain wave 2026-05-15T18:05 → 22:57Z, none reflected in `state.md` / JSON tracker since the prior S5 BUILD-VERIFY catch-up (PR #19010, 2026-05-15T23:28Z merge). This STATE-SYNC absorbs the three PREPs, re-pins bearers at lake-manifest SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (Mathlib v4.26.0, 0 drift), refreshes the ACT-readiness gate, and stages the now-fully-planned S6 ACT (single Docker run, +30 LOC, single `meta.json` bump).

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
| Session 13 (S7 STATE-SYNC) | 2026-05-16 | researcher-8 | (this PR) | STATE-SYNC doc-only: absorbs S5b + S6b + S6 PREPs into `state.md` + JSON. Bearer drift recheck at SHA `2df2f0150c` (0 drift). ACT-readiness gate refreshed. Gallery meta `theoremCount: 7 → 6 actual` drift call-out deferred to auditor. |

## Lean File Snapshot

`proofs/Proofs/SpernerSimplicialBridgeOQ01.lean` (origin/main HEAD `78448f56d0a`, unchanged since S3 ACT #18537 of 2026-05-13T03:32Z):

| Metric | Value |
|--------|-------|
| Lines | 184 |
| Definitions | 3 (`topCellsOfDim` L60, `MixedPseudomanifold` L66, `boundaryDoorCount` L148 noncomputable) |
| Theorems / lemmas | 6 (`topCellsOfDim_eq_of_pure` L74, `topCellsOfDim_eq_empty_of_pure` L83, `MixedPseudomanifold.of_pure` L97, `card_of_mem_topCellsOfDim` L128, `hpseudo_of_mixed` L134, `sperner_mixed_panchromatic_at_dim` L170) |
| Sorries | 0 |
| Axioms (own) | 0 |
| Build status | ✅ verified 2026-05-14 — `docker-build.sh Proofs.SpernerSimplicialBridgeOQ01` succeeded (7745 jobs) |
| `omit` directives | 0 (4 sites pending per S5b PREP) |

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
| S7 (this PR) | STATE-SYNC absorbing S5b + S6b + S6 PREPs (doc-only) | 🚧 PR (this session) |
| S6 ACT (next) | Bundled lint-cleanup + mixed-aggregator paste from S5b/S6 PREP recipes (+30 LOC, 1 Docker run) | ⏸ ready |
| S6+ optional | Decidable `boundaryDoorCount`, n=7/11 stratification analogs (sibling OQs) | optional |

## Next Action

**Top priority — S6 ACT (bundled, single Docker run)**: paste S6 PREP §7 + S5b PREP §3 recipes into `proofs/Proofs/SpernerSimplicialBridgeOQ01.lean`:

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

- This S7 STATE-SYNC PR (researcher-8, doc-only).
- No outstanding ACT/SCAFFOLD/BUILD-VERIFY PRs on this slug post-drain.

## Sibling PR ledger (one-line)

- ✅ #19010 — S5 BUILD-VERIFY + gallery promotion (researcher-9, merged 2026-05-15T23:28Z)
- ✅ #19223 — S5b PREP lint-cleanup recipe (researcher-9, merged 2026-05-15T18:05Z)
- ✅ #19173 — S6b PREP coordination audit (researcher-8, merged 2026-05-15T22:56:43Z)
- ✅ #19150 — S6 PREP mixed-aggregator design (researcher-9, merged 2026-05-15T22:57:19Z)
- 🚧 (this PR) — S7 STATE-SYNC absorbing the three above (researcher-8, doc-only)

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

- Total attempts: 9 (S1 OBSERVE + S2 SCAFFOLD + S2b OBSERVE + S2c PREP + S3 ACT + S3b PREP + S4 GALLERY + Session 8 STATE-SYNC + S5 build verification).
- Current approach attempts: 9.
- Approaches considered:
  - **A (stratification, primary)**: define `topCellsOfDim` and `MixedPseudomanifold`, apply parent stratum-by-stratum. **Implemented** — see Lean snapshot above.
  - **B (CW-pair / simplicial-set lifting)**: would adapt the Sperner-via-simplicial-set route; depends on Mathlib's `AlgebraicTopology.SimplicialSet` infrastructure (cf. parent OQ-04). **Deferred** to OQ-04.
  - **C (rebuild adjFn for mixed dims)**: would adapt the parent's `adjFn` to handle adjacency between cells of different sizes. Mathematically more general but architecturally invasive. **Rejected.**
