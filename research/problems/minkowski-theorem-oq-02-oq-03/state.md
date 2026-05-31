# Research State: minkowski-theorem-oq-02-oq-03

## Current State
**Phase**: S6α ACT shipped (Lean — `stdLatticeN_coords` via PREP-3 §3.3 paste-ready upgrade, build pending) — S5-b ACT shipped (Lean — `shearM_toLin'_apply_zero` + `shearM_toLin'_apply_succ` + `dirichletBoxN` def + `dirichletSetN_eq_shearM_preimage` merged via PR #19046, build verified 3058 jobs) — S5-c PREP (PR #19181 + paste-ready upgrade #19505) — **S5-c ACT pending** (rect-volume assembly, ~49 LOC), **S6 ACT pending** (final assembly, ~80 LOC, depends on S5-c + S6α).
**Path**: full
**Since**: 2026-05-12
**Last Updated**: 2026-05-30 (Session 11, researcher-1, **S11 S6α ACT** — `stdLatticeN_coords` paste-ready ship per PREP-3 §3.3; build pending)
**Iteration**: 11

## Lean status at HEAD
`proofs/Proofs/MinkowskiTheoremOQ02OQ03.lean` (370 LOC, 0 sorries, 0
axioms; counts post-S11 ACT — build pending for S6α deliverable; carry-forward
3058-job clean baseline from #19046 PR body, 2026-05-14, applies to PART 1-6
content unchanged by this S11 ACT):

| Lemma                                | Statement                                                  | Status                                  |
| ------------------------------------ | ---------------------------------------------------------- | --------------------------------------- |
| `dirichletSetN`                      | n-dim Cassels parallelepiped (Fin (n+1) → ℝ)               | def in place (S2)                       |
| `dirichletSetN_symmetric`            | Central symmetry about origin                              | sorry-free, 0 axioms (S2)               |
| `dirichletSetN_measurable`           | Lebesgue measurable (open set + iInter)                    | sorry-free, 0 axioms (S3)               |
| `dirichletSetN_convex`               | Convex (linear preimages of `Ioo` + `convex_iInter`)       | sorry-free, 0 axioms (S4)               |
| `shearM`                             | `(n+1) × (n+1)` shear matrix `(1, α) ⊕ (-I_n)`             | def in place (S5-a, PR #18975)          |
| `shearM_lowerTriangular`             | `BlockTriangular toDual` form (Mathlib `det_of_lowerTriangular` bearer) | sorry-free, 0 axioms (S5-a, PR #18975) |
| `shearM_det`                         | `(shearM α).det = (-1)^n` (via lowerTriangular + Fin.prod_univ_succ) | sorry-free, 0 axioms (S5-a, PR #18975) |
| `shearM_toLin'_apply_zero`           | `(shearM.toLin' v) 0 = v 0` (row-0 collapse via `Fin.sum_eq_single`) | sorry-free, 0 axioms (S5-b, PR #19046)  |
| `shearM_toLin'_apply_succ`           | `(shearM.toLin' v) i.succ = α i * v 0 − v i.succ` (row-`i.succ` decomposition) | sorry-free, 0 axioms (S5-b, PR #19046) |
| `dirichletBoxN`                      | `Set.pi` axis-aligned box `(−(Qⁿ+1), Qⁿ+1) × (−1/Q, 1/Q)ⁿ` via `Fin.cases` | def in place (S5-b, PR #19046)          |
| `dirichletSetN_eq_shearM_preimage`   | `dirichletSetN n α Q = shearM.toLin' ⁻¹' dirichletBoxN` (bridge identity) | sorry-free, 0 axioms (S5-b, PR #19046)  |
| `dirichletSetN_volume`               | Volume = `2^(n+1)(Qⁿ+1)/Qⁿ`                                | **S5-c ACT pending** (#19181 recipe)    |
| `stdLatticeN_coords`                 | Integer-coordinate extraction (general `{m : ℕ} [NeZero m]` analogue of parent `stdLattice2_coords`) | **S6α ACT shipped (this PR), build pending; 0 sorries / 0 axioms** |
| `simultaneous_dirichlet_…`           | Assembly + integer extraction                              | **S6 ACT pending** (#18511 recipe)      |

## Merged PRs (chronological)

| PR     | Phase             | Author        | Merged (UTC)         | Files touched                                                                                                                  |
| ------ | ----------------- | ------------- | -------------------- | ------------------------------------------------------------------------------------------------------------------------------ |
| #18339 | S1 OBSERVE        | researcher-1  | 2026-05-12 22:39:38  | `problem.md`, `knowledge.md`, `state.md` (seeker stub → S1 entry), research JSON, `sessions/2026-05-12-s01-observe.md`           |
| #18419 | S5 PREP           | researcher-11 | 2026-05-13 00:51:28  | `sessions/2026-05-12-s5-prep-shear-volume-generalization.md`                                                                   |
| #18511 | S6 PREP           | researcher-1  | 2026-05-13 03:11:07  | `sessions/2026-05-12-s6-prep-minkowski-assembly-roadmap.md`                                                                    |
| #18551 | S2 ACT            | researcher-1  | 2026-05-13 03:49:30  | `proofs/Proofs/MinkowskiTheoremOQ02OQ03.lean` (new, +117 LOC: def + symmetry), `sessions/2026-05-13-s2-act-…md`                |
| #18613 | S3 + S4 ACT       | researcher-3  | 2026-05-13 06:23:30  | `proofs/Proofs/MinkowskiTheoremOQ02OQ03.lean` (+72 LOC: measurable + convex), `sessions/2026-05-13-s3-s4-act-…md`              |
| #18622 | S5 PREP-2         | researcher-5  | 2026-05-13 06:50:27  | `sessions/2026-05-13-s5-prep-2-mathlib-bearer-audit.md`                                                                        |
| #18967 | STATE-SYNC        | researcher-12 | 2026-05-14 (early)   | `state.md` (Session 7), research JSON (Session 7 refresh)                                                                      |
| #18975 | S5-a ACT          | (researcher)  | 2026-05-14           | `proofs/Proofs/MinkowskiTheoremOQ02OQ03.lean` (+63 LOC: `shearM` def + `shearM_lowerTriangular` + `shearM_det = (-1)^n`)        |
| #18991 | Session 8 STATE-SYNC | researcher-5 | 2026-05-15 23:29     | `state.md`, JSON sidecar (catch-up to #18975 only)                                                                              |
| #19283 | S5-b PREP         | researcher-?  | 2026-05-15 18:01     | `sessions/2026-05-15-s5b-prep-Tv-preimage.md` (Tv0/Tv_succ/rectN/preimage-eq proof templates, doc-only)                          |
| #19192 | S6 PREP-2         | researcher-?  | 2026-05-15 22:55     | `sessions/2026-05-14-s6-prep-2-stdLatticeN-skeleton-audit.md` (`stdLatticeN_coords` v4.26.0 audit + standalone S6α ACT plan)     |
| #19181 | S5-c PREP         | researcher-?  | 2026-05-15 22:56     | `sessions/2026-05-14-s5c-prep-rect-volume-bridge.md` (`dirichletSetN_volume` rect-volume bridge recipe, ENNReal-valued B1)       |
| #19321 | S8-c PREP body    | researcher-8  | 2026-05-15 ~23:11    | `sessions/2026-05-15-s8c-prep-postdrain-audit.md` (§1–§9: bearer re-verify + #19046 mergeability + S5-c/S6α sequencing + 5 hazards) |
| #19046 | **S5-b ACT** (Lean) | (researcher) | 2026-05-15 23:27     | `proofs/Proofs/MinkowskiTheoremOQ02OQ03.lean` (+79 LOC: `shearM_toLin'_apply_zero` + `shearM_toLin'_apply_succ` + `dirichletBoxN` def + `dirichletSetN_eq_shearM_preimage`); build verified 3058 jobs |
| #19343 | S8-c PREP §10 addendum | researcher-? | 2026-05-16 01:08   | `sessions/2026-05-15-s8c-prep-postdrain-audit.md` (+§10: post-#19046/#18991 merge state realignment, doc-only)                  |
| #19495 | S10 PREP-3 (S6α paste-ready) | researcher-8 | 2026-05-16 08:53     | `sessions/2026-05-16-s10-prep-3-s6alpha-pasteready-upgrade.md` (~280 LOC, §1–§11; S6α `stdLatticeN_coords` paste-ready upgrade + 5-bearer drift recheck + Risks A+B pre-resolved inline; AMBER host-disk gate) |
| #19505 | S10 PREP-4 (S5-c paste-ready, ANALYSIS-ONLY) | researcher-9 | 2026-05-16 08:52     | `sessions/2026-05-16-s10-prep-4-s5c-pasteready-upgrade.md` (`dirichletSetN_volume` paste-ready upgrade; new pin `abs_neg_one_pow` collapses 4-step chain to 1; `LinearMap.continuous_of_finiteDimensional` drop-in replaces missing `LinearMap.continuous_on_pi`; deliberately deferred state.md/JSON edits to drain-wave STATE-SYNC) |
| (this PR) | **S11 S6α ACT** (Lean) | researcher-1 | 2026-05-30 | `proofs/Proofs/MinkowskiTheoremOQ02OQ03.lean` (+39 LOC: import `Proofs.MinkowskiFundamentalTheorem` + PART 7 `stdLatticeN_coords` lemma per PREP-3 §3.3 paste-ready upgrade, with added `[NeZero m]` constraint for general-m signature; 0 sorries, 0 axioms; build pending — follows slug "build pending" convention #18975/#19046/#18991), `state.md` (head + Merged-PRs + Lean-status + Next-ACT-candidates), JSON sidecar (iter 10 → 11, leanFiles counts 331/8 → 370/9), new `sessions/2026-05-30-s11-s6alpha-act-stdLatticeN-coords.md` |

## Session 11 — S11 S6α ACT: `stdLatticeN_coords` paste-ready ship per PREP-3 §3.3 (researcher-1, 2026-05-30)

**Mode.** Lean ACT + minimal state.md/JSON refresh. No `problem.md`,
`knowledge.md`, `approaches/*`, gallery, parent-file, sibling-slug, or
`lake-manifest.json` edits.

**What ships.** A single new lemma `stdLatticeN_coords` in
`proofs/Proofs/MinkowskiTheoremOQ02OQ03.lean` (new PART 7 section
appended after PART 6; +39 LOC including section banner + ~14-LOC
docstring + ~13-LOC proof body). The lemma generalises the parent
OQ-02's `m = 2`-specialised `stdLattice2_coords`
(`Proofs/MinkowskiTheoremOQ02.lean:147`) to general `{m : ℕ} [NeZero m]`.
Skeleton is PREP-3 §3.3 paste-ready upgrade verbatim, with one signature
adjustment: `[NeZero m]` added (required for general-`m` resolution of
`stdLattice m`'s implicit `[NeZero n]` from `MinkowskiFundamentalTheorem.lean:583`).

**Bearers.** All 5 cited bearers from PREP-3 §2 recheck (pin
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`, unchanged since 2026-05-15):
`Submodule.mem_span_range_iff_exists_fun`, `Pi.basisFun_apply`,
`Pi.single_apply`, `Int.cast_smul_eq_zsmul`, `Finset.sum_ite_eq'` (line 152
form). Risks A + B from PREP-3 §3.2 pre-resolved by explicit
`simp only` chain; Risk C resolved by `Finset.sum_congr + .symm` workaround
in Step C.

**Build status.** Build pending. Host disk 94% full / 61 Gi avail (better
than the 100% PREP-3 blocker but still inside the AMBER gate window per
PREP-3 §6). Docker daemon responsive (<10s `docker info`) but inline build
incompatible with researcher iteration cadence (30-45min Mathlib refetch
+ 10min cache fetch). Slug precedents #18975 (S5-a ACT, 2026-05-14),
#19046 (S5-b ACT, 2026-05-15), #18991 (Session 8 STATE-SYNC, 2026-05-15)
all shipped "build pending" with downstream verification by mechanic.
This PR follows the same pattern; auditor/mechanic Docker-verify of the
S6α deliverable is the documented next step.

**Coordination.** No open slug-PRs at branch time (verified via
`gh pr list --state open --limit 200 | grep -i minkowski`); file
appended after `end MinkowskiTheoremOQ02OQ03`'s last existing PART
(PART 6 S5-b ACT, lines 252-329 of pre-ship file); S5-c ACT (the other
paste-ready candidate) targets a different PART (PART 6 volume
extension), so file-disjoint append surface confirms zero conflict risk
with the next ACT claimant.

**Files touched.**
- `proofs/Proofs/MinkowskiTheoremOQ02OQ03.lean`: +1 import, +1 lemma, +PART 7 banner; 331 → 370 LOC; 8 → 9 theorems; 0 sorries / 0 axioms (carry-forward).
- `state.md`: head refresh (iter, phase, last-updated), Merged-PRs +1 row, Lean-status table flip S6α to shipped, Open-questions table flip, Next-ACT-candidates drop S6α row, Next Action rewrite, Attempt Count +2, this Session 11 block (above the prior Session 10 STATE-SYNC).
- `sessions/2026-05-30-s11-s6alpha-act-stdLatticeN-coords.md` (new): full ACT memo (§1–§8 — provenance, bearers, parent model, coordination, honest-status, files touched, next action).
- `src/data/research/problems/minkowski-theorem-oq-02-oq-03.json`: iter 10 → 11, phase + focus + nextAction refresh, leanFiles[0].{lineCount: 331 → 370, theoremCount: 8 → 9}, +1 builtItems, progressSummary append, nextSteps drop S6α, lastUpdate bump.

----

## Session 10 — S10 STATE-SYNC: absorb PREP-4 (#19505) into canonical state.md + JSON (researcher-6, 2026-05-16)

**Mode.** Doc-only. No Lean / `problem.md` / `knowledge.md` / `approaches/*` edits.

**Why STATE-SYNC.** S10 PREP-4 (#19505, researcher-9, merged 2026-05-16T08:52:58Z) shipped paste-ready upgrade of `dirichletSetN_volume` (S5-c ACT recipe) as ANALYSIS-ONLY (no `state.md` / JSON edits). #19495 (S10 PREP-3, merged ~30s later) absorbed PREP-3 itself but predated PREP-4 in authoring time, so its state.md/JSON updates do not reflect PREP-4. This STATE-SYNC is the drain wave PREP-4 explicitly named: catch the missing Merged-PRs table rows (#19495 + #19505) + iter bump (9 → 10) + focus/nextAction refresh.

**Outcome.** This STATE-SYNC PR:

1. Adds `sessions/2026-05-16-s10-statesync-prep4-absorb.md` (~200 LOC, 9 sections) with: §1 why STATE-SYNC, §2 pre-sync drift table, §3 PREP-4 deliverables summary, §4 3-bearer spot-check at pin SHA, §5 slug-wide status post-STATE-SYNC, §6 files touched + NOT touched, §7 next-claim disposition (incl PREP-fatigue heuristic), §8 honest confidence, §9 PR title + commit body.
2. Updates `state.md`: header `Last Updated` + `Iteration` (9 → 10); Merged-PRs table (+ #19495 + #19505 rows above this Session 10 STATE-SYNC block); this Session 10 STATE-SYNC block above the pre-existing Session 10 PREP-3 block.
3. Refreshes JSON sidecar: `currentState.iteration` (9 → 10), `focus` (describes PREP-3 + PREP-4 both absorbed), `nextAction` (refined paste-ready pointers), `attemptCounts.total` (17 → 18), `lastUpdate` (2026-05-16T05:28 → ~10:55Z).

**Pre-sync drift table** (verbatim from §2 of the session memo):

| Field | At HEAD (pre-sync) | Truth (post-this-PR) |
|---|---|---|
| `Last Updated` | "Session 10, researcher-8, S10 PREP-3" | "Session 10, researcher-6, S10 STATE-SYNC absorbing PREP-4 (#19505)" |
| `Iteration` | 9 | 10 |
| Merged-PRs table | last row #19343 | + #19495 + #19505 |
| JSON iter | 9 | 10 |
| JSON `attemptCounts.total` | 17 | 18 |
| JSON `lastUpdate` | 2026-05-16T05:28:00Z | 2026-05-16T~10:55:00Z |

**Bearer-pin spot-check** (this STATE-SYNC, 3-bearer recheck at pin `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`): `abs_neg_one_pow` ✓, `LinearMap.continuous_of_finiteDimensional` ✓, `Submodule.mem_span_range_iff_exists_fun` (PREP-3 bearer #1) ✓. 0 substantive drift since PREP-3/PREP-4 (~2 hours ago at same pin SHA).

**Slug-wide status post-this-STATE-SYNC**: `proofs/Proofs/MinkowskiTheoremOQ02OQ03.lean` 331 LOC / 0 sorries / 0 axioms (S5-b ACT #19046 build-verified 3058 jobs, carries forward). **S5-c + S6α both paste-ready at HEAD**; S6 final follows. Total LOC to OQ-03 graduation: ~149 across 3 ACTs. Host disk RED (100% capacity / 6.9 Gi avail at 2026-05-16T~10:55Z) gates all ACT-class Lean work.

**No Lean / problem / knowledge / gallery / sister-slug edits.** Pure doc work. Three files touched: this state.md head + Merged-PRs table + this Session 10 STATE-SYNC block, the new session memo, JSON sidecar.

**Next-claim disposition**: per §7 of the session memo, if disk recovers next claim should pick S5-c or S6α ACT (both paste-ready); otherwise PREP-fatigue heuristic suggests release-without-action (this STATE-SYNC is the 4th doc-only event in <12 hours; further doc work yields marginal value until disk gate clears).

----

## Session 10 — S10 PREP-3: S6α `stdLatticeN_coords` paste-ready upgrade + fresh bearer drift recheck under host-disk-blocked ACT window (researcher-8, 2026-05-16)

**Mode.** Doc-only. No Lean / `problem.md` / `knowledge.md` / `approaches/*` edits.

**Why PREP-3.** S6 PREP-2 (#19192) shipped a v4.26.0 bearer audit + a §5 Lean skeleton flagged as "paper design" in its §9 honesty caveats (no `lake build` performed; default `simp` chain may misfire on Risks A+B). This PREP-3 (a) re-verifies the 5 bearers cited in #19192 §3 at fresh HEAD `cf1cfa085e4` (pin `2df2f015...` unchanged since 2026-05-15T22:55Z), (b) catalogues a NEW bearer variant (`Finset.prod_ite_eq'` no-`s` form at `Piecewise.lean:297`) not noted by #19192 §3.4, (c) upgrades the §5 skeleton to paste-ready by replacing the default `simp` chain with a defensive `simp only` list (pre-resolves Risks A+B inline), and (d) captures the live host-disk blocker (100% capacity on `/System/Volumes/Data`; Docker daemon non-responsive at 30s timeout) that gates any Lean ACT this cycle.

**Outcome.** This PREP-3 PR:

1. Adds `sessions/2026-05-16-s10-prep-3-s6alpha-pasteready-upgrade.md` (~280 LOC, 11 sections) with: §1 position vs HEAD; §2 bearer drift recheck table (5 bearers, 0 substantive drift, 1 new variant); §3 paste-ready §5 upgrade (~13-LOC body w/ defensive `simp only`); §3.4 line-297 fallback; §4 live host-disk blocker capture; §5 S5-c + S6α order-of-operations table (4 race scenarios); §6 ACT-readiness gate (7/8 GREEN, 1/8 AMBER); §7 honest framing (4 caveats); §8 pre-claim cross-checks (9); §9 no-edit guarantee; §10 done-when; §11 references.
2. Bumps `Iteration` 8 → 9 and `Last Updated` to Session 10.
3. Updates JSON sidecar `currentState.iteration` (8 → 9), `currentState.focus`, `currentState.nextAction` (note the AMBER host-disk gate), `attemptCounts.{total, currentApproach}` (16 → 17), `knowledge.builtItems` (+1 session file), `lastUpdate`/`updatedAt` (2026-05-16 stamps).

**Bearer drift recheck.** 5/5 from S6 PREP-2 §3 unchanged at original lines: `Submodule.mem_span_range_iff_exists_fun` (372), `Pi.basisFun_apply` (131), `Int.cast_smul_eq_zsmul` (151), `Finset.prod_ite_eq'` (with-`s` at 152, off-by-one cosmetic vs #19192 cite of 151–153), plus the newly-catalogued no-`s` form at line 297. Pin `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0) confirmed via `gh api git/trees/...` echoing the SHA and via `proofs/lake-manifest.json:8`.

**Live ACT blocker.** Host `df -h /System/Volumes/Data` returns `883Gi used / 7.1Gi avail / 100% capacity` at 2026-05-16T05:24:10Z; `docker info` hangs past 30s timeout (containerd `meta.db` corruption signature per `_researcher_act_pivot_to_prep_when_host_docker_corrupt`). S6α ACT (~22-23 LOC paste-ready per §3.3) cannot be Docker-verified this cycle. Subsequent claimants must check `df -h /System/Volumes/Data` BEFORE branching for ACT — if still ≥99%, defer ACT and ship STATE-SYNC or another PREP-level doc instead.

**No Lean / problem / knowledge changes.** Pure doc work. Three files touched: this `state.md` row, `sessions/2026-05-16-s10-prep-3-s6alpha-pasteready-upgrade.md` (new), JSON sidecar.

**Build status.** No `.lean` changes; no Docker build attempted (blocked by host disk pressure — see §4 of session memo). #19046's 3058-jobs-clean status carries forward as the post-S5-b build-verification anchor on `main`; the S6α ACT remains the next Lean increment when the host-disk blocker clears.

**Pre-claim cross-checks** (per researcher anti-patterns memory): worktree synced to `origin/main` `cf1cfa085e4` before reading state; fresh topic branch off `origin/main`; bearer recheck via `curl` of raw.githubusercontent.com (faster than full `gh api` round-trip, equivalent content); 0 open slug-PRs at claim time (`gh api search/issues?q=...minkowski-theorem-oq-02-oq-03+is:pr`); host disk + Docker daemon health captured at 05:24Z; absolute worktree paths used for all edits (per `_edit_tool_targets_main_repo_not_worktree_when_using_absolute_path_without_worktree_prefix`).

----

## Session 9 — STATE-SYNC: Option-B catchup absorbing #19283/#19192/#19181/#19321/#19046/#19343 (researcher-1, 2026-05-16)

**Mode.** Doc-only. No Lean / `problem.md` / `knowledge.md` /
`approaches/*` edits.

**Why STATE-SYNC.** Six PRs merged on this slug after Session 8
STATE-SYNC (#18991, merged 2026-05-15T23:29:31Z), which catches only
#18975 (S5-a ACT, 2026-05-14):

| # | PR | Phase | Merged (UTC) | Recorded in S8? |
|---|---|---|---|---|
| 1 | #19283 | S5-b PREP | 2026-05-15T18:01:41Z | No |
| 2 | #19192 | S6 PREP-2 | 2026-05-15T22:55:55Z | No |
| 3 | #19181 | S5-c PREP | 2026-05-15T22:56:26Z | No |
| 4 | #19321 | S8-c PREP body | 2026-05-15T~23:11Z | No |
| 5 | #19046 | **S5-b ACT** (Lean, +79 LOC) | 2026-05-15T23:27:39Z | No |
| 6 | #19343 | S8-c PREP §10 addendum | 2026-05-16T01:08:50Z | No |

S8-c PREP §6.1 explicitly designates this as the **Option-B**
STATE-SYNC: capture rows 2–5 of S8-c §6 (all 4 unrecorded PRs at
S8-c-PREP-authoring time) plus the post-merge S5-b ACT row + the §10
addendum, in a single coherent catchup. The S8-c §10 addendum
explicitly names this Option-B STATE-SYNC as action item **#1** in
the forward-action list.

**Outcome.** This STATE-SYNC PR:

1. Rewrites the `Current State` header to reflect post-#19046 + post-#19343 status
   (Phase: "S5-b ACT shipped"; Last Updated: 2026-05-16; Iteration: 7 → 8).
2. Expands the `Lean status at HEAD` table from 9 to 14 rows: adds 4
   shipped declarations from #19046 (`shearM_toLin'_apply_zero` +
   `shearM_toLin'_apply_succ` + `dirichletBoxN` def +
   `dirichletSetN_eq_shearM_preimage`) and renames the pending
   `dirichletSetN_volume` row to "S5-c ACT pending (#19181 recipe)";
   adds a separate `stdLatticeN_coords` row for the S6α ACT
   (parallelizable with S5-c).
3. Adds 6 rows to the `Merged PRs` table (#18991, #19283, #19192,
   #19181, #19321, #19046, #19343).
4. Bumps `Attempt Count`: `Total attempts: 16 (15 merged PRs + this STATE-SYNC)`
   per §6 of the accompanying sessions/ file.
5. Refreshes `Next-ACT candidates` table: S5-a + S5-b both shipped;
   remaining are S5-c (~49 LOC, #19181 recipe, ENNReal-valued B1),
   S6α (~22 LOC, #19192 recipe, parallelizable with S5-c), S6 final
   (~80 LOC, #18511 recipe, sequenced after both).
6. Refreshes `Next Action`: pick either S5-c ACT or S6α ACT (both
   parallelizable per S8-c §5). Total remaining LOC to OQ-03
   graduation: ~150 across 3 ACTs.
7. Updates the JSON sidecar's `currentState.iteration` (7 → 8),
   `currentState.phase`, `currentState.focus`, `currentState.nextAction`,
   `currentState.attemptCounts.{total, currentApproach}` (7 → 16),
   `knowledge.progressSummary`, `knowledge.builtItems` (+4 new sessions/
   files + this Session 9), `knowledge.insights` (+1 S5-b ACT lessons),
   `leanFiles[0].lineCount` (252 → 331), `leanFiles[0].theoremCount`
   (4 → 8), `leanFiles[0].defCount` (2 → 3), top-level `lastUpdate`
   (`2026-05-14T03:50:00Z` → `2026-05-16T01:35:00Z`), and `updatedAt`
   (`2026-05-13` → `2026-05-16`).

**Bearer drift re-verify.** All 6 bearers from S8-c §1 re-confirmed
at Mathlib pin `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`. Two
additional bearers used by #19046's S5-b ACT proofs
(`Matrix.toLin'_apply`, `Finset.sum_eq_single`) recorded in the
accompanying sessions/ file §4 for completeness. Zero substantive
drift across the Session 8 → Session 9 window (~24 h).

**No Lean / problem / knowledge changes.** Pure doc sync, strictly
orthogonal to all merged ACT recipes. The 3 files touched are:
`sessions/2026-05-16-s9-statesync.md` (new), `state.md` (this edit),
`src/data/research/problems/minkowski-theorem-oq-02-oq-03.json`
(currentState + leanFiles + knowledge + lastUpdate + updatedAt
fields).

**Build status.** No `.lean` changes; no Docker build attempted or
needed. #19046's "build verified 3058 jobs" status (per its PR body,
2026-05-14) carries forward as the live build-verification anchor for
the post-S5-b chain on `main`.

**Pre-claim cross-checks** (per researcher anti-patterns memory):
worktree synced to `origin/main` `8a3cda556b6` before reading state
(avoided stale-iter trap); fresh topic branch off `origin/main`
(avoided open-PR contamination — the pre-existing
`research/shapley-folkman-oq-01-s10-statesync` branch was NOT
re-used); `--repo rjwalters/lean-genius` + `--limit 500` flags
explicit on all `gh` invocations; worktree absolute paths used for
all edits (per `_main_repo_linter_reverts_edits_use_worktree_absolute_path`).

----

## Session 8 — STATE-SYNC after #18975 S5-a ACT (researcher-5, 2026-05-14)

**Mode.** Doc-only. No Lean edits.

**Why STATE-SYNC.** PR #18975 ("S5-a ACT — shearM def + lowerTriangular
+ det = (-1)^n") merged on 2026-05-14 after Session 7's STATE-SYNC
(PR #18967, also 2026-05-14, doc-only). The S5-a ACT advanced
`MinkowskiTheoremOQ02OQ03.lean` from 189 → 252 LOC, adding three
sorry-free / axiom-free declarations (`shearM` def, `shearM_lowerTriangular`,
`shearM_det = (-1)^n`). state.md's "Current State" / "Lean status at
HEAD" / "Merged PRs" / "Next-ACT candidates" sections and the research
JSON `currentState.focus` / `nextAction` / `knowledge.progressSummary`
fields still describe the pre-S5-a state. Live Lean source counts
diverge from JSON `currentState.focus` (189 LOC claim) by +63 LOC.

**Drift surface.**

* `currentState.phase` (`"ACT"`): unchanged — still appropriate.
* `currentState.iteration` (6): bumped to 7 to reflect Session 8.
* `currentState.focus`: rewritten to record #18975's three new
  declarations and the surviving S5-b/S5-c/S6 backlog.
* `currentState.nextAction`: narrowed from "S5 ACT (volume calculation),
  narrowest entry point S5-a" to "S5-b (Tv0/Tv_succ + h_eq preimage)"
  since S5-a is now landed.
* `knowledge.progressSummary`: refreshed to add #18975 ahead of the
  existing chronology.
* `leanFiles`: the file's JSON entry for `MinkowskiTheoremOQ02OQ03.lean`
  was previously *missing entirely* — the JSON `leanFiles` array
  contained only OQ02 + OQ02OQ01 entries despite OQ02OQ03 having
  shipped since #18551. Session 8 adds the missing entry with
  `lineCount: 252 / theoremCount: 4 / defCount: 2 / axiomCount: 0 /
  sorryCount: 0` (the count splits `def shearM` + `def dirichletSetN`
  into the `defCount` bucket and counts `shearM_*` + `dirichletSetN_*_*`
  in `theoremCount`).

**Counts on file at #18975 merge:**

* `proofs/Proofs/MinkowskiTheoremOQ02OQ03.lean`: 252 LOC, 4 theorems +
  2 `def`s, 0 sorries, 0 axioms.
* No change to gallery `meta.json` (`src/data/proofs/minkowski-theorem-oq-02-oq-03/meta.json`
  was last touched independently and its leanFiles count is auditor-
  invisible).

### Next-ACT candidates (refresh)

`S5-a` row in the candidates table is now landed (PR #18975). Remaining
entries unchanged from Session 7:

* **S5-b ACT** (Tv0 / Tv_succ + `h_eq` preimage, ~50 LOC, recommended
  entry point) — substantively bears on the chain
  `dirichletSetN_volume → shearM⁻¹ image factorisation → preimage
  measurability + volume identity`.
* **S5-c ACT** (volume assembly, ~80 LOC) — depends on S5-b.
* **S6 ACT** (`simultaneous_dirichlet_from_minkowski`, ~80-120 LOC)
  — depends on S5-c plus the integer-coordinate extraction sub-ACT
  (S6 PREP, PR #18511).

### Honest-status block

* **Mathematical progress in this PR**: zero — STATE-SYNC catches the
  books up to #18975 without adding theorems, definitions, sorries,
  or axioms.
* **Build status**: unchanged. #18975 shipped "(build pending)" per
  the active build-pending convention; the post-S5-a chain (`shearM`
  + `shearM_lowerTriangular` + `shearM_det`) remains gated on Docker
  CI green for the `proofs/.lake` infra repair (orthogonal mechanic
  infra task).
* **Pre-claim cross-checks** (per researcher anti-patterns memory):
  worktree synced to `origin/main` BEFORE reading state (avoided
  stale-iter trap); fresh topic branch off `origin/main` (avoided
  open-PR contamination); 2nd STATE-SYNC this session (within the
  2-per-session cap — first was S23 PREP for `minkowski-theorem-oq-04`,
  which is *not* STATE-SYNC since it shipped a new spec doc).

----

## Session 7 — STATE-SYNC: align state.md + JSON with 5-PR backlog (researcher-12, 2026-05-13)

**Mode.** Doc-only (no `.lean` changes, no `problem.md` / `knowledge.md`
changes).

**Trigger.** `state.md` was last updated at the end of Session 1 (S1
OBSERVE, PR #18339), declaring `Phase: OBSERVE` and `Next Action: S2-A`.
Five subsequent PRs have since merged on `main` (S5 PREP #18419, S6 PREP
#18511, S2 ACT #18551, S3 + S4 ACT #18613, S5 PREP-2 #18622) without a
`state.md` refresh in any of them; the JSON sidecar
`src/data/research/problems/minkowski-theorem-oq-02-oq-03.json` was
similarly frozen at S1. Future claimants reading `state.md` would
believe `MinkowskiTheoremOQ02OQ03.lean` does not yet exist.

**Outcome.** This STATE-SYNC PR:

1. Promotes the **Phase** header to reflect the actual highest Lean
   ACT (`S4`) and the latest doc-only PREP (`S5 PREP-2`).
2. Bumps **Iteration** from 1 to 6 (one per merged PR after S1).
3. Adds a **Lean status table** documenting all 6 lemmas (4 shipped,
   2 pending).
4. Adds a **Merged PRs table** with PR #, phase, author, UTC timestamp,
   and the actual files-touched diff each shipped.
5. Adds **Session-log entries** below for sessions 2-6 (one paragraph
   each, citing the canonical session-file in `sessions/`).
6. Adds **Open questions — PREP coverage** cross-reference linking
   each S1 OBSERVE shortlist item to its PREP/ACT memo.
7. Adds **Next-ACT candidates** table with LOC estimate, risk, and
   pre-staging status for S5 ACT (volume) and S6 ACT (assembly).
8. Updates the JSON sidecar's `currentState.phase`, `iteration`,
   `focus`, `nextAction`, `knowledge.progressSummary`,
   `knowledge.builtItems`, and `updatedAt`.

**No Lean / problem / knowledge changes.** Pure doc sync.

**Build status.** No `.lean` changes; no Docker build attempted or
needed.

## Session 6 — S5 PREP-2: Mathlib bearer audit + CRITICAL erratum (researcher-5, 2026-05-13, PR #18622)

Doc-only memo in `sessions/2026-05-13-s5-prep-2-mathlib-bearer-audit.md`.
Closes 4 honest gaps flagged in S5 PREP (§9 of the predecessor) by
verifying Mathlib bearers at the locked pin
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0):

- **CRITICAL ERRATUM** in S5 PREP §3.1: `shearM_lowerTriangular` was
  stated as `BlockTriangular id` (upper-triangular condition). The
  corrected signature is `BlockTriangular (toDual : Fin (n+1) →
  (Fin (n+1))ᵒᵈ)`, matching `Mathlib/LinearAlgebra/Matrix/Block.lean`
  `det_of_lowerTriangular` at line 291. The bug would have surfaced
  as a unification failure at S5 ACT.
- `Fin.prod_univ_succ` verified at `Mathlib/Algebra/BigOperators/Fin.lean:76`.
- `Finset.prod_const_neg_one_eq_pow` confirmed **absent**; two-line
  `prod_const + card_univ + Fintype.card_fin` chain is canonical.
- `Finset.sum_ite_eq'` verified at `…/Piecewise.lean:152`, with explicit
  `Tv_succ` proof template (~15 LOC, two variants offered).
- `Real.map_matrix_volume_pi_eq_smul_volume_pi` namespace surfaced;
  `open Real` required (parent OQ-01 has it at line 32).
- `[DecidableEq ι]` requirement surfaced: `inferInstance` for `Fin (n+1)`.
- Risk register: 10/10 resolved (vs. 4 in S5 PREP).
- Revised S5 ACT LOC estimate: ~160 (down from 180).

## Session 5 — S3 + S4 ACT: measurable + convex (researcher-3, 2026-05-13, PR #18613)

Lean ACT in `proofs/Proofs/MinkowskiTheoremOQ02OQ03.lean` (+72 LOC, 0
sorries, 0 axioms). Doc in
`sessions/2026-05-13-s3-s4-act-measurable-convex.md`.

- **`dirichletSetN_measurable`** (~16 LOC): rewrites
  `dirichletSetN n α Q` as the intersection of a coordinate preimage of
  `Ioo` (for the `|v 0|` clause) with `⋂ i : Fin n` over preimages of
  `Ioo` under continuous functionals (for the `|α i * v 0 - v i.succ|`
  clauses), then closes via `(isOpen_Ioo.preimage …).inter
  (isOpen_iInter_of_finite …)`.
- **`dirichletSetN_convex`** (~14 LOC): same intersection structure,
  swapping topology for `LinearMap.proj` algebra and
  `convex_Ioo.linear_preimage` / `convex_iInter`.

Both are verbatim n-dim generalisations of the parent OQ-01's
analogues. Lean file at 189 LOC after merge.

## Session 4 — S2 ACT: dirichletSetN def + symmetry (researcher-1, 2026-05-13, PR #18551)

Lean ACT in `proofs/Proofs/MinkowskiTheoremOQ02OQ03.lean` (new file,
+117 LOC, 0 sorries, 0 axioms). Doc in
`sessions/2026-05-13-s2-act-dirichletSetN-def-symmetric.md`.

- **`dirichletSetN n α Q`** (def): the Cassels-parallelepiped
  `{v : Fin (n+1) → ℝ | |v 0| < Qⁿ + 1 ∧ ∀ i, |α i * v 0 - v i.succ| <
  1/Q}`, indexed by `Fin (n+1)` with `v 0` reserved as the
  common-denominator coordinate.
- **`dirichletSetN_symmetric`** (~9 LOC of proof): `v ∈ S → -v ∈ S`,
  one of the 3 Minkowski hypotheses. Generalises parent OQ-01's
  `dirichletSet_symmetric` by replacing the single `i = 1` clause
  with `∀ i : Fin n`.

## Session 3 — S6 PREP: Minkowski assembly + integer-coordinate extraction roadmap (researcher-1, 2026-05-12, PR #18511)

Doc-only memo in `sessions/2026-05-12-s6-prep-minkowski-assembly-roadmap.md`.
Decomposes the assembly step into 5 stages (mirroring parent OQ's
`dirichlet_approximation_from_minkowski` at `MinkowskiTheoremOQ02.lean:182`):

1. Apply `MinkowskiProved.minkowski_integer_lattice_proved (n+1)` to
   `dirichletSetN n α Q`, supplying the four hypotheses (symmetry,
   measurability, convexity, volume threshold).
2. Extract integer coordinates `(q, p) ∈ Fin (n+1) → ℤ` from the
   lattice-point existential via the (n+1)-dim analogue of parent's
   `stdLattice2_coords`.
3. Parse the parallelepiped membership: `q := |v 0|`, `p i := v i.succ`
   (modulo sign on `v 0`).
4. Show `q ≠ 0` from non-triviality of the lattice point.
5. Discharge the conclusion bounds `1 ≤ q ≤ Qⁿ` and `|α i · q - p i| <
   1/Q`.

Identifies parent's `stdLattice2_coords` as the (n+1)-dim analogue
target (currently only stated for `n = 1`); flags it as the one piece
of new infrastructure beyond S2-S5.

## Session 2 — S5 PREP: shear-map volume calculation (researcher-11, 2026-05-12, PR #18419)

Doc-only memo in `sessions/2026-05-12-s5-prep-shear-volume-generalization.md`.
Decomposes the n-dim volume calculation into 4 mechanical pieces
(mirroring parent OQ-01's `dirichletSet_volume`):

- **shearM definition**: `Matrix (Fin (n+1)) (Fin (n+1)) ℝ` with
  column 0 = `Fin.cases (1 : ℝ) α` (first column carries α₀…α_{n-1});
  off-column-0 diagonal = -1.
- **shearM_det = (-1)ⁿ**: via `det_of_lowerTriangular` + diagonal
  product collapse.
- **T_image_is_rectangle**: image of `dirichletSetN` under `M.toLin'`
  is the open box `(-(Qⁿ+1), Qⁿ+1) × (-1/Q, 1/Q)ⁿ`.
- **dirichletSetN_volume**: chain
  `volume S = ENNReal.ofReal (|det M|⁻¹) · volume rect = volume rect =
  2(Qⁿ+1) · (2/Q)ⁿ`.

S5 PREP-2 (Session 6 above) closes the 4 honest gaps flagged here.

## Session 1 — S1 OBSERVE: literature audit + Mathlib API survey + S2 shortlist (researcher-1, 2026-05-12, PR #18339)

Doc-only deliverable in `sessions/2026-05-12-s01-observe.md`. Filled
the seeker-init `problem.md` / `knowledge.md` / `state.md` skeletons.
Surveyed Mathlib for the n-dim geometry-of-numbers infrastructure used
by parent `MinkowskiTheoremOQ02.lean` and axiom-free sibling
`MinkowskiTheoremOQ02OQ01.lean`. Found:

- **`MinkowskiProved.minkowski_integer_lattice_proved`** at
  `MinkowskiFundamentalTheorem.lean:638` already stated for arbitrary
  `n` (hypothesis `(2 : ENNReal) ^ n < volume s`); the n-dim Minkowski
  step is free.
- **`map_matrix_volume_pi_eq_smul_volume_pi`** (used in
  `MinkowskiTheoremOQ02OQ01.lean:103`) stated for any `Fin n`; the
  shear-map step generalises.
- The three measure-theoretic axioms in parent OQ have axiom-free
  analogs in OQ-01 whose proof patterns lift to arbitrary `n`.

Recommended construction (Cassels 1957, Theorem I.II.A): the
parallelepiped `dirichletSetN α Q` defined above + lower-triangular
shear with `|det T| = 1` mapping to `(-(Qⁿ+1), Qⁿ+1) × (-1/Q, 1/Q)ⁿ`,
volume `2(Qⁿ+1) · (2/Q)ⁿ = 2^(n+1)(Qⁿ+1)/Qⁿ > 2^(n+1)`. Three S2 ACT
targets shortlisted (narrowest first): symmetric (~10 LOC), measurable
(~30 LOC), convex (~30 LOC). All three have since shipped (S2 ACT,
S3 + S4 ACT).

## Active Approach
**Approach A (Cassels 1957 parallelepiped)** — verbatim n-dim
generalisation of `MinkowskiTheoremOQ02OQ01.lean`'s 1D axiom-free
proof, using `Fin (n+1)`-indexed parallelepiped and lower-triangular
shear matrix.

Three of the four Minkowski hypotheses (symmetry, measurability,
convexity) are sorry-free, axiom-free, and merged. The remaining
volume hypothesis is the hardest step but fully pre-staged in S5 PREP
+ S5 PREP-2; assembly into `simultaneous_dirichlet_from_minkowski` is
pre-staged in S6 PREP.

## Attempt Count
- Total attempts: 19 (15 merged PRs + Session 9 STATE-SYNC + Session 10 PREP-3 + Session 10 STATE-SYNC + this Session 11 S6α ACT)
- Current approach attempts: 19 (all Approach A)
- Approaches tried: 1

## Blockers
None identified. All Mathlib bearers for S5 ACT verified by S5 PREP-2;
the `(n+1)`-dim analogue of parent's `stdLattice2_coords` (needed for
S6 ACT) is the one piece of new infrastructure required and is
roadmapped in S6 PREP.

## Open questions — PREP coverage cross-reference

| S1 OBSERVE shortlist item        | PREP coverage         | ACT status        |
| -------------------------------- | --------------------- | ----------------- |
| `dirichletSetN` def              | (S1 sketch)           | Shipped (PR #18551, S2 ACT)  |
| `dirichletSetN_symmetric`        | (S1 sketch)           | Shipped (PR #18551, S2 ACT)  |
| `dirichletSetN_measurable`       | (S1 sketch, OQ-01 ref) | Shipped (PR #18613, S3 ACT) |
| `dirichletSetN_convex`           | (S1 sketch, OQ-01 ref) | Shipped (PR #18613, S4 ACT) |
| `shearM` matrix infrastructure   | PR #18419 (S5 PREP) + PR #18622 (S5 PREP-2 bearer audit) | Shipped S5-a (PR #18975) + S5-b (PR #19046) — `shearM` + `shearM_lowerTriangular` + `shearM_det = (-1)^n` + `shearM_toLin'_apply_{zero, succ}` + `dirichletBoxN` def + `dirichletSetN_eq_shearM_preimage` |
| `dirichletSetN_volume`           | PR #19181 (S5-c PREP, rect-volume bridge recipe) + PR #19283 (S5-b PREP) | **Pending S5-c ACT** (~49 LOC) |
| `simultaneous_dirichlet_from_minkowski` | PR #18511 (S6 PREP assembly roadmap) | **Pending S6 ACT** (~80 LOC) |
| `stdLatticeN_coords (n+1) → ℤ` extraction | PR #19192 (S6 PREP-2 standalone S6α plan) + PR #19495 (S10 PREP-3 paste-ready upgrade) + PR #18511 §4 | **Shipped S11 ACT (this PR), build pending** (+39 LOC w/ docstring per `proofs/Proofs/MinkowskiTheoremOQ02OQ03.lean` PART 7) |

## Next-ACT candidates (in dependency order, parallelizable lanes annotated)

| Candidate                              | LOC est. | Risk   | Pre-staging                | Notes                                                                                                                          |
| -------------------------------------- | -------- | ------ | -------------------------- | ------------------------------------------------------------------------------------------------------------------------------ |
| **S5-c ACT** `dirichletSetN_volume`    | ~49 (15 + 15 + 19 split per #19181 §3) | medium | #19181 §3 recipe (3 declarations: A `dirichletBoxN_measurable`, B `dirichletBoxN_volume` ENNReal-valued B1, C `dirichletSetN_volume` via `Real.map_matrix_volume_pi_eq_smul_volume_pi` pushforward); bearers verified at S8-c §1 + Session 9 §4 | All upstream dependencies on `main`: `dirichletBoxN`, `shearM_det = (-1)^n`, `dirichletSetN_eq_shearM_preimage`. Step C `abs ((-1)^n)⁻¹ = 1` plumbing: C-i `simp [shearM_det, abs_neg_one_pow, abs_one, inv_one]` (S8-c §4.4 preferred path); C-ii parity case-split fallback (~3 lines). |
| **S6 ACT** `simultaneous_dirichlet_from_minkowski` | ~80   | medium | PR #18511 (S6 PREP) 5-stage pattern mirroring `MinkowskiTheoremOQ02.lean:182` | Depends on **both** S5-c (volume hypothesis) and S6α (this PR, shipped). Sequenced after S5-c lands. |

**Post-S11 ACT (this PR)**: the narrowest entry point is now **S5-c ACT**
(~49 LOC, paste-ready per #19181/#19505), which replaces the last
"pending" Minkowski hypothesis on `dirichletSetN`. After S5-c lands, the
final **S6 ACT** assembly (~80 LOC) wires S5-c + S6α (this PR) into
`simultaneous_dirichlet_from_minkowski`. Estimated remaining `.lean`
LOC to OQ-03 graduation: **~129 LOC across 2 ACTs**.

## Next Action

**Post-S11 ACT (this PR, S6α shipped build-pending)**: the next ACT pick
is **S5-c ACT** (~49 LOC, `dirichletSetN_volume` via rect-volume bridge —
#19181 §3 + S10 PREP-4 #19505 paste-ready upgrade). After S5-c lands,
**S6 ACT** (final assembly, ~80 LOC, #18511 5-stage pattern) wires
S5-c (volume hypothesis) + S6α (this PR, integer extraction) into
`simultaneous_dirichlet_from_minkowski`. Total remaining LOC to OQ-03
graduation: ~129 LOC across 2 ACTs.

**⚠️ Host-disk pre-flight gate** (per S10 PREP-3 §4): the researcher
host hit 100% capacity on `/System/Volumes/Data` (7.1Gi avail) at
2026-05-16T05:24:10Z with `docker info` hanging past 30s timeout. ANY
ACT picker on this slug MUST check `df -h /System/Volumes/Data` BEFORE
branching — if still ≥99%, defer ACT and ship another PREP-level doc
or STATE-SYNC instead. The S6α paste-ready §3.3 skeleton is otherwise
verified-ready (7/8 GREEN gate, 1/8 AMBER on this external blocker).

All ENNReal / abs-determinant plumbing hazards documented in S8-c §7
(5 entries) carry forward unchanged; live hazards for each ACT are
catalogued in Session 9 §9 + Session 10 §3.2/§3.4 of the new sessions/
files.
