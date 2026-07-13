# S6 STATE-SYNC — residual drift cleanup deferred by S5

**Date**: 2026-05-16
**Researcher**: researcher-1
**Phase**: STATE-SYNC (doc-only; strict refinement of S5 STATE-SYNC #18893)
**PR scope**: 3 files — `state.md`, `src/data/research/problems/sqrt2-plus-sqrt3-irrational-oq-01.json`, this session note. **Zero** Lean / gallery / problem.md / knowledge.md touches.

## 1. Why S6 fires (strict refinement, not new work)

S5 STATE-SYNC #18893 (researcher-?, merged 2026-05-13T17:49:43Z) correctly flipped this slug from `phase: ACT, status: active` to `phase: COMPLETED, status: completed` and added the "Completion summary" prepend to `state.md` listing the 5 deliverable PRs (#18222 S1, #18353 S2 PREP, #18369 S2 ACT, #18538 S3 GALLERY, #18402 S4 PREP).

S5 did not, however, sweep four residual drift items that survived the catchup. They are not in the PR diff (`gh pr diff 18893 -R rjwalters/lean-genius`):

| # | Field | S5 left as | Reality on disk (2026-05-16) | Severity |
|---|---|---|---|---|
| 1 | JSON `leanFiles` | `[]` | `proofs/Proofs/Sqrt2PlusSqrt3PlusSqrt5IrrationalOQ01.lean` (144 LOC, 5 theorems, 0 sorries, 0 axioms, build verified at Mathlib SHA `2df2f0150c…`) | MEDIUM (data-integrity for downstream tooling that scans `leanFiles[]`) |
| 2 | JSON `progressSummary` prose | "(145 lines, 0 sorries, 0 axioms)" | 144 LOC (`wc -l` confirms) | LOW (prose drift; `currentState.focus` already says 144) |
| 3 | JSON `builtItems[4]` and `nextSteps[0]` prose | "(new, 145 lines)" and "lineCount=145" | 144 LOC | LOW (same as #2, propagated) |
| 4 | JSON `nextAction` + `state.md` "seeded successor" wording | "seeded by S4 PREP #18402" | PR #18402 shipped **only** the design memo `sessions/2026-05-12-s4-prep-besicovitch-1940-sibling-design.md`; `ls src/data/research/problems/ \| grep sqrt2-plus-sqrt3-irrational-oq-02` is empty | MEDIUM (overstates what shipped — a future reader could believe the sibling slug exists and try to claim it) |

Items #2 + #3 collectively are the off-by-one carried over from the S2 ACT memo where the prose said `145 lines` but the actual file ended up at 144 LOC after one whitespace trim. The `currentState.focus` and gallery `meta.json` both say 144, so this is purely prose drift in the older summary/items/next-steps fields.

Item #4 is the most material: S4 PREP itself (PR #18402) explicitly framed its scope as "**does not create the sibling slug — that is a seeker job**" (see line 8-9 of the S4 PREP memo). The "seeded" wording in S5's state.md prepend and JSON `nextAction` therefore overstates the deliverable.

## 2. Fix items (S6 deliverables)

### 2.1 `state.md` (5 edits)

- L3 header: `"S4 PREP sibling-slug seeded"` → `"S4 PREP sibling-slug design-memo only"`.
- L4 header: `"Iteration: 4"` → `"Iteration: 5"`; session list extended with S5 STATE-SYNC + S6 STATE-SYNC.
- L5 header: `"Last session: S4 PREP (2026-05-13) ..."` → `"Last session: S6 STATE-SYNC (2026-05-16) — residual drift ..."`.
- L9 section header: `"## Completion summary (STATE-SYNC, 2026-05-13)"` → `"## Completion summary (STATE-SYNC, 2026-05-13; refined 2026-05-16)"`.
- L21 table row: `"(seeds sqrt2-plus-sqrt3-irrational-oq-02)"` → `"(design memo only; slug not yet created in pool)"`. Two new table rows added for S5 STATE-SYNC and S6 STATE-SYNC.
- L30-32 post-table prose: `"the seeded successor is..."` → `"the planned successor is...slug has not been created in the research pool as of 2026-05-16 — this is a job for the seeker, not this slug"`.
- "Session log" appended with S5 + S6 entries.
- "Open questions / blockers" replaced "None. S2 implementation is mechanical..." (stale, pre-S2-ACT phrasing) with "None remain. Slug is COMPLETED. Besicovitch (1940) general-k formalisation lives under the planned (not-yet-created) sqrt2-plus-sqrt3-irrational-oq-02 sibling slug — a seeker job."

### 2.2 JSON (8 edits via `jq`)

| Field | Before | After |
|---|---|---|
| `currentState.iteration` | `4` | `5` |
| `currentState.attemptCounts.total` | `4` | `5` |
| `currentState.focus` | "...S4 PREP (#18402, Besicovitch sibling-slug design memo). Lean file ... 144 lines ..." | "...S4 PREP (#18402, Besicovitch sibling-slug design memo only — slug not yet created). S5 STATE-SYNC (#18893, phase ACT→COMPLETED doc-only). S6 STATE-SYNC (this PR, residual drift: leanFiles populated, 145→144 LOC fixes, oq-02 \"seeded\" wording corrected). Lean file ... 144 lines ..." |
| `currentState.nextAction` | "None for this slug. Besicovitch ... is now tracked under successor slug ... (seeded by S4 PREP #18402)." | "None for this slug. Besicovitch ... is design-scoped by S4 PREP #18402 under the planned (not-yet-created) successor slug ... — that is a seeker job, not this slug." |
| `knowledge.progressSummary` | "(145 lines, 0 sorries, 0 axioms)" | "(144 lines, 0 sorries, 0 axioms)" |
| `knowledge.builtItems[4]` | "(new, 145 lines)" | "(new, 144 lines)" |
| `knowledge.nextSteps[0]` | "lineCount=145" | "lineCount=144" |
| `leanFiles` | `[]` | `[{ path: "proofs/Proofs/Sqrt2PlusSqrt3PlusSqrt5IrrationalOQ01.lean", lineCount: 144, sorries: 0, axioms: 0, theorems: 5, definitions: 0, buildVerified: true, mathlibSha: "2df2f0150c275ad53cb3c90f7c98ec15a56a1a67" }]` |
| `lastUpdate` | `"2026-05-13T17:35:00.000Z"` | this PR's UTC timestamp |

Applied via `jq` to one temp file then `mv` (per the `_mechanic_pnpm_build_regenerates_all_research_jsons` memory: skip `pnpm build` for single-slug edits; `wc -l` is the authoritative LOC source matching the gallery `meta.json`).

### 2.3 New session note

This file — the drift inventory + fix log.

## 3. Explicit non-actions

Per the "Don't refactor beyond what the task requires" rule and the project's `Axiom Integrity Policy`, the following are **not** touched in this PR:

1. `proofs/Proofs/Sqrt2PlusSqrt3PlusSqrt5IrrationalOQ01.lean` — 144 LOC, 5 theorems, 0 sorries, 0 axioms. Build-verified at Mathlib SHA `2df2f0150c…` (the pinned revision, unchanged since S2 ACT). No reason to touch.
2. `proofs/Proofs.lean` — already imports `Sqrt2PlusSqrt3PlusSqrt5IrrationalOQ01`. No reason to touch.
3. `src/data/proofs/sqrt2-plus-sqrt3-plus-sqrt5-irrational/{meta,annotations,index}.{json,ts}` — gallery `meta.json` already correctly records `lineCount: 144`, `theoremCount: 5`, `axiomCount: 0`, `status: verified`, `badge: original`. No reason to touch.
4. `research/problems/sqrt2-plus-sqrt3-irrational-oq-01/problem.md` and `knowledge.md` — these are S1 OBSERVE-phase scoping documents. They contain accurate domain content (proof strategy, parent-identity reuse, Mathlib API table, floating-point sanity check); none of it is wrong. The historical "S2 implementation will be mechanical" framing is appropriate to those files as historical record.
5. `src/data/research/problems/sqrt2-plus-sqrt3-irrational-oq-02.json` — explicitly **not** created. S4 PREP memo itself reserved this for the seeker. Creating it here would be claiming new work, which is out of scope for STATE-SYNC.
6. Re-spot-check of bearers (parent `sqrt2_plus_sqrt3_sq`, `Real.irrational_sqrt_natCast_iff`, `Real.sq_sqrt`, `Real.sqrt_mul`, `Real.sqrt_pos`, `Real.sqrt_nonneg`) — the S2 ACT build at Mathlib SHA `2df2f0150c…` (3060 jobs clean) is the bearer verification; pin unchanged ⇒ no re-check needed (per the SHA-stable-busywork memory note).
7. Audit tracker PR #18567 — not added to `state.md` Completion-summary table. Audit-clean PRs are not session deliverables.
8. No Docker / Lean build invocations from this researcher. The slug is COMPLETED, the build was verified by S2 ACT three days ago at the same pinned Mathlib revision, and this PR makes zero `.lean` changes. Re-running the build would be busywork.

## 4. Honest calibration

This is a **low-value, high-precision** cleanup PR. The slug was already COMPLETED with the gallery shipped and the prior STATE-SYNC catchup merged on 2026-05-13. The residual drift items #1-#4 are either prose off-by-ones (#2, #3), a data-integrity nit that affects only downstream tools that scan `leanFiles[]` (#1), or a wording overstatement that could mislead a future seeker into thinking the sibling slug already exists (#4).

I am not claiming a "session" in the sense of advancing proof-of-the-theorem progress — the theorem was already proved. I am cleaning up after S5 STATE-SYNC. Counting this as iteration 5 is mostly a bookkeeping aid (so a future state-sync can see that S5 was followed by S6 within 3 days, instead of misreading the gap and re-doing the same catchup).

If a future researcher claim-randoms back onto this slug, they should release immediately — there is nothing left to do here.

## 5. References (from memory)

- `_researcher_postship_pivot_to_long_completed_slug_with_recent_observe_audit_updated_4_of_5_surfaces_canonical_json_materially_contradicts_observe_findings_ship_13_field_state_sync` — closest pattern match; differs here because the recent catchup was a STATE-SYNC (not OBSERVE), the surfaces were 2-of-4 (state.md + JSON; problem.md + knowledge.md correctly untouched), and the JSON drift is residual (`leanFiles[]` empty, prose off-by-one) rather than a material contradiction of a refuted nextAction. Hence S6 is *much* smaller (~80 LOC session note, 8-field JSON edit) than the 13-field pattern in memory.
- `_mechanic_pnpm_build_regenerates_all_research_jsons` — explicitly skipped `pnpm build` for this single-slug fix; used `wc -l` value (matches gallery `meta.json`).
- `_worktree_absolute_path_lands_in_main_repo_use_dotloom_worktrees_path_or_cp_recovery` — all edits in this PR use the `.loom/worktrees/researcher-1` path; verified `git status` after edits to confirm changes landed in the worktree.
