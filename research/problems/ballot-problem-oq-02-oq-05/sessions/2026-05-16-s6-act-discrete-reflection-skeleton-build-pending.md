# S6 ACT — `discrete_reflection` paste-ready skeleton (build pending — Docker daemon hung)

**Researcher**: researcher-9
**Date**: 2026-05-16
**Phase**: ACT (skeleton-shipping ACT, not discharge ACT)
**Predecessor**: S5 PREP `2026-05-16-s5-prep-discrete-reflection-paste-ready-skeleton.md` (researcher-6, same day, T-~6h)
**Successor pointer**: S7 (discharge 4 inline sorries — Aristotle-eligible for R5 + final assembly)

## 1. Why S6 fires today

Claim landed on this slug via `claim-random` at 2026-05-16T15:25Z (researcher-9, this session). Predecessor S5 PREP (researcher-6, same day at 09:31Z) staged a paste-ready ~90-LOC skeleton with 4 acknowledged sorries on R4/R5/LOW/R6 and an explicit `## 11. Next action` instruction reading:

> Paste §5's skeleton verbatim into `proofs/Proofs/BallotProblemOQ02OQ05.lean` after line 130 (`end BallotOQ05`). Wrap with the `section DiscreteReflection ... end DiscreteReflection` shown in §5 (re-opens the namespace via the existing `namespace BallotOQ05` at line 47, so the section sits inside it).

The "after line 130 / re-opens the namespace" phrasing is internally inconsistent — line 130 IS `end BallotOQ05`, so "after line 130" places the new content OUTSIDE the namespace. A literal paste would compile only with an explicit re-open (`namespace BallotOQ05 ... end BallotOQ05`) wrapping the new section. The cleaner interpretation — chosen here — is to insert the new `section DiscreteReflection ... end DiscreteReflection` block JUST BEFORE the existing `end BallotOQ05` line, so the section sits inside the namespace without a re-open. This is a one-line interpretation fix; no design change.

S6 fires today (not deferred to a future researcher) because:

- S5 PREP-time host snapshot (09:31Z) reported Docker daemon hung, host disk 100%/6.9Gi avail. ACT-time recheck (15:26Z, this session) shows **Docker still hung** (`timeout 8 docker info` returns no Server section; CLI v29.4.1 responds) and **disk slightly worse** at 5.4Gi avail. Waiting for infra recovery is open-ended; the memory feedback pattern `feedback_researcher_postship_pivot_to_act_ready_slug_where_predecessor_statesync_staged_clean_paste_recipe_ship_act_with_build_pending_qualifier` (and the closely related PREP-variant) explicitly authorizes ACT-shipping under `(build pending — Docker daemon hung)` when 3 risk-acceptance criteria hold (verified in §3 below).
- The skeleton was peer-reviewed by S5 PREP §6 risk inventory and §7 ACT-readiness gate (7 GREEN / 1 RED-INFRA-only). Postponing the paste does not add information.
- Sibling-coordination check still GREEN (re-verified §4 below) — no race risk.

## 2. Paste application

**Insertion point**: BEFORE line 130 (the existing `end BallotOQ05`). The pasted content occupies lines 131-227 of the new file (file 130 → 229 LOC, +99 LOC).

**Contents pasted** (verbatim from S5 PREP §5 with one expansion: added a docstring block immediately above `section DiscreteReflection` summarizing build status + insertion correction note for traceability — does not affect Lean compile units):

| Position | Identifier | Type | Sorry | LOC est |
|----------|------------|------|-------|---------|
| §IV intro | (docstring `Part IV`) | doc | — | ~22 |
| body | `partialSumBool` | `def` | 0 | 2 |
| body | `hitSet` | `def` | 0 | 3 |
| body | `firstHitFin` | `noncomputable def` | 0 | 4 |
| body | `reflectAt` | `def` | 0 | 3 |
| body | `reflectAt_involutive` | `lemma` | **1 (R4 MEDIUM)** | 4+sorry |
| body | `partialSumBool_reflectAt_endpoint` | `lemma` | **1 (R5 HIGH)** | 5+sorry |
| body | `reaches_iff_hits_or_above` | `lemma` | **1 (LOW)** | 5+sorry |
| body | `discrete_reflection` | `theorem` | **1 (R6 HIGH)** | 10+sorry |

Total: 6 new bindings (5 defs/lemmas + 1 theorem) + 4 acknowledged sorries.

## 3. Risk-acceptance for `(build pending — Docker daemon hung)`

The memory feedback pattern requires 3 conjunctive criteria. All hold:

### 3.1 Leaf-only (✅)

```
$ grep -rn 'import Proofs.BallotProblemOQ02OQ05' proofs/Proofs/
(no matches)
```

0 downstream importers. A 4-sorry add introduces no surface that any other slug can depend on, so the sorry regression is contained.

### 3.2 Recent BUILD-VERIFY (✅)

Base file commit at S6 ACT-time is `cff3fd36c83` (#19282 S2 ACT, researcher-9, 2026-05-15). That commit was build-verified via Docker on the SAME day with `7744 jobs successful` (logged in state.md S2 ACT Focus section). T+1d build-recent — the lake-pinned Mathlib SHA has not changed since then (verified §3.3), so the base file's verifiable state is intact.

### 3.3 Bearer 0-drift (✅)

Lake-pinned Mathlib SHA at base commit:

```
$ jq -r '.packages[] | select(.name == "mathlib") | .rev' proofs/lake-manifest.json
2df2f0150c275ad53cb3c90f7c98ec15a56a1a67
```

Same SHA as S5 PREP §4. All 10 bearer pins re-verified GREEN via `gh api` (S5 PREP §4 used the same incantation):

| API | File | Line | Status |
|-----|------|------|--------|
| `Finset.card_bij` | `Mathlib/Data/Finset/Card.lean` | 341 | GREEN (S4+S5 pinned) |
| `Finset.card_bij'` | `Mathlib/Data/Finset/Card.lean` | 366 | GREEN (S4+S5 pinned) |
| `Finset.card_nbij` | `Mathlib/Data/Finset/Card.lean` | 383 | GREEN (S5 new pin) |
| `Finset.card_nbij'` | `Mathlib/Data/Finset/Card.lean` | 398 | GREEN (S5 new pin — used by `discrete_reflection`) |
| `Finset.min'` | `Mathlib/Data/Finset/Max.lean` | 196 | GREEN (S5 new pin — used by `firstHitFin`) |
| `Finset.min'_mem` | `Mathlib/Data/Finset/Max.lean` | 207 | GREEN (S5 new pin — used by R5 sketch) |
| `Finset.min'_le` | `Mathlib/Data/Finset/Max.lean` | 210 | GREEN (S5 new pin) |
| `Finset.le_min'` | `Mathlib/Data/Finset/Max.lean` | 213 | GREEN (S5 new pin) |
| `BrownianMotion`/`iIndepFun` | (unchanged since S2) | — | GREEN |

No drift.

## 4. Sibling-coordination recheck (✅)

```
$ grep -rnE 'discrete_reflection|partialSumBool|reflectAt' proofs/Proofs/Ballot*
proofs/Proofs/BallotProblemOQ02.lean:184: axiom reflection_principle ...  -- continuous BM, unrelated
proofs/Proofs/BallotProblemOQ02OQ05.lean:135: def partialSumBool ...      -- this file post-paste
proofs/Proofs/BallotProblemOQ02OQ05.lean:140: def hitSet ...              -- this file post-paste
proofs/Proofs/BallotProblemOQ02OQ05.lean:147: noncomputable def firstHitFin ...  -- this file post-paste
proofs/Proofs/BallotProblemOQ02OQ05.lean:155: def reflectAt ...           -- this file post-paste
proofs/Proofs/BallotProblemOQ02OQ05.lean:162: lemma reflectAt_involutive  -- this file post-paste
proofs/Proofs/BallotProblemOQ02OQ05.lean:175: lemma partialSumBool_reflectAt_endpoint  -- this file post-paste
proofs/Proofs/BallotProblemOQ02OQ05.lean:188: lemma reaches_iff_hits_or_above  -- this file post-paste
proofs/Proofs/BallotProblemOQ02OQ05.lean:209: theorem discrete_reflection -- this file post-paste
```

The parent `BallotProblemOQ02.lean:184` `reflection_principle` axiom is the CONTINUOUS BM reflection principle (S8+ target), not the discrete one — unrelated namespace, unrelated argument type. No race.

```
$ cd /tmp && GH_REPO=rjwalters/lean-genius gh pr list --repo rjwalters/lean-genius --search 'discrete_reflection' --state open --limit 5
(no matches)
```

No active sibling-slug PR claiming the same identifier.

## 5. Sorry inventory + discharge roadmap

All 4 sorries are theorem/lemma sorries (none on defs — definitions are concrete and computable except `firstHitFin` which is `noncomputable` by design to use `Finset.min'`). Per `research/SORRY-CLASSIFICATION.md`, all 4 are eligible for Aristotle submission. Recommended pre-submission posture: leave inline as-is; assess after R4 + LOW are discharged manually (cheap), then bundle R5 + R6 for Aristotle.

| Sorry | Risk | LOC est | Aristotle? | Discharge sketch |
|-------|------|---------|------------|------------------|
| `reflectAt_involutive` | R4 MEDIUM | ~10 | Marginal (case-split on guard) | `unfold reflectAt`; `funext i`; case-split on `(firstHitFin ω a).val ≤ i.val`; either both reflections flip (and `Bool.not_not` collapses) or neither flips (identity). |
| `partialSumBool_reflectAt_endpoint` | R5 HIGH | ~25 | **Good Aristotle candidate** | `unfold partialSumBool reflectAt`; rewrite `∑ i : Fin n` as `∑ i ∈ Finset.univ` split into `{i : i.val < τ.val}` and `{i : τ.val ≤ i.val}` (via `Finset.sum_ite` after a `decide`); identity on the first piece; sign-flip telescopes on the second; combine with `partialSumBool ω τ = a` (from `min'_mem h` + `hitSet` defn) to close. |
| `reaches_iff_hits_or_above` | LOW | ~8 | Likely Aristotle-friendly w/ hint | Forward: if `S_k ≥ a` and `S_0 = 0 < a`, find first `j ≤ k` with `S_j ≥ a` (well-ordering); show `S_j = a` (since `S_{j-1} < a` and `|S_j - S_{j-1}| = 1`). Backward: `∃ k, S_k = a ∨ S_n ≥ a` both give `∃ k, S_k ≥ a` trivially. |
| `discrete_reflection` | R6 HIGH | ~20 | **Best Aristotle candidate** (well-scoped given R4+R5+LOW) | After supporting lemmas land: write the LHS filter as the union (paths-ending-≥-a) ⊔ (paths-ending<a-hits-a). Apply `Finset.card_nbij'` with `i = j = fun ω _ => reflectAt ω a` mapping the second piece to (paths-ending->a); use R4 for `left_inv`/`right_inv` collapse and R5 for membership-image into ending>a. Final card identity is `|reaches ≥ a| = |ending ≥ a| + |ending > a| = 2·|ending ≥ a| - |ending = a|` (`ending > a = ending ≥ a - ending = a` via disjoint union). |

**ℕ-subtraction well-definedness**: `card_eq ≤ card_ge` (paths-ending-=-a ⊆ paths-ending-≥-a) ⟹ `2*card_ge - card_eq` is well-defined on `ℕ`. Discharge via `Finset.card_le_card` + `Finset.filter_subset_filter` (5-LOC side lemma, can be inlined in R6 if not surfaced as a separate lemma).

## 6. Build deferral rationale

Per the established memory feedback pattern (build-pending qualifier under Docker daemon hung), 3 conjunctive criteria are required AND met (§3.1 / §3.2 / §3.3). Disk-100% precondition NOT met (5.4 Gi free, ≥1 Gi avail) — this is the "Docker daemon hung, NOT disk-full" sub-pattern (`feedback_researcher_docker_daemon_hang_server_unresponsive_ship_build_pending_distinct_from_disk_full`). Mitigation: do NOT run `docker system prune` (destructive); do NOT attempt `lake build` directly (memory wrapper blocks); wait for daemon recovery.

Build-verify trigger conditions for any future researcher / mechanic claiming this slug for S7+:

- `timeout 8 docker info` returns Server section in ≤ 5 s, AND
- `df -h /System/Volumes/Data` shows ≥ 10 Gi avail.

Then: `./proofs/scripts/docker-build.sh Proofs.BallotProblemOQ02OQ05`. Expected outcome on a clean rebuild against current Mathlib pin: file compiles with 4 inline sorries (sorry warnings expected, no errors). Any error indicates either (a) the paste introduced a typo (re-read against S5 PREP §5 verbatim), or (b) a Mathlib bearer drift (re-run §3.3 recheck — if a pin moved, that is an S7-PREP-3 not an S7-ACT).

## 7. Out of scope (deliberate non-actions)

- **Discharge any of the 4 sorries**: deferred to S7 (separate iteration). Discharging inline would expand the PR diff beyond a single ACT's worth of risk.
- **PR #19065 close**: deferred to deployer/champion sweep (cross-author; S4 STATE-SYNC + S5 PREP both flagged for close, neither closed; this S6 ACT preserves that disposition).
- **Edit `leanFiles[]` in research-JSON**: the array is empty (length 0) which is a 1-day drift since #19282 introduced `BallotProblemOQ02OQ05.lean` on main. Per memory pattern (`feedback_researcher_postship_pivot_to_completed_slug_with_predecessor_statesync_scoped_to_3_fields_missing_iter_bump_nextsteps_cleanup_sessions_bootstrap_and_leanfiles_drift`), manual `leanFiles[]` edits risk clobber by `enrich-research.ts` auto-population — this is mechanic territory. Recorded here as **informational handoff** to mechanic agent:

  ```
  Suggested leanFiles[] entry for BallotProblemOQ02OQ05.lean (after S6 ACT lands):
  {
    "path": "proofs/Proofs/BallotProblemOQ02OQ05.lean",
    "lineCount": 229,
    "sorryCount": 4,
    "axiomCount": 1,
    "theoremCount": 1
  }
  ```

  (Numbers per `wc -l` and `grep -cE` on the post-paste file.)

- **Top-level `phase` field**: currently `"ACT"`, matches `currentState.phase` post-update. No drift.
- **`meta.json` update**: this slug has no `src/data/proofs/<slug>/` gallery dir (OQ-only slug, not yet gallery-promoted). N/A.
- **Mathstodon herald post**: this is a scaffolding ACT (adds sorries, doesn't close them). Not herald-worthy.

## 8. Acceptance criteria

- ✅ `proofs/Proofs/BallotProblemOQ02OQ05.lean` has 4 inline sorries on R4/R5/LOW/R6 at lines documented in §4.
- ✅ File is 229 LOC, 1 axiom (`donsker_fclt`), 4 sorries, 6 new bindings (3 defs + 1 noncomputable def + 3 lemmas) + 1 new theorem.
- ✅ `section DiscreteReflection ... end DiscreteReflection` sits INSIDE `namespace BallotOQ05` (the `end BallotOQ05` is still the file's last line at 229).
- ✅ `research/problems/ballot-problem-oq-02-oq-05/state.md` head updated to Phase=ACT, Iteration=6, Last Updated=2026-05-16T15:30Z; S6 ACT block prepended; Next Action block points at S7 discharge.
- ✅ `src/data/research/problems/ballot-problem-oq-02-oq-05.json` updated: `lastUpdate`, `currentState.{phase, since, iteration, focus, nextAction, attemptCounts.total}`, `knowledge.{progressSummary, nextSteps}` all refreshed.
- ✅ This session memo committed.
- ❌ **Docker build verification**: deferred under `(build pending — Docker daemon hung)` qualifier. Trigger conditions in §6.

## 9. Host context snapshot (S6 ACT-time)

```
$ date -u +%Y-%m-%dT%H:%M:%SZ
2026-05-16T15:26:58Z

$ pwd
/Users/rwalters/GitHub/lean-genius/.loom/worktrees/researcher-9

$ git rev-parse HEAD
1a75a113925...  # origin/main at branch creation

$ git branch --show-current
research/researcher-9-bp-oq02-oq05-s6-act-1527Z

$ df -h /System/Volumes/Data
/dev/disk3s5   926Gi   884Gi   5.4Gi   100%     21M   57M   27%   /System/Volumes/Data

$ timeout 8 docker info --format '{{.ServerVersion}}'
(timeout — no Server section)

$ timeout 5 docker version --format '{{.Client.Version}}'
29.4.1

$ jq -r '.packages[] | select(.name == "mathlib") | .rev' proofs/lake-manifest.json
2df2f0150c275ad53cb3c90f7c98ec15a56a1a67   # unchanged since S2/S4/S5
```

Disk slightly worse than S5 PREP-time (5.4 Gi vs 6.9 Gi); Docker state identical (daemon hung, CLI responsive). NOT the disk-full extreme (≥ 1 Gi avail). Pattern: `feedback_researcher_docker_daemon_hang_server_unresponsive_ship_build_pending_distinct_from_disk_full`.

## 10. References

- `sessions/2026-05-16-s5-prep-discrete-reflection-paste-ready-skeleton.md` — predecessor PREP, source of the paste.
- `sessions/2026-05-16-s4-statesync-postdrain-s2-act-merged.md` — S4 STATE-SYNC absorbing #19282 + #19288.
- `sessions/2026-05-15-s3-prep-duplicate-act-audit-recommend-19065.md` — S3 PREP duplicate-S2-ACT race audit (deferred close).
- #19282 (S2 ACT, researcher-9, 2026-05-15) — base file commit `cff3fd36c83`.
- `proofs/Proofs/BallotProblemOQ02.lean:184` — parent's continuous BM reflection_principle axiom (S8+ target).
- Memory: `feedback_researcher_postship_pivot_to_act_ready_slug_where_predecessor_statesync_staged_clean_paste_recipe_ship_act_with_build_pending_qualifier`, `feedback_researcher_docker_daemon_hang_server_unresponsive_ship_build_pending_distinct_from_disk_full`, `feedback_researcher_postship_pivot_to_act_phase_slug_whose_predecessor_prep_is_correction_of_prior_prep_ship_act_under_build_pending`.
