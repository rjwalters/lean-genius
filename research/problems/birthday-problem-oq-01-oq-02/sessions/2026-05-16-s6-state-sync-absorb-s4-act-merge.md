# S6 STATE-SYNC — absorb S4 ACT merge (PR #19422), research-JSON catchup

**Date**: 2026-05-16
**Researcher**: researcher-10
**Phase**: STATE-SYNC (post-S4-ACT-merge)
**Status**: doc-only

## 0. TL;DR

S4 ACT (PR #19422, `probCollision_ge_paley_zygmund` + private bridge `one_sub_exp_neg_ge_div_one_add`, 7744-job build verified) **MERGED 2026-05-16T04:40:14Z** (merge commit `cbfc0fdd8f1`). The PR body explicitly states "a follow-on S6 STATE-SYNC is owed to absorb this ACT" — this iteration discharges that.

**No Lean source touched.** Catch-up scope:

1. **state.md head**: Phase ACT (S2b complete, build-verified) → ACT (S4 complete, build-verified, S6 STATE-SYNC catch-up). Iteration 6 → 7.
2. **state.md Iteration History**: append S4 ACT row (PR #19422, 2026-05-16T04:40:14Z merge, 7744 jobs).
3. **state.md Next Action**: rewrite from "S4 ACT paste-ready" (DONE) to "S5 PREP — tight Paley-Zygmund denominator" (per PR #19250 §R5 + this PR's roadmap §3).
4. **state.md Open PRs**: refresh to (this PR — S6 STATE-SYNC).
5. **JSON research file** (`src/data/research/problems/birthday-problem-oq-01-oq-02.json`): 13-field drift catch-up (`phase`, `currentState.{phase, since, iteration, focus, attemptCounts.{total, currentApproach}, nextAction}`, `knowledge.{progressSummary, builtItems, insights, nextSteps}`).
6. **knowledge.md**: append Insight 6 — F-extra trap (`field_simp` needs `ring` for algebraic residue `1 + x - 1 = x` in bridge lemma).

Cycle is **doc-only** — no Lean changes, no Docker build required.

**Infrastructure**: Docker daemon hung (`timeout 5 docker info --format '{{.ServerVersion}}'` → exit 124; `df -h /System/Volumes/Data` → 100% / 6.9Gi avail) at session start. **Irrelevant to this iteration** (doc-only STATE-SYNC).

## 1. Drift inventory (state.md + research JSON)

### state.md drift (predates PR #19422 merge 2026-05-16T04:40:14Z)

| Field | Pre-S6 (current main) | Actual (post-PR-#19422) | Action |
|-------|------------------------|--------------------------|--------|
| Head `**Phase**` | `S3 ACT + S4 PREP merged (Path Z scaffold ready, paste-ready against main)` | `S4 ACT merged (probCollision_ge_paley_zygmund, build verified 7744 jobs)` | rewrite |
| Head `**Iteration**` | 6 | 7 | bump |
| Head `**Since**` | `2026-05-15T23:30:27Z (S3 ACT PR #19098 merged; STATE-SYNC researcher-3)` | `2026-05-16T04:40:14Z (S4 ACT PR #19422 merged; STATE-SYNC researcher-10)` | rewrite |
| `## Next Action` | `S4 ACT (next Lean-modifying iteration): Paste PR #19250 §4's 25-LOC Path Z scaffold...` | `S5 PREP (next iteration): Tighten Paley-Zygmund denominator from 2d + k(k-1) to 2d + k(k-1) - 2 via full E[X²] expansion (~120 LOC, gain Δ ≈ 0.0003)` | rewrite |
| `## Open PRs` | `(this PR — S2a ACT)` | `(this PR — S6 STATE-SYNC)` | rewrite |
| `## Iteration History` | missing S4 ACT row | add: `S4 / 2026-05-16 / researcher-? / #19422 / ACT — probCollision_ge_paley_zygmund + private bridge; +61 LOC (143→203); Docker 7744 jobs; 0 sorries, 0 axioms` | append |

### Research JSON drift (`src/data/research/problems/birthday-problem-oq-01-oq-02.json`)

13 fields require refresh:

| Field | Pre-S6 | Post-S6 |
|-------|--------|---------|
| `phase` | `"S3 ACT + S4 PREP merged"` | `"S4 ACT merged"` |
| `currentState.phase` | `"S3 ACT + S4 PREP merged"` | `"S4 ACT merged"` |
| `currentState.since` | `"2026-05-15T23:30:27.000Z"` | `"2026-05-16T04:40:14.000Z"` |
| `currentState.iteration` | 6 | 7 |
| `currentState.focus` | 1.5KB string about S5 STATE-SYNC catch-up | rewrite to summarize S4 ACT MERGED outcome + S6 STATE-SYNC scope |
| `currentState.attemptCounts.total` | 6 | 7 |
| `currentState.attemptCounts.currentApproach` | 6 | 7 |
| `currentState.nextAction` | 1.2KB string detailing S4 ACT paste recipe | rewrite to S5 PREP target (tight Paley-Zygmund) |
| `knowledge.progressSummary` | 2.8KB through S5 STATE-SYNC | append S4 ACT MERGED + S6 STATE-SYNC |
| `knowledge.builtItems` | 2 items (`one_sub_prod_le_sum`, `probCollision_le_choose_two_div`) | append `probCollision_ge_paley_zygmund` + `one_sub_exp_neg_ge_div_one_add (private bridge)` |
| `knowledge.insights` | 5 items | append F-extra trap insight (field_simp + ring) |
| `knowledge.nextSteps` | 5 items, first is S4 ACT | remove S4 ACT (done), elevate S5 PREP + S6 PREP to position 1-2 |
| `lastUpdate` | (absent / null) | `2026-05-16T<this-PR-timestamp>` (introduce field) |

## 2. S4 ACT outcome summary (post-merge)

From PR #19422 body + merge commit `cbfc0fdd8f1`:

- **File**: `proofs/Proofs/BirthdayProblemOQ01OQ02.lean` 143 → 203 LOC (+61, 0 deletions).
- **New declarations** (2 total): 1 private + 1 public.
  - `private lemma one_sub_exp_neg_ge_div_one_add (x : ℝ) (hx : 0 ≤ x) : x / (1 + x) ≤ 1 - Real.exp (-x)` (L151–165)
  - `theorem probCollision_ge_paley_zygmund (k d : ℕ) (hkd : k ≤ d) (hd : 0 < d) : ((k : ℝ) * ((k : ℝ) - 1)) / (2 * (d : ℝ) + (k : ℝ) * ((k : ℝ) - 1)) ≤ probCollision k d` (L173–203)
- **Build**: 7744 jobs green at v4.26.0 / Mathlib pin `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` / 10s warm cache.
- **Sorries**: 0 (unchanged). **Axioms**: 0 (unchanged).
- **Total theorem count**: 4 (was 2 after PR #19098 = `one_sub_prod_le_sum` + `probCollision_le_choose_two_div`; now also `one_sub_exp_neg_ge_div_one_add` private + `probCollision_ge_paley_zygmund` public).

### Closed-form bracket on `probCollision k d` (post-S4)

The slug now states a complete closed-form 2-sided bracket without any OQ01 parent dependency:

```
k(k-1) / (2d + k(k-1))  ≤  probCollision k d  ≤  k(k-1) / (2d)
```

Both bounds purely intra-namespace; OQ01's 7 v4.26.0 regressions remain owned by a separate mechanic/doctor pass per S5 §5 catalogue (carried forward in S6 unchanged).

### F-extra trap surfaced at S4 ACT iter 1 (NEW, not in S4c/S5/S5b registers)

Per PR #19422 body §"ACT-time elaboration fixes":

> F-extra: `field_simp` on `1 - 1/(1+x) = x/(1+x)` leaves `1 + x - 1 = x` | **NEW at iter 1** | append `ring` | +1

S5b §5 had claimed `field_simp` would auto-close the identity given `hx1 : 0 < 1 + x`; this was correct for the side-condition but missed the algebraic residue. Build iter 1 failed at L159:51 with `unsolved goals: ⊢ 1 + x - 1 = x`; iter 2 with `ring` appended built green at `[7744/7744] (10s)`.

**Insight 6 (new)**: `field_simp` does NOT discharge algebraic residues after clearing denominators. Always pair with `ring` (or `linarith`/`nlinarith` if the residue is inequality-typed) to close out the cleared-fraction goal. The "field_simp closes the goal" heuristic only holds when the cleared form is `0 = 0` or directly typeclass-decidable.

## 3. S5 PREP target (S5 = tight Paley-Zygmund)

Per PR #19250 §R5 + state.md L172–176, the next non-STATE-SYNC iteration is:

**S5 PREP — Tight Paley-Zygmund (Path Y elaboration)**: tighten the lower-bound denominator from `2d + k(k-1)` (current S4 ACT) to `2d + k(k-1) - 2` using exact second-moment formula `E[X²] = E[X] + C(n,2) * (C(n,2) - 1) / d²` instead of variance bound `Var(X) ≤ E[X]`.

**Gain**: Δ ≈ 0.0003 at threshold `n = 23, d = 365` (lower bound 0.4732 → 0.4735). Marginal, but completes the textbook closed-form Paley-Zygmund.

**LOC budget**: ~120 LOC for the full elaboration (one major helper for second-moment formula + one closed-form theorem mirroring `probCollision_ge_paley_zygmund` with the tighter denominator).

**Risk**: MEDIUM — requires the second-moment formula `E[X²]` which depends on the OQ02 product expansion. Not blocked by OQ01 regressions.

This is **deferred from S6** — S6 is doc-only STATE-SYNC. S5 PREP target stands ready for the next research session.

## 4. S6 PREP target (S6 = bridge to OQ01OQ01 finite-sample-space `collisionCount`)

Per PR #18921's S1 OBSERVE design + knowledge.md "Active Approach" §:

**S6 PREP — Bridge OQ02-product to OQ01OQ01-counting**: prove `probAllDistinct_eq_descFactorial_div`:

```
probAllDistinct k d = (d.descFactorial k : ℝ) / (d : ℝ)^k
```

Connects OQ02's product `∏ (1 - i/d)` with OQ01OQ01's counting-formula form (descending factorial / total-mappings). ~30 LOC telescoping.

This is needed for Path Y's full variance-form pipeline (S5 elaboration). **Independent of S5 PREP** (can be done in parallel).

## 5. OQ01 parent-regression handoff (unchanged from S4c/S5)

The 7 v4.26.0 errors in `BirthdayProblemOQ01.lean` (sibling slug, not this slug's responsibility):

| Line | Error | Replacement candidate |
|------|-------|------------------------|
| L408 | `Nat.choose_three_right` removed | Manual `Nat.choose_succ_succ` + arithmetic chain |
| L420 | `native_decide` on `C(23, 2) = 253` | `decide` or explicit `Nat.choose_eq_factorial_div_factorial` |
| L453 | `native_decide` on `C(28, 2) = 378` | as above |
| L476 | `native_decide` on `2 * 365` | `decide` |
| L483 | `native_decide` on `C(28, 2) - 365` | as above |
| L498-499 | `native_decide` on cross-product | as above |
| L510-511 | `native_decide` on `C(28, 2) ≤ 2 * 365` | as above |

**Status**: catalogue stable since S4c PREP (PR #19315 §5); no mechanic/doctor PR has touched `BirthdayProblemOQ01.lean` between S5 STATE-SYNC merge (2026-05-16T03:51Z) and S6 STATE-SYNC commit (this PR). Owned by separate-slug repair.

## 6. Bearer-pin drift recheck (sibling check at S6 time)

Lake SHA at `proofs/lake-manifest.json`: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (unchanged from S4c/S5/S5b/S4-ACT — all reference the same pin).

Time elapsed since S5b PR #19417 (last bearer recheck): 2026-05-16T03:51:17Z → 2026-05-16T~10:00Z = ~6h10min. By lake-manifest immutability argument (no Mathlib bump committed to main between PR #19454's S2-A ACT @ ecb47b3 and this S6 STATE-SYNC's commit), all 9 S4c-era bearers + the 4 S4 ACT-era bearers (`Real.add_one_le_exp`, `Real.exp_neg`, `one_div_le_one_div_of_le`, `intervalIntegral.integral_comp_mul_left` — wait, last not relevant here) remain byte-stable.

**Net drift**: 0. No bearer rows require updating.

## 7. Failure-mode register update (F1–F8)

Carries forward from S4c §4 (F1–F6) + S5 §4 (F7 paste-anchor) + S5b §3/§4 (F8/F9 pre-pin), plus 1 new:

| Marker | Trap | Source | Status |
|--------|------|--------|--------|
| F1–F6 | (per S4c §4 register) | S4c PREP | unchanged |
| F7 | Paste outside namespace | S5 §4 | unchanged |
| F8 | `set S` + `linarith` doesn't bridge unfolded term | S5b §3a | **PRE-PINNED, fired & fixed at S4 ACT iter 1** |
| F9 | `Real.exp_neg` gives `⁻¹` not `1/_` | S5b §4a | **PRE-PINNED, fired & fixed at S4 ACT iter 1** |
| **F-extra** | `field_simp` on `1 - 1/(1+x) = x/(1+x)` leaves `1 + x - 1 = x` | **S4 ACT iter 1 (NEW)** | **NEW** — `ring` append fix at iter 2; carried into S6 insights |

**F-extra is the only addition** — F1–F9 are now closed (S4 ACT shipped clean, all surfaced traps fixed).

## 8. ACT-readiness for S5 PREP (forward-looking)

Gate items if/when a researcher claims this slug for S5 PREP:

| # | Item | Status |
|---|------|--------|
| 1 | Mathematical scope (tight Paley-Zygmund Δ ≈ 0.0003) | ✅ GREEN — §3 |
| 2 | Path Y design memo (S4 PREP §"Path Y" ~120 LOC) | ✅ GREEN — PR #19250 §Path-Y |
| 3 | Second-moment formula `E[X²]` known | ⚠️ AMBER — formula known mathematically (`E[X²] = E[X] + C(n,2)*(C(n,2)-1)/d²`), but no Mathlib direct API |
| 4 | OQ02 dependencies stable | ✅ GREEN — OQ02 unchanged since S5b |
| 5 | OQ01 dependencies stable | ✅ GREEN — bracket avoids OQ01 |
| 6 | Bearer pin verified at S6 time | ✅ GREEN — §6 |
| 7 | F-extra trap documented | ✅ GREEN — §2 |
| 8 | Docker reachable for S5 PREP (doc-only)? | N/A — PREP is doc-only |

**Gate**: 6/8 GREEN, 1/8 AMBER (E[X²] Mathlib API surface unverified), 1/8 N/A. S5 PREP is **READY** modulo a 5-min API recheck for `E[X²]` machinery in `Mathlib.Probability.Variance` (likely needs ad-hoc derivation from `BirthdayProblemOQ02.gauss_sum_div` + `gauss_sum_sq_div` if the latter exists).

## 9. Honest scope disclaimers

- **0 Lean code changes**: 0 LOC delta to `proofs/Proofs/BirthdayProblemOQ01OQ02.lean` (203 LOC unchanged).
- **0 Docker build**: not required for doc-only STATE-SYNC.
- **JSON `lastUpdate` field**: introduced (was absent/null in prior STATE-SYNCs). If schema validation breaks downstream, the field can be reverted; otherwise this normalizes the slug to match the schema documented in `src/data/research/SCHEMA.md` (or `.lean/scripts/research-schema/`).
- **S6 absorbs 1 PR** (#19422); S5 absorbed 1 PR (#19098). No batched-multi-ACT absorb here.
- **No new insights to `knowledge.md` beyond F-extra**: the 5 existing insights from S1–S5 cover the mathematical content. F-extra is the only S4-ACT-time-discovered trap.

## 10. Memory cross-references

This cycle follows memory pattern `_postship_pivot_lands_on_slug_where_recent_act_did_partial_inline_statesync_leaving_n_drift` in spirit, BUT differs because:

- The "predecessor ACT" (PR #19422) explicitly DECLARED in its body "a follow-on S6 STATE-SYNC is owed to absorb this ACT (state.md `phase` → `S4 ACT merged`; `iteration` 6 → 7; JSON `currentState` refresh; bearer table augmented with `Real.exp_neg`'s `← one_div` form + `field_simp + ring` trap). Not done here to keep PR Lean-only."
- So this is **planned-deferred-STATE-SYNC**, not "drift from partial inline state-sync". The work-package was explicit at S4-ACT-time; this S6 discharges it.

Sibling-slug check: oq-03-oq-01-oq-02-oq-01 has its own S22 STATE-SYNC (PR #19405, 2026-05-16T03:51:48Z). No cross-slug interaction with this STATE-SYNC.

Distinct from:
- `_partial_inline_statesync_leaving_n_drift` — there the predecessor ACT partially synced inline; here PR #19422 explicitly deferred.
- `_postship_pivot_lands_on_audit_corrected_skeleton_with_sorries_docker_unsafe_upgrade_to_paste_ready` — Lean-content PREP, not STATE-SYNC.
- `_postship_pivot_lands_on_slug_whose_juststatesync_conditional_pivot_recommendation_needs_prestaging` — pre-staging vs absorbing.

## 11. Files touched (this PR)

| File | Delta | Reason |
|------|-------|--------|
| `research/problems/birthday-problem-oq-01-oq-02/sessions/2026-05-16-s6-state-sync-absorb-s4-act-merge.md` | new (~360 LOC) | This session memo |
| `research/problems/birthday-problem-oq-01-oq-02/state.md` | +30/-40 (refresh head + Next Action + Open PRs; append S4 ACT + S6 row to Iteration History; add S6 STATE-SYNC section) | Catch-up |
| `research/problems/birthday-problem-oq-01-oq-02/knowledge.md` | +20 (append Insight 6: F-extra trap) | New trap |
| `src/data/research/problems/birthday-problem-oq-01-oq-02.json` | 13-field refresh | Catch-up |

**Total**: ~3 files modified + 1 new file. 0 Lean source changes. 0 Docker build.
