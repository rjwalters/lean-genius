# Iteration 40 STATE-SYNC — state.md catch-up after Iter 39 PREP #21401

**Date**: 2026-05-31
**Researcher**: researcher-1
**Phase**: STATE-SYNC (doc-only; closes one-sided drift between `state.md` and research JSON `currentState` left by Iter 39 PREP)
**Type**: Doc-only. No edits to `Proofs/BaselProblemOQ01OQ01OQ02OQ03.lean`, gallery `meta.json`, or `knowledge.md`.
**Lake-pinned Mathlib SHA**: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (unchanged from Iter 38 ACT build verification and Iter 39 PREP bearer re-audit).

## Drift Inventory (1 file, 3 fields + 1 narrative gap)

| # | File | Field / Section | Stale | Correct | Source-of-truth |
|---|------|-----------------|-------|---------|-----------------|
| D1 | `state.md` line 4 (`Phase`) | header | `ACT (Iter 38 — 28b-2 witness saturation SHIPPED, build verified; remaining Route B work: 28a Beta-integral)` | `ACT (Iter 39 PREP — 28a Beta-integral paste-ready skeleton SHIPPED doc-only; remaining Route B work: 28a ACT)` | research JSON `currentState.phase` (already bumped by PR #21401) |
| D2 | `state.md` line 7 (`Last Updated`) | header | `2026-05-28 (Iter 38 ACT …)` | `2026-05-31 (Iter 40 STATE-SYNC …)` | this STATE-SYNC |
| D3 | `state.md` line 8 (`Iteration`) | header | `39` | `40` | research JSON `currentState.iteration: 40` (already bumped by PR #21401) |
| D4 | `state.md` body — missing `## Iter 39 PREP` narrative block between `## Iter 38 ACT` (line 10) and the prior `## Iter 37 INFRA-SIGNAL` block | | absent | inserted (see §"Files Modified" below) | Iter 39 PREP session log `sessions/2026-05-31-iter39-prep-28a-paste-ready-skeleton.md` (merged via #21401) |
| D5 | `state.md` `## Current Focus` section (line 107+) | | still describes Iter 35b/Iter 36 (researcher-11, 2026-05-15) as current focus | refreshed to Iter 40 STATE-SYNC and 28a next-ACT pointer; prior text preserved as "Prior focus snapshot (Iteration 36, 2026-05-15)" | research JSON `currentState.focus` + `currentState.nextAction` |
| (bonus) | research JSON `lastUpdate` | | `2026-05-31T00:00:00.000Z` (midnight, PR #21401 stamp) | `2026-05-31T17:00:00Z` (this STATE-SYNC stamp) | this STATE-SYNC |

## Why this STATE-SYNC exists

Iter 39 PREP (PR #21401, merged 2026-05-31) shipped a paste-ready 28a Beta-integral identity skeleton with bearer re-verification. Per the PREP's own §"Honest framing / self-audit" / §"What this PREP does NOT include":

> No edits outside this session log: `state.md`, `knowledge.md`, `problem.md`, gallery `meta.json`, and `src/data/research/problems/*.json` are untouched.

But the merged PR #21401 commit (`b0e937094f7` / `82030debbbe`) **did** touch `src/data/research/problems/basel-problem-oq-01-oq-01-oq-02-oq-03.json` — bumping `currentState.iteration: 38 → 40`, `currentState.phase` (Iter 39 PREP framing), `currentState.focus`, `currentState.nextAction`, `currentState.attemptCounts.total: 28 → 30`, `lastUpdate: 2026-05-28 → 2026-05-31T00:00Z`. This is consistent with prior PREP-iter precedent (Iter 35c STATE-SYNC notes that `lineCount`/`theoremCount` drift is auditor-territory, but `currentState` is in-scope for the PR shipping the iter).

The remaining one-sided drift is in `state.md`, which the PREP explicitly disclaimed editing. This STATE-SYNC closes it.

## Pre-conditions

- **Lean file unchanged**: `proofs/Proofs/BaselProblemOQ01OQ01OQ02OQ03.lean` last touched 2026-05-28 (PR #20863 Iter 38 ACT). HEAD: 1802 LOC, 1 axiom (`hanson_bound`), 0 sorries, 77 theorems + 1 def. Build verified 3066/3066 jobs at lake-pin `2df2f0150c…`.
- **Docker**: UP at 2026-05-31T17:00Z (host disk 12 Gi used / 59 Gi avail; `docker info` instant). Sufficient for a future 28a ACT cache-hit verification.
- **G9 lake self-loop**: STILL present in main repo (`proofs/.lake` → itself). Per `[[project_lake_self_loop_main_repo]]` memory: ship ACT PRs under "build pending — G9 lake self-loop" qualifier; do not fix from inside a research PR. Does not affect this STATE-SYNC (doc-only).
- **Pool sync N/A**: research JSON `status` already matches `.lean/state/candidate-pool.json` `candidates[].status: in-progress`. No `claim-problem.sh update` call needed post-PR.

## Bearer Pin Verification (re-confirmed by Iter 39 PREP)

Iter 39 PREP §"Bearer re-verification at SHA `2df2f0150c…`" inspected all five bearers directly via `gh api repos/leanprover-community/mathlib4/contents/<path>?ref=<SHA>`. Surface area unchanged from Iter 36 PREP and Iter 38 ACT build:

| Bearer | Module | Status (Iter 39 PREP) |
|--------|--------|-------------------------|
| 1: `Complex.betaIntegral_eval_nat_add_one_right` | `Mathlib/Analysis/SpecialFunctions/Gamma/Beta.lean:202-203` | unchanged since Iter 29 |
| 2: `Nat.ascFactorial_eq_prod_range` | `Mathlib/Data/Nat/Factorial/BigOperators.lean:49-51` | unchanged since Iter 29 |
| 3: `Nat.factorial_mul_ascFactorial` *(NEW)* | `Mathlib/Data/Nat/Factorial/Basic.lean:227-233` | newly identified by Iter 39 |
| 4: `Nat.choose_mul_factorial_mul_factorial` *(NEW)* | `Mathlib/Data/Nat/Choose/Basic.lean:141` | newly identified by Iter 39 |
| 5: `Complex.ofReal_pow`, `intervalIntegral.integral_ofReal` | `Mathlib/Data/Complex/Basic.lean` + `Mathlib/MeasureTheory/Integral/IntervalIntegral.lean` | newly framed by Iter 39 (Iter 29 left as Erratum 1) |

Surface area for next ACT (28a Beta-integral identity): the 5 bearers above plus tactic-level `field_simp` / `linear_combination` / `ring` chains. Iter 39 PREP flags `linear_combination` minor syntax drift (v4.25 → v4.26) and `field_simp` over ℂ as the two highest-risk tactic-level dependencies.

## Build Inheritance Argument

Lean file `proofs/Proofs/BaselProblemOQ01OQ01OQ02OQ03.lean` unchanged on `main` since 2026-05-28 (PR #20863 / commit `09810e74cf8`). Lake-pin SHA `2df2f0150c…` stable since 2026-05-12 (Iter 29 PREP first audit). Build status inherits from the last green Iter 38 ACT verification (3066/3066 jobs).

This STATE-SYNC edits **only** doc fields:
- `state.md` (header + 2 new narrative sections + Current Focus refresh)
- `sessions/2026-05-31-iter40-state-sync-after-iter39-prep.md` (this memo, new file)
- `src/data/research/problems/<slug>.json` (`lastUpdate` field only; `currentState.iteration` already at 40)

No `.lean` files touched. Cache-replay forecast: N/A (no source change → no rebuild needed).

## Files Modified (2 in PR + 1 minor JSON `lastUpdate` refresh)

1. `research/problems/basel-problem-oq-01-oq-01-oq-02-oq-03/state.md`:
   - **Header lines 4 / 7 / 8**: Phase, Last Updated, Iteration fields bumped.
   - **New `## Iter 40 STATE-SYNC` section** (between header and `## Iter 38 ACT`): explains the drift and the catch-up.
   - **New `## Iter 39 PREP` section** (between `## Iter 40 STATE-SYNC` and `## Iter 38 ACT`): narrative summary of the PREP — bearer chain, paste-ready calc shell, real-bridge two-path analysis, ACT cost estimate.
   - **`## Current Focus` section** (line 107+): refreshed to point at 28a as the next ACT; prior Iter 36 content preserved as "Prior focus snapshot".
2. `research/problems/basel-problem-oq-01-oq-01-oq-02-oq-03/sessions/2026-05-31-iter40-state-sync-after-iter39-prep.md`: this memo, new file.
3. `src/data/research/problems/basel-problem-oq-01-oq-01-oq-02-oq-03.json`: `lastUpdate` refresh only (`2026-05-31T00:00:00.000Z` → `2026-05-31T17:00:00Z`). All `currentState` fields are already at iteration-40 values from PR #21401.

## What this STATE-SYNC does NOT include

1. **No Lean edits**. The 28a Beta-integral identity ACT is the next researcher's task; the paste-ready skeleton is in `sessions/2026-05-31-iter39-prep-28a-paste-ready-skeleton.md`. Build verification would be Docker-cache-hit at lake-pin `2df2f0150c…` once `proofs/.lake` G9 self-loop is resolved (memory `[[project_lake_self_loop_main_repo]]`).
2. **No `meta.json` edits**. Gallery `src/data/proofs/basel-problem-oq-01-oq-01-oq-02-oq-03/meta.json` `lineCount` / `theoremCount` drift is auditor/mechanic territory (cf. Iter 35c STATE-SYNC precedent), not in scope for this STATE-SYNC.
3. **No `knowledge.md` edits**. Knowledge fields already reflect Iter 38 ACT's 28b-2 witness saturation completion; Iter 39 PREP added paper-level context but no new "built items" or "insights" worth promoting (the Bearer 3 and Bearer 4 identifications are ACT-readiness details, not slug-level knowledge).
4. **No PR for `axiom hanson_bound` closure**. Still 1 axiom; Route B chain needs the 28a Lean ACT first.

## Cross-references

- Iter 28 PREP (2026-05-12, #18352): Route B strategic choice.
- Iter 29 PREP (2026-05-12, #18485): initial Mathlib bearer audit (Bearers 1, 2; Erratum 1 on cpow); Bearers 3 and 4 elided.
- Iter 34a ACT (2026-05-15, #19208): 28b-1 bridge bound + `sum_mod_pow_lt_of_pow_dvd_succ`. Build verified.
- Iter 35b ACT (2026-05-15, #19372): 28c divisibility bridge `choose_mul_succ_dvd_lcmRange`. Build verified.
- Iter 35c STATE-SYNC (2026-05-15, #19316): precedent for this STATE-SYNC's format (doc-only `state.md` + JSON refresh after a multi-PR drain wave; `meta.json` drift left to mechanic).
- Iter 36 PREP (2026-05-15): 28b-2 paste-ready discharge.
- Iter 37 INFRA-SIGNAL (2026-05-25, #20636): Docker gate RED→GREEN.
- Iter 38 ACT (2026-05-28, #20863): 28b-2 witness saturation shipped. Build verified 3066/3066 jobs.
- Iter 39 PREP (2026-05-31, #21401): 28a Beta-integral paste-ready skeleton. The doc-only PREP that this STATE-SYNC catches `state.md` up to.

## Next Steps (deferred to next researcher)

1. **Iter 41 ACT (recommended next)**: ship the 28a Beta-integral identity per Iter 39 PREP paste-ready skeleton (~80-100 LOC). The Lean target is `complex_betaIntegral_nat_eq_choose_inv (n k : ℕ) (hk : k ≤ n)` plus its `real_betaIntegral_nat_eq_choose_inv` cast-bridge or direct-IBP companion. Build verification expected to be cache-hit at lake-pin `2df2f0150c…` (post-G9 self-loop resolution per `[[project_lake_self_loop_main_repo]]` memory).
2. **Iter 42 ACT (after 28a)**: integer-squeeze assembly of `hanson_bound` from 28a + 28b-1 + 28b-2 + 28c + the numerical floor `hanson_n1..hanson_n100` (n₀ ≤ 100 slack budget).
3. **Iter 43 (post-axiom-closure)**: gallery promotion to `verified-original` once `hanson_bound` is a theorem. Parent slug `basel-problem-oq-01-oq-01-oq-02` axiom `lcm_hanson_bound` can then chain to this slug's theorem to reduce parent's axiom count from 5 to 4.

## Pattern Observation

This is the second consecutive STATE-SYNC-class iteration shipped today by researcher-1 (the first being `binomial-theorem-oq-02-oq-02-oq-01` Iter 4 drift-closure, branch `feature/researcher-1`, PR #21539). Pattern: claim-random keeps surfacing slugs where prior iterations left state-tracking drift (deferred CLI calls, missing narrative sections, JSON-only updates). This is healthy — STATE-SYNC iterations close drift at a steady cadence without competing for the same ACT-readiness gates that the 28a Beta-integral ACT needs.
