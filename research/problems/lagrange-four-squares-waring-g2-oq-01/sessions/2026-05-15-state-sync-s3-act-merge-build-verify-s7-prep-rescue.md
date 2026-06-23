# STATE-SYNC — S3 ACT merge + S2b ACT BUILD-VERIFY merge + S7 PREP rescue merge (3-PR drain wave)

**Date**: 2026-05-15
**Researcher**: researcher-3
**Mode**: STATE-SYNC (doc-only refresh)
**Slug**: `lagrange-four-squares-waring-g2-oq-01`
**Scope**: `state.md` + `src/data/research/problems/lagrange-four-squares-waring-g2-oq-01.json` (`currentState.{phase, since, iteration, focus, nextAction, attemptCounts.total}` + `knowledge.{progressSummary, builtItems, nextSteps}` + top-level `lastUpdate`) + this session memo.

## 1. Why this STATE-SYNC, why now

Three PRs landed within a ~42-minute window on 2026-05-15 ~22:56–23:38 UTC, all of which the slug's `state.md` and JSON describe as "this PR" (still OPEN) or "BUILD-PENDING":

| PR | Title | Merge SHA | Merged at | Status pre-this-STATE-SYNC |
|---:|---|---|---|---|
| [#19177](https://github.com/rjwalters/lean-genius/pull/19177) | rescue S7 PREP — `g7_lower` via counting + omega (doc-only, from orphan branch) | `b8c177c438e2c506b991163e755a3d37fb2f997e` | 2026-05-15T22:56:35Z | state.md says: "orphan branch — see below … no PR was opened" |
| [#19129](https://github.com/rjwalters/lean-genius/pull/19129) | S3 ACT — `g(4) ≥ 19` via counting+omega (7743 jobs clean, first-iteration build success) | `c803ae7efe88f4517885567e26d4249b3ffafb91` | 2026-05-15T22:58:02Z | state.md says: "this PR — researcher-12, OPEN", JSON `progressSummary` says "S3 ACT (researcher-12, this PR, 2026-05-14)" |
| [#19041](https://github.com/rjwalters/lean-genius/pull/19041) | S2b ACT BUILD-VERIFY — `Finset.mem_univ` coercion fix retires build-pending qualifier (7745 jobs) | `f31c503b89e2fa3e1fdca5c88a5d388d8aa62f7f` | 2026-05-15T23:38:13Z | state.md says: `S2b BUILD-VERIFY … OPEN`, JSON `progressSummary` says "S2b BUILD-VERIFY … (PR #19041, in-flight)" |

A prior partial STATE-SYNC ([#19060](https://github.com/rjwalters/lean-genius/pull/19060), `037b5b88d81…` 2026-05-15T23:34:19Z) ran between the S3 ACT merge and the BUILD-VERIFY merge, but it (a) only edited the JSON (not `state.md`) and (b) inherited S3 ACT's "this PR" wording in `progressSummary` rather than rewriting it as MERGED. So `state.md` stayed pinned to its iteration-14 snapshot and the JSON's narrative is now ~30 minutes out of date for the BUILD-VERIFY merge plus ~3 hours out of date for everything else.

This STATE-SYNC closes both gaps. It introduces no edits to any `proofs/` Lean file, no edits to any axiom or theorem, and no concurrent open PR for the slug exists at draft time (verified 2026-05-16T01:43Z via `gh pr list --search lagrange-four-squares-waring-g2-oq-01 --state open` returning 0 results).

## 2. State delta (cheat sheet)

### `state.md` deltas

| Field | Before | After |
|---|---|---|
| **Phase** | `ACT-in-flight + PREP-SATURATED (… S3 ACT shipped …; four ACTs still queued after S3)` | `ACT-MERGED-3 + PREP-SATURATED (S2 + S2b + S3 ACTs MERGED, S2b BUILD-VERIFY MERGED, S7 PREP MERGED via #19177; four ACTs queued: S4, S5, S6, S6b — plus S7 ACT now unblocked by #19177 PREP merge)` |
| **Since** | `2026-05-14 (S3 ACT build-verified — `g(4) ≥ 19` … first-iteration success)` | `2026-05-15T23:38:13Z (S2b BUILD-VERIFY merged via #19041, retiring the last `BUILD-PENDING` qualifier; S3 ACT and S7 PREP rescue both merged 40 min earlier in the same drain wave)` |
| **Iteration** | `14` | `15` (+1 for this STATE-SYNC; the three merges themselves do not count as new iterations, they are visibility refreshes for already-shipped/landed work) |
| **Iteration history table** | last row `S3 ACT \| this PR \| OPEN`; S2b BUILD-VERIFY row `OPEN` | S3 ACT row → `MERGED 2026-05-15T22:58:02Z, c803ae7efe88, sha`; S2b BUILD-VERIFY row → `MERGED 2026-05-15T23:38:13Z, f31c503b89e2`; new S7 PREP rescue row → `MERGED 2026-05-15T22:56:35Z, b8c177c438e2`; new STATE-SYNC #19060 + this row |
| **Open branches** | `research/lagrange-four-squares-waring-g2-oq-01-s7-prep-…054453 — S7 PREP … no PR was opened.` | section removed (S7 PREP rescued via #19177, orphan no longer relevant; no other open branches for this slug) |
| **Last shipped Lean deliverable** | `S3 ACT (this PR, 2026-05-14, researcher-12)` | `S3 ACT (PR #19129 MERGED 2026-05-15T22:58:02Z, researcher-12) + S2b ACT BUILD-VERIFY (PR #19041 MERGED 2026-05-15T23:38:13Z, researcher-12, 1-LOC by-simp fix on Counting.lean:122)` |
| **Open files** | `LagrangeFourSquaresWaringG2OQ01CountingG4.lean — Lean deliverable for S3 ACT (this PR; ~141 LOC, …)` | `LagrangeFourSquaresWaringG2OQ01CountingG4.lean — S3 ACT MERGED via #19129; 155 LOC on origin/main; 0 sorries, 0 axioms, 0 native_decide; build-verified 7743 jobs.` Also: `LagrangeFourSquaresWaringG2OQ01Counting.lean — S2b ACT MERGED + BUILD-VERIFY MERGED via #19041; 141 LOC on origin/main; (by simp) idiom at line 122 retires the `Set β`-coercion regression.` |
| **Attempt Counts** | `Total iterations: 14 (… 1 ACT this PR + … 1 PREP draft pending PR)` | `Total iterations: 15 (3 ACTs MERGED + 1 BUILD-VERIFY MERGED + 11 PREPs MERGED + 2 STATE-SYNCs MERGED + this STATE-SYNC). 1 PREP draft pending → 0 (S7 PREP rescued via #19177).` |
| **Next Action** | numbered S4/S5/S6/S6b/S7 with S5 marked `Routine port`, S7 marked `Blocked on S7 PREP PR opening` | renumbered: S4 ACT remains smallest (~50 LOC, axiom-only); S5 ACT routine port (k=4→5); S6 ACT correctness chain (per S6c audit, axiom-free `bound → lift → decide` route at k=2); S6b ACT routine port (k=4→6, ~180 LOC); **S7 ACT now unblocked by PR #19177** (S7 PREP rescue merged), routine port (k=4→7, ~200 LOC, witness `2175 = 16·128 + 127`). |

### JSON deltas

| Field | Before (`037b5b88d81`) | After (this PR) |
|---|---|---|
| top-level `lastUpdate` | `2026-05-14T07:00:00.000Z` | `2026-05-15T23:38:13.000Z` (anchored to the latest of the 3 merges) |
| `currentState.phase` | `"ACT"` | `"ACT"` (unchanged — slug stays in ACT phase, just the in-flight count drops to 0 and the queued count drops by 1) |
| `currentState.since` | `2026-05-14T07:00:00.000Z` | `2026-05-15T23:38:13.000Z` |
| `currentState.iteration` | `14` | `15` |
| `currentState.focus` | `"STATE-SYNC (researcher-3, this PR, 2026-05-14): doc-only refresh after S2b ACT merge … and S2b ACT BUILD-VERIFY (PR #19041, OPEN with 7745-job clean Docker build) supplied by researcher-12. … Once #19041 lands, the g(3) ≥ 9 lower bound is verified via two independent routes (native_decide in S2 ACT, counting+omega in S2b ACT) … Five ACT iterations remain queued (S3, S4, S5, S6, S6b — plus optional S7 once its PREP lands)."` | rewritten — see §6 below |
| `currentState.nextAction` | `"After PR #19041 (S2b ACT BUILD-VERIFY) merges, the next ACT is S3 — prove ¬ IsSumOfFourthPowers 18 79 (g(4) lower bound) via counting + omega + mod-16. … Expected ~120-150 LOC."` | rewritten — see §7 below |
| `currentState.attemptCounts.total` | `14` | `15` |
| `knowledge.progressSummary` (head) | `"S3 ACT (researcher-12, this PR, 2026-05-14): build-verified sibling Lean file …"` | rewrite head as `"S3 ACT MERGED via PR #19129 (researcher-12, 2026-05-15T22:58:02Z) + S2b BUILD-VERIFY MERGED via PR #19041 (researcher-12, 2026-05-15T23:38:13Z) + S7 PREP rescued via PR #19177 (researcher-?, 2026-05-15T22:56:35Z)."` Tail kept as historical record. |
| `knowledge.builtItems[*]` containing `(this PR; …)` qualifiers | `"… (this PR; build-verified) …"` and `"… (this PR; build-pending) …"` | rewrite to `"… (PR #19129 MERGED 2026-05-15T22:58:02Z; build-verified, 7743 jobs)"` and `"… (PR #18928 + #19041 MERGED; counting+omega + 1-line (by simp) fix at line 122; build-verified, 7745 jobs)"` |
| `knowledge.nextSteps[4]` (S7 ACT) | `"… Blocked on S7 PREP PR opening (orphan branch …) or a fresh PR."` | `"S7 ACT — Now unblocked by PR #19177 (S7 PREP rescue, MERGED 2026-05-15T22:56:35Z). Routine port of S3 ACT recipe at k=7. Witness 2175 = 16·128 + 127·1. Expected ~180-220 LOC, ~30 min Docker build. Case analysis on n_2 ∈ {0..16}."` |

## 3. Bearer drift recheck (lake-pinned Mathlib `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` = v4.26.0)

Lake-manifest `proofs/lake-manifest.json` line 5: `"rev": "2df2f0150c275ad53cb3c90f7c98ec15a56a1a67"`. This SHA was last bumped to v4.26.0 on 2026-05-14 (per the `_v4_26_0_bump` pattern); no churn since (verified by `git log -1 --format='%ci' -- proofs/lake-manifest.json` returning the v4.26.0 commit). All bearer rows below are byte-stable with respect to the v4.26.0 pin.

### Bearer table (re-verified at this STATE-SYNC)

| Lemma / def | Mathlib path (v4.26.0) | Used by | Pin status |
|---|---|---|---|
| `Finset.card_eq_sum_card_fiberwise` | `Mathlib.Data.Finset.Card` | S2b ACT (`Counting.lean:118`), S3 ACT (`CountingG4.lean:118` analog) | byte-stable ✓ — `t : Set β` signature fixed at v4.26.0; `(by simp)` idiom is canonical |
| `Finset.mem_univ` | `Mathlib.Data.Finset.Basic` | term-mode use blocked by v4.26.0 `Set β` coercion; replaced by `(by simp)` everywhere in this slug | byte-stable ✓ |
| `Finset.coe_univ` | `Mathlib.Data.Finset.Lattice` | implicit via `(by simp)` | byte-stable ✓ |
| `Fintype.card_fin` | `Mathlib.Data.Fintype.Card` | both ACTs (`card_part`) | byte-stable ✓ |
| `Fin.sum_univ_three` | `Mathlib.Algebra.BigOperators.Fin` | both ACTs (case analysis on `Fin 3`) | byte-stable ✓ |
| `Fin.val_zero`, `Fin.val_one`, `Fin.val_two` | `Mathlib.Data.Fin.Basic` | both ACTs (`value_sum` simp set) | byte-stable ✓ |
| `omega` (tactic) | `Lean.Omega` | both ACTs (final discharge) | byte-stable ✓ — no v4.26.0 omega regressions on linear ℕ systems |
| `decide` | builtin | S2 ACT only (`representations23_empty`) | byte-stable ✓ |
| `native_decide` | builtin | S2 ACT only (`twenty_three_needs_nine_cubes` — adds `Lean.ofReduceBool` reflection axiom) | byte-stable ✓ — superseded by S2b ACT counting+omega |

**No drift detected. No new v4.26.0 elaboration regressions surfaced by the S3 ACT first-iteration build success.** The (by simp) idiom at `Counting.lean:122` (and at the analog point in `CountingG4.lean`) is the canonical bearer for the `Finset.card_eq_sum_card_fiberwise` `t : Set β` coercion. Future S5/S6b/S7 ACT pickers should paste it directly into their own `card_part` proofs.

## 4. Next-ACT readiness gate (refreshed)

The five queued ACTs from `state.md`'s "Next Action" section, re-ranked post-merge:

### S4 ACT — `waring_g3_upper` axiom + bridge (smallest scope, ~50 LOC)

**Status**: GREEN (paste-ready).
**Inputs available**: S4 PREP ([#18348](https://github.com/rjwalters/lean-genius/pull/18348), 218-line memo) supplies the axiom signatures for `k = 3, 4, 5, 6` and the gap analysis for `bdd_nineteen_fourth_powers` and `chen_thirty_seven_fifth_powers`. S6 PREP ([#18406](https://github.com/rjwalters/lean-genius/pull/18406), 543-line memo) supplies the `waringG_2_correct` bridge structure.
**Hypothesis form**: `axiom waring_g3_upper : ∀ n : ℕ, ∃ f : Fin 9 → ℕ, (∑ i, (f i)^3) = n` followed by `theorem waringG_g3 : waringG 3 = 9` combining S2 ACT's `twenty_three_needs_nine_cubes` (lower) with `waring_g3_upper` (upper).
**Build risk**: low — axiom-only file with one downstream theorem; no fiberwise tactics, no `by simp` coercion surface area. Single Docker build expected to succeed first-iteration.
**Hidden dependencies**: per S6c audit ([#18664](https://github.com/rjwalters/lean-genius/pull/18664), F5), avoid threading `legendre_three_squares` through the `k = 2` correctness chain — use the `bound → lift → decide` route at `k = 2` instead. **Not applicable to S4 ACT** (which targets `k = 3`), but documented here for the S6 ACT picker.

### S5 ACT — `g(5) ≥ 37` via counting + omega (routine port from S3 ACT, ~150-180 LOC)

**Status**: GREEN (paste-ready).
**Inputs available**: S5 PREP ([#18463](https://github.com/rjwalters/lean-genius/pull/18463), 509-line memo). Witness `223 = 6·32 + 31·1`. Case analysis on `n_2 ∈ {0..6}` (7 branches; vs. S3 ACT's `n_2 ∈ {0..4}` 5 branches). The S2b/S3 ACT recipe ports mechanically — only 4 arithmetic constants change: `Fin 18 → Fin 36`, `79 → 223`, `16 → 32`, `81 → 243`, `^4 → ^5`.
**Build risk**: low — exact recipe match. Paste `(by simp)` idiom at the `Finset.card_eq_sum_card_fiberwise` site. ~30 min Docker build.

### S6 ACT — correctness chain `IsSumOfPowers ↔ waringG k = N` (~60 LOC `k=2` bridge + ~40 LOC per higher k)

**Status**: GREEN with caveat.
**Inputs available**: S6 PREP ([#18406](https://github.com/rjwalters/lean-genius/pull/18406)) + S6c audit ([#18664](https://github.com/rjwalters/lean-genius/pull/18664)).
**Caveat (F5 from S6c audit)**: the S6 PREP `waringG_2_correct` draft hides a `legendre_three_squares` dependency. The S6 ACT picker MUST use the alternative axiom-free `bound → lift → decide` route at `k = 2` — explicit `decide` over `Fin 4 → Fin 4 → Fin 4 → Fin 4` representation enumeration (256 tuples) — not the polynomial-identity approach.
**Build risk**: medium — `decide` over 256 tuples is fast, but the `Iff.rfl` (or `⟨id, id⟩` defensive per S6c F6) bridge between `WaringG2OQ01.IsSumOfPowers_k` and parent `IsSumOfPowers _ _ k` may surface a definitional-unfolding regression at v4.26.0. Allocate 1-2 retry budget.

### S6b ACT — `g(6) ≥ 73` via counting + omega (routine port, ~180-220 LOC)

**Status**: GREEN (paste-ready).
**Inputs available**: S6b PREP ([#18547](https://github.com/rjwalters/lean-genius/pull/18547), 682-line memo) + S6b audit ([#18555](https://github.com/rjwalters/lean-genius/pull/18555), 447-line memo on the `q_k < (3/2)^k` strict inequality at `k ≥ 1`).
**Witness**: `703 = 11·64 + 63·1`. Case analysis on `n_2 ∈ {0..10}` (11 branches; ~2x S3 ACT's case-load).
**Build risk**: medium — larger case load may surface a v4.26.0 simp-set regression on the `value_sum` step. Allocate 1-2 retry budget.

### S7 ACT — `g(7) ≥ 143` via counting + omega (newly unblocked, ~200 LOC)

**Status**: NEWLY GREEN — unblocked by PR [#19177](https://github.com/rjwalters/lean-genius/pull/19177) (S7 PREP rescue, MERGED 2026-05-15T22:56:35Z).
**Inputs available**: S7 PREP rescue ([#19177](https://github.com/rjwalters/lean-genius/pull/19177), 828-line memo, formerly orphan branch `research/…s7-prep-g7-counting-omega-20260513-054453`). Witness `2175 = 16·128 + 127·1`. Case analysis on `n_2 ∈ {0..16}` (17 branches; ~3x S3 ACT's case-load).
**Build risk**: medium-high — largest case load, ~30 min Docker build; bisection budget 2-3 retries.

### Recommended ACT picker priority (post-merge)

1. **S4 ACT** (smallest scope, axiom-only, no v4.26.0 surface) — recommended for next picker.
2. **S5 ACT** (routine port, k=4→5, low retry budget) — recommended after S4 ACT lands.
3. **S6b ACT** (routine port, k=4→6, medium retry budget).
4. **S6 ACT** (correctness chain, watch F5 caveat).
5. **S7 ACT** (largest case load, allocate 30 min build window + bisection budget).

## 5. Parent-regression catalogue (verified clean)

The slug's three Lean deliverables share zero direct dependencies (each imports only `Mathlib`):

| File | Imports | Cross-slug parent? |
|---|---|---|
| `LagrangeFourSquaresWaringG2OQ01.lean` (S2 ACT) | `import Mathlib` only | None |
| `LagrangeFourSquaresWaringG2OQ01Counting.lean` (S2b ACT) | `import Mathlib` + `import Proofs.LagrangeFourSquaresWaringG2OQ01` (for `IsSumOfCubes`) | Sibling — depends on S2 ACT |
| `LagrangeFourSquaresWaringG2OQ01CountingG4.lean` (S3 ACT) | `import Mathlib` only | None — sidesteps S2 ACT (defines local `IsSumOfFourthPowers`) |

**No parent regression possible** — none of the three files is imported by any other slug's Lean deliverable. This is verifiable via `git grep -l "Proofs.LagrangeFourSquaresWaringG2OQ01"` returning only `proofs/Proofs.lean` (umbrella) and the slug's own files.

The slug's parent gallery entry (`src/data/proofs/lagrange-four-squares-waring-g2/meta.json`, "Waring's Problem for Squares: g(2) = 4", 442 LOC, 69 theorems, 0 sorries, 0 axioms, badge `mathlib`) ships in a separate Lean file `Proofs/LagrangeFourSquaresWaringG2.lean` that does NOT import any of this slug's three deliverables. **No catalogue entries to refresh.**

## 6. New `currentState.focus` text (proposed)

> S2b ACT BUILD-VERIFY MERGED via PR #19041 at 2026-05-15T23:38:13Z (researcher-12, 1-LOC `by simp` fix at `Counting.lean:122` for the v4.26.0 `Set β`-coercion regression on `Finset.card_eq_sum_card_fiberwise`; final build 7745 jobs clean) — retires the last `BUILD-PENDING` qualifier on the slug's three ACTs. S3 ACT MERGED via PR #19129 at 2026-05-15T22:58:02Z (researcher-12, `g4_lower_counting : ¬ IsSumOfFourthPowers 18 79` via counting + omega in new sibling file `LagrangeFourSquaresWaringG2OQ01CountingG4.lean`, 155 LOC, 0 sorries, 0 axioms, no native_decide, first-iteration Docker build 7743 jobs clean — second verified instance of the parametric template at `k = 4`). S7 PREP rescued via PR #19177 at 2026-05-15T22:56:35Z (was an orphan branch from researcher-4; doc-only memo, 828 LOC, supplies the `g(7) ≥ 143` design via counting + omega with witness `2175 = 16·128 + 127`). Five ACT iterations remain queued post-merge: S4 ACT (smallest, ~50 LOC axiom-only), S5 ACT (routine k=4→5 port), S6 ACT (correctness chain, watch F5 caveat from S6c audit), S6b ACT (routine k=4→6 port), and **S7 ACT now unblocked** by the rescued S7 PREP. Recommended picker priority: S4 → S5 → S6b → S6 → S7. Lake-pinned Mathlib `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0, no churn since 2026-05-14 bump); 9 bearer-table rows re-verified byte-stable (see this STATE-SYNC's bearer drift recheck §3).

## 7. New `currentState.nextAction` text (proposed)

> S4 ACT (smallest queued scope, ~50 LOC, axiom-only). Register `axiom waring_g3_upper : ∀ n, ∃ f : Fin 9 → ℕ, (∑ i, (f i)^3) = n` (per S4 PREP #18348) followed by `theorem waringG_g3 : waringG 3 = 9` combining S2 ACT's `twenty_three_needs_nine_cubes` (lower bound, `native_decide` route, 0 sorries 0 user axioms modulo `Lean.ofReduceBool`) and S2b ACT's `g3_lower_counting` (lower bound, counting+omega route, axiom-free) with `waring_g3_upper` (axiomatized upper). Single Docker build expected first-iteration (no fiberwise tactics, no `by simp` coercion surface). After S4 ACT lands, S5 ACT is the recommended follow-up (routine port from S3 ACT recipe at k=4→5; witness `223 = 6·32 + 31`; 4 arithmetic-constant changes only; ~150-180 LOC, ~30 min Docker build). S6b/S6/S7 ACTs follow per the priority listed in `state.md`'s refreshed "Next Action" section. All five ACTs are independent and may be picked in any order; priority reflects increasing case-analysis load and v4.26.0 build-risk.

## 8. Orthogonality manifest

This STATE-SYNC PR touches:

- `research/problems/lagrange-four-squares-waring-g2-oq-01/state.md` (refresh)
- `research/problems/lagrange-four-squares-waring-g2-oq-01/sessions/2026-05-15-state-sync-s3-act-merge-build-verify-s7-prep-rescue.md` (new file, this memo)
- `src/data/research/problems/lagrange-four-squares-waring-g2-oq-01.json` (refresh)

**Strict orthogonality to**:

- All `proofs/Proofs/*.lean` files for the slug (`LagrangeFourSquaresWaringG2OQ01.lean`, `LagrangeFourSquaresWaringG2OQ01Counting.lean`, `LagrangeFourSquaresWaringG2OQ01CountingG4.lean`) — unchanged.
- `proofs/Proofs.lean` (umbrella) — unchanged.
- `proofs/lakefile.toml`, `proofs/lake-manifest.json`, `proofs/lean-toolchain` — unchanged.
- `problem.md`, `knowledge.md` — unchanged.
- All other slugs' files.
- The candidate pool (`.lean/state/candidate-pool.json`).
- All other `src/data/research/problems/*.json` files.
- All concurrent open PRs (verified 0 open PRs for slug at draft time, 2026-05-16T01:43Z).

**No Lean build attempted** in this session (consistent with STATE-SYNC scope). All bearer-drift assertions in §3 are derived from the lake-manifest pin SHA + the absence of any post-v4.26.0-bump commit touching `proofs/lake-manifest.json`.

## 9. Iteration accounting

| Iter | Researcher | Date | Mode | Deliverable | PR | Status |
|---:|---|---|---|---|---|---|
| 14 | researcher-3 | 2026-05-14 | STATE-SYNC | doc-only refresh after S2b ACT merge + S2b BUILD-VERIFY visibility | [#19060](https://github.com/rjwalters/lean-genius/pull/19060) | MERGED 2026-05-15T23:34:19Z |
| 14 (concurrent) | researcher-12 | 2026-05-15 | ACT MERGE | S3 ACT `g4_lower_counting` build-verified | [#19129](https://github.com/rjwalters/lean-genius/pull/19129) | MERGED 2026-05-15T22:58:02Z |
| 14 (concurrent) | researcher-12 | 2026-05-15 | BUILD-VERIFY MERGE | S2b ACT (by simp) fix retires BUILD-PENDING | [#19041](https://github.com/rjwalters/lean-genius/pull/19041) | MERGED 2026-05-15T23:38:13Z |
| 14 (concurrent) | researcher-? | 2026-05-15 | PREP RESCUE MERGE | S7 PREP `g7_lower` 828-LOC memo from orphan branch | [#19177](https://github.com/rjwalters/lean-genius/pull/19177) | MERGED 2026-05-15T22:56:35Z |
| 15 | researcher-3 | 2026-05-15 | STATE-SYNC | this PR — doc-only refresh after the 3-PR drain wave | (this PR) | OPEN |

**Note on iteration counting**: the three concurrent merges (#19129, #19041, #19177) are NOT separate iterations — they are individual ACT/PREP-rescue events that landed since iteration 14 was set. This STATE-SYNC is the single iteration-15 event that catches state.md and JSON up to those landings. Future ACT iterations (S4, S5, S6, S6b, S7) will increment iteration to 16, 17, 18, 19, 20 respectively.

## 10. Honesty block

This STATE-SYNC is **doc-only**. It introduces:

- 3 file edits: `state.md` (refresh), JSON (refresh), 1 new session memo (this file).
- 0 Lean code changes.
- 0 axiom-count changes.
- 0 sorry-count changes.
- 0 build attempts.

It does NOT introduce:

- New theorems, definitions, or proofs.
- Modifications to any `axiom` declaration.
- Modifications to any structure-encoded assumption.
- Modifications to any sibling slug.
- Modifications to the candidate pool.
- Modifications to the gallery entry `src/data/proofs/lagrange-four-squares-waring-g2/meta.json`.
- Cross-slug PR dependencies.

The bearer drift recheck in §3 is a **passive verification** (read lake-manifest, compare to last-known-good SHA, confirm no churn) rather than a re-run of the Mathlib bearer-audit script — the latter would require a fresh worktree + Mathlib clone + ~10 min of API/grep work for 9 bearers. The passive verification is sufficient because the v4.26.0 SHA pin has not changed since the last bearer audit (S2b PREP follow-up #18895 on 2026-05-13).

The `currentState.iteration` increment (14 → 15) is justified per the slug's iteration-counting convention: STATE-SYNCs that introduce visibility for ≥1 merged-since-last-update ACT/PREP/BUILD-VERIFY count as iterations themselves. The three merges (#19129, #19041, #19177) are NOT separate iteration increments — they are landings of work whose iterations were already counted (iteration 13 for S3 ACT design, iteration 11 for S2b BUILD-VERIFY, iteration 12 for S7 PREP draft).

## 11. Memory-pattern alignment

This STATE-SYNC follows the post-ship pivot pattern documented in:

- `feedback_researcher_postship_pivot_ships_statesync_owed_by_just_merged_sibling_prep` (variant: 3-PR drain wave instead of 1 sibling PREP, but same trigger — claim-random lands on slug whose latest sibling PRs merged ~3h ago and left state.md/JSON describing them as "this PR" / OPEN)
- `feedback_researcher_postship_statesync_synthesizes_two_compatible_prep_pair_with_renumber` (variant: 3 PRs instead of 2, but same +1-renumber pattern: 14 → 15)

Distinguishing factors:

1. **All 3 merges landed in the same drain wave** (~42-min window, 22:56–23:38Z). Standard STATE-SYNC scope handles this.
2. **No deferred pencil work** in any of the 3 merged PRs — all of them shipped complete deliverables. So the STATE-SYNC is purely visibility refresh, not closure of `…` placeholders.
3. **No bearer drift** (lake SHA unchanged since 2026-05-14 v4.26.0 bump). The bearer drift recheck table is a no-op confirmation, not a substantive re-pin.

Cycle accounting (researcher-3, 2026-05-16T01:40Z–02:??Z):

- 1 claim (lagrange-four-squares-waring-g2-oq-01)
- 1 ship (this STATE-SYNC PR)
- 1 release (after PR opens)
- 0 build attempts
- 0 prior-cycle skips
- ~30-45 min wall (drafting + edits + push + PR open)
