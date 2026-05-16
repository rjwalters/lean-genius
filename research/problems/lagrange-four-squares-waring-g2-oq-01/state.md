# Current State

**Phase**: ACT-MERGED-3 + PREP-SATURATED (S2 + S2b + S3 ACTs MERGED on origin/main; S2b BUILD-VERIFY MERGED; S7 PREP rescued and MERGED via #19177; S1 → S7 PREP layer fully on origin/main; four ACTs queued — S4, S5, S6, S6b — plus S7 ACT now unblocked)
**Since**: 2026-05-15T23:38:13Z (S2b ACT BUILD-VERIFY merged via [#19041](https://github.com/rjwalters/lean-genius/pull/19041); S3 ACT merged via [#19129](https://github.com/rjwalters/lean-genius/pull/19129) ~40 min earlier in the same drain wave; S7 PREP rescued via [#19177](https://github.com/rjwalters/lean-genius/pull/19177))
**Iteration**: 15 (+1 STATE-SYNC for the 3-PR drain wave on top of iteration 14: S1 OBSERVE, S2 ACT, S2b PREP, S3 PREP, S4 PREP, S5 PREP, S6 PREP, S6b PREP, S6b audit, S6c audit, S2b bearer audit, S2b ACT, S2b BUILD-VERIFY, S3 ACT, **STATE-SYNC #19060 + this STATE-SYNC**)

## Current Focus

**This iteration is a STATE-SYNC** (researcher-3, 2026-05-15) catching `state.md` and JSON up to the 3-PR drain wave that landed at 2026-05-15T22:56–23:38 UTC. See `sessions/2026-05-15-state-sync-s3-act-merge-build-verify-s7-prep-rescue.md` for full delta.

Lower-bound layer `g(k) ≥ N` design coverage is **saturated through k = 7** under the parametric "counting + omega" template established by S2b PREP / S3 PREP / S5 PREP / S6b PREP / S7 PREP (all five PREPs MERGED post-rescue). Upper-bound layer is **fully specified as an axiom inventory** (S4 PREP). The semantic correctness chain bridging local `IsSumOfPowers` predicates to `waringG k = N` is **scoped** (S6 PREP) and **audited** for typing/axiom errors (S6c PREP).

**S2b ACT BUILD-VERIFY MERGED** (PR [#19041](https://github.com/rjwalters/lean-genius/pull/19041), 2026-05-15T23:38:13Z, researcher-12): 1-LOC `by simp` fix at `LagrangeFourSquaresWaringG2OQ01Counting.lean:122` retiring the v4.26.0 `Set β`-coercion regression on `Finset.card_eq_sum_card_fiberwise`; final build 7745 jobs clean. The slug's lower bound `g(3) ≥ 9` is now verified via two independent routes (S2 ACT `native_decide` + S2b ACT counting+omega), with the latter axiom-free modulo no reflection-axiom dependency.

**S3 ACT MERGED** (PR [#19129](https://github.com/rjwalters/lean-genius/pull/19129), 2026-05-15T22:58:02Z, researcher-12): `WaringG2OQ01.CountingG4.g4_lower_counting : ¬ IsSumOfFourthPowers 18 79` shipped in new sibling file `LagrangeFourSquaresWaringG2OQ01CountingG4.lean` (155 LOC on origin/main, 0 sorries, 0 axioms, no `native_decide`). First-iteration Docker build 7743 jobs clean — the S2b BUILD-VERIFY `(by simp)` fix was incorporated up front. The parametric template is now verified at `k ∈ {3, 4}`.

**S7 PREP rescued** (PR [#19177](https://github.com/rjwalters/lean-genius/pull/19177), 2026-05-15T22:56:35Z): doc-only memo (828 LOC) supplying the `g(7) ≥ 143` design via counting + omega (witness `2175 = 16·128 + 127`). S7 PREP was previously an orphan branch (`research/lagrange-four-squares-waring-g2-oq-01-s7-prep-g7-counting-omega-20260513-054453`); the rescue PR opens S7 ACT as a routine port of the S3 ACT recipe at `k = 7`. After this STATE-SYNC, **five ACT iterations remain queued: S4 (smallest, axiom-only), S5 (routine k=4→5 port), S6 (correctness chain), S6b (routine k=4→6 port), S7 (now unblocked, routine k=4→7 port).**

**Last shipped Lean deliverables** (origin/main, byte-stable at lake SHA `2df2f01…` v4.26.0):
- S3 ACT — `WaringG2OQ01.CountingG4.g4_lower_counting : ¬ IsSumOfFourthPowers 18 79` (PR [#19129](https://github.com/rjwalters/lean-genius/pull/19129) MERGED, 0 sorries, 0 axioms, counting+omega, no `native_decide`); `proofs/Proofs/LagrangeFourSquaresWaringG2OQ01CountingG4.lean` (155 LOC); registered in `proofs/Proofs.lean`.
- S2b ACT BUILD-VERIFY — `(by simp)` fix at `LagrangeFourSquaresWaringG2OQ01Counting.lean:122` (PR [#19041](https://github.com/rjwalters/lean-genius/pull/19041) MERGED, 7745 jobs clean).
- S2b ACT — `WaringG2OQ01.Counting.g3_lower_counting : ¬ IsSumOfCubes 8 23` via counting+omega (PR [#18928](https://github.com/rjwalters/lean-genius/pull/18928) MERGED 2026-05-13); `proofs/Proofs/LagrangeFourSquaresWaringG2OQ01Counting.lean` (141 LOC, 0 sorries, 0 axioms post-#19041).
- S2 ACT — `WaringG2OQ01.twenty_three_needs_nine_cubes : ¬ IsSumOfCubes 8 23` via `native_decide` (PR [#18176](https://github.com/rjwalters/lean-genius/pull/18176) MERGED 2026-05-12); `proofs/Proofs/LagrangeFourSquaresWaringG2OQ01.lean` (118 LOC).

## Active Approach

**Two-tier strategy: lower bounds verified, upper bounds axiomatized.** Verified — S4 PREP confirms upper bounds for `k ∈ {3, 4, 5, 6}` are research-level (Wieferich–Kempner 1909/1912, BDD 1986, Chen 1964, Pillai 1940) and must enter as `axiom` declarations rather than proved theorems.

**Lower-bound proof technique**: parametric "counting + omega".

1. *Bounding step*: each summand `f i` satisfies `(f i)^k ≤ n_k < 3^k`, so `f i ≤ 2`. (The key arithmetic fact, audited in S6b audit [PR #18555], is `q_k := ⌊(3/2)^k⌋ < (3/2)^k` strictly for every `k ≥ 1` — guaranteeing `n_k = q_k · 2^k + (2^k − 1) < 3^k`.)
2. *Lifting step*: `f : Fin s → ℕ` with each `f i ≤ 2` lifts to `g : Fin s → Fin 3`.
3. *Counting step*: let `n_j = |{i : g i = j}|` for `j ∈ {0, 1, 2}`. Then `n_0 + n_1 + n_2 = s` and `n_1 + 2^k · n_2 = n_k`.
4. *Omega step*: the resulting linear system over `ℕ` is infeasible — `omega` discharges. (Cases up to `n_2 ≤ q_k` exhibit a "miss by 1" calibration `n_0 = -1` characteristic of the witness construction.)

The S2 ACT shipped instance uses an alternative `native_decide` over `3^8 = 6561` tuples; the counting+omega route is the parametric design now established for `k ≥ 4` where `3^k · s` exceeds `native_decide`'s budget. S2b PREP supplies a counting+omega-style sibling proof for `k = 3` (smaller search space, same template).

**Upper-bound technique**: axiomatize the research-level results, register each as `axiomatized` in `meta.json`.

**Correctness-chain technique** (S6 PREP, S6c audit): for each `k`, bridge `WaringG2OQ01.IsSumOfPowers_k` (local) ↔ parent `IsSumOfPowers _ _ k` via `Iff.rfl` (or `⟨id, id⟩` defensively per S6c F6), then combine lower-bound theorem and upper-bound axiom to derive `waringG k = N` as a semantic certificate (not just `rfl`).

## Iteration history

| Iter | Researcher | Date | Mode | Deliverable | PR | Status |
|---:|---|---|---|---|---|---|
| S1 | researcher-? | 2026-05-12 | OBSERVE | Survey of `g(k)` history, two-tier architecture, Mathlib gap analysis | [#18152](https://github.com/rjwalters/lean-genius/pull/18152) | MERGED |
| S2 | researcher-3 | 2026-05-12 | ACT | `g(3)` lower bound via `native_decide` on `3^8 = 6561` tuples; new file `LagrangeFourSquaresWaringG2OQ01.lean` (118 LOC, 0 sorries, 0 axioms) | [#18176](https://github.com/rjwalters/lean-genius/pull/18176) | MERGED |
| S3 | researcher-10 | 2026-05-12 | PREP | `g(4)` lower bound design via counting+omega (369-line memo, full Lean sketch); identifies that `native_decide` over `3^18 ≈ 4·10^8` is infeasible | [#18314](https://github.com/rjwalters/lean-genius/pull/18314) | MERGED |
| S4 | researcher-? | 2026-05-12 | PREP | Upper-bound axiom inventory for `k = 3..6`: `waring_g3_upper`, `waring_g4_upper`, `waring_g5_upper`, `waring_g6_upper`; gap analysis for `bdd_nineteen_fourth_powers`, `chen_thirty_seven_fifth_powers` (218-line memo) | [#18348](https://github.com/rjwalters/lean-genius/pull/18348) | MERGED |
| S5 | researcher-4 | 2026-05-13 | PREP | `g(5)` lower bound design via counting+omega; witness `n = 223 = 6 · 32 + 31`; (509-line memo) | [#18463](https://github.com/rjwalters/lean-genius/pull/18463) | MERGED |
| S2b | researcher-? | 2026-05-13 | PREP | Counting+omega sibling for `g(3) ≥ 9`, unifying with S3/S5/S6b/S7 parametric template (186-line memo) | [#18483](https://github.com/rjwalters/lean-genius/pull/18483) | MERGED |
| S6 | researcher-12 | 2026-05-12 | PREP | `waringG k = N` correctness chain — semantic bridge `WaringG2OQ01.IsSumOfPowers_k ↔ IsSumOfPowers _ _ k` + `g_k_eq_N` theorems for `k = 3, 4, 5, 6` (543-line memo) | [#18406](https://github.com/rjwalters/lean-genius/pull/18406) | MERGED |
| S6b | researcher-10 | 2026-05-13 | PREP | `g(6)` lower bound design via counting+omega; witness `n = 703 = 11 · 64 + 63`; (682-line memo) | [#18547](https://github.com/rjwalters/lean-genius/pull/18547) | MERGED |
| S6b audit | researcher-? | 2026-05-13 | PREP | Audit of S6b PREP `{0,1,2}`-trick boundary arithmetic; proves `q_k < (3/2)^k` strictly for all `k ≥ 1`, hence `n_k < 3^k` universally (447-line memo) | [#18555](https://github.com/rjwalters/lean-genius/pull/18555) | MERGED |
| S6c audit | researcher-? | 2026-05-13 | PREP | Audit of S6 PREP §3 `waringG_2_correct` draft — 4 typing errors (F1–F4) + 1 axiom-integrity finding (F5: hidden `legendre_three_squares` dependency); proposes axiom-free `bound → lift → decide` alternative at `k = 2` (625-line memo) | [#18664](https://github.com/rjwalters/lean-genius/pull/18664) | MERGED |
| S7 | researcher-4 | 2026-05-13 | PREP | `g(7)` lower bound design via counting+omega; witness `n = 2175 = 16 · 128 + 127`; (828-line memo) | (orphan branch — see below) | DRAFT |
| S2b audit | researcher-4 | 2026-05-13 | PREP | Mathlib bearer audit for S2b PREP skeleton at lake-pinned SHA `2df2f01` (Mathlib v4.26.0); 9-row bearer table + sorry-free tactic draft (`Finset.sum_fiberwise` route, ~75 LOC) ready for S2b ACT paste | [#18895](https://github.com/rjwalters/lean-genius/pull/18895) | MERGED |
| S2b ACT | researcher-1 | 2026-05-13 | ACT | `g3_lower_counting : ¬ IsSumOfCubes 8 23` via counting + omega, sibling of S2 ACT's `native_decide`; eliminates `Lean.ofReduceBool` reflection axiom on the `g(3) ≥ 9` lower bound; new file `LagrangeFourSquaresWaringG2OQ01Counting.lean` (~141 LOC). | [#18928](https://github.com/rjwalters/lean-genius/pull/18928) | MERGED |
| S2b BUILD-VERIFY | researcher-12 | 2026-05-14 | ACT | 1-LOC `by simp` fix on `Finset.card_eq_sum_card_fiberwise` membership goal (v4.26.0 `Set β`-coercion regression); 7745 jobs clean. | [#19041](https://github.com/rjwalters/lean-genius/pull/19041) | **MERGED** 2026-05-15T23:38:13Z (`f31c503b89e2`) |
| S3 ACT | researcher-12 | 2026-05-14 | ACT | `g4_lower_counting : ¬ IsSumOfFourthPowers 18 79` via counting+omega — second verified instance of the parametric template (sibling of S2b ACT at `k = 4`). New file `LagrangeFourSquaresWaringG2OQ01CountingG4.lean` (155 LOC on origin/main, 0 sorries, 0 axioms, no `native_decide`). **First-iteration Docker build success, 7743 jobs clean.** Registered in `Proofs.lean`. | [#19129](https://github.com/rjwalters/lean-genius/pull/19129) | **MERGED** 2026-05-15T22:58:02Z (`c803ae7efe88`) |
| S7 PREP rescue | researcher-? | 2026-05-15 | PREP | Rescued the orphan-branch `g(7) ≥ 143` design memo (828 LOC) from `research/lagrange-four-squares-waring-g2-oq-01-s7-prep-g7-counting-omega-20260513-054453`. Opens S7 ACT as a routine port of the S3 ACT recipe at `k = 7`. | [#19177](https://github.com/rjwalters/lean-genius/pull/19177) | **MERGED** 2026-05-15T22:56:35Z (`b8c177c438e2`) |
| STATE-SYNC | researcher-3 | 2026-05-15 | STATE-SYNC | doc-only refresh after S3 ACT (#19129) merge + S2b BUILD-VERIFY (#19041) merge (partial — JSON-only, did not touch state.md) | [#19060](https://github.com/rjwalters/lean-genius/pull/19060) | **MERGED** 2026-05-15T23:34:19Z (`037b5b88d81`) |
| STATE-SYNC | researcher-3 | 2026-05-15 | STATE-SYNC | this PR — doc-only refresh after the 3-PR drain wave (#19129 + #19041 + #19177); refreshes `state.md` (Phase, Iteration, Current Focus, Iteration history, Open branches, Next Action, Attempt Counts, Open files, Honesty block, Future Iterations) + JSON (`currentState.{phase, since, iteration, focus, nextAction, attemptCounts.total}` + `knowledge.{progressSummary, builtItems, nextSteps}` + top-level `lastUpdate`) + new session memo. **No Lean changes.** | (this PR) | OPEN |

**Total PREP/ACT artifacts on origin/main**: 15 PRs merged (post-S2b ACT: 11 PREP/ACT/audit + 2 STATE-SYNC + S3 ACT + S2b BUILD-VERIFY + S7 PREP rescue) + this STATE-SYNC OPEN, ~5.5k lines of design documentation, 3 verified Lean files (S2 ACT, S2b ACT post-#19041, S3 ACT) on origin/main.

## Open branches

None for this slug as of 2026-05-16T01:43Z. The S7 PREP orphan branch `research/lagrange-four-squares-waring-g2-oq-01-s7-prep-g7-counting-omega-20260513-054453` was rescued and MERGED via PR [#19177](https://github.com/rjwalters/lean-genius/pull/19177) at 2026-05-15T22:56:35Z, retiring the orphan-branch entry that previously occupied this section.

## Blockers

None for the PREP layer — design coverage is saturated through `k = 7`.

**ACT-side risk**: Docker build of Lean ACTs requires a fresh Mathlib clone if the worktree's `proofs/.lake` symlink is broken (`feedback_researcher_lake_symlink_broken.md`); end-to-end build is ~45 minutes. Allocate session budget accordingly.

## Next Action

Five ACT iterations remain queued after the 3-PR drain wave (S3 ACT + S2b BUILD-VERIFY + S7 PREP all MERGED on 2026-05-15). Listed in recommended picker order (smallest scope / lowest build-risk first):

1. **S4 ACT** — register `axiom waring_g3_upper : ∀ n, ∃ f : Fin 9 → ℕ, (∑ i, (f i)^3) = n` (per S4 PREP [#18348](https://github.com/rjwalters/lean-genius/pull/18348)) + `theorem waringG_g3 : waringG 3 = 9` combining S2 ACT's `twenty_three_needs_nine_cubes` (lower, `native_decide` route) and S2b ACT's `g3_lower_counting` (lower, axiom-free counting+omega) with `waring_g3_upper` (axiomatized upper). **Smallest scope, ~50 LOC, axiom-only file, no fiberwise tactics, no `(by simp)` coercion surface — single Docker build expected first-iteration.**
2. **S5 ACT** — `g(5) ≥ 37` via counting+omega. Witness `223 = 6 · 32 + 31`. Expected size: ~150–180 LOC (case analysis on `n_2 ∈ {0..6}` has 7 branches vs. 5 for `k = 4`). **Routine port of S3 ACT recipe** — change `Fin 18 → Fin 36`, `79 → 223`, `16 → 32`, `81 → 243`, `^4 → ^5`. Paste `(by simp)` idiom from `Counting.lean:122` directly.
3. **S6b ACT** — `g(6) ≥ 73`. Witness `703 = 11 · 64 + 63`. Expected size: ~180–220 LOC (case analysis on `n_2 ∈ {0..10}`). Routine port of S3 ACT recipe at `k = 6`. Allocate 1-2 retry budget for v4.26.0 simp-set regressions on the larger case load.
4. **S6 ACT** — implement the correctness chain. Per S6c audit ([#18664](https://github.com/rjwalters/lean-genius/pull/18664), F5): **avoid the hidden `legendre_three_squares` dependency** by using the axiom-free `bound → lift → decide` route at `k = 2`. Expected size: ~60 LOC for the `k = 2` bridge + ~40 LOC per higher `k` once lower bounds and upper-bound axioms are in. Allocate 1-2 retry budget for `Iff.rfl` definitional-unfolding regressions.
5. **S7 ACT** — `g(7) ≥ 143`. Witness `2175 = 16 · 128 + 127`. **NEWLY UNBLOCKED** by PR [#19177](https://github.com/rjwalters/lean-genius/pull/19177) (S7 PREP rescue MERGED). Routine port of S3 ACT recipe at `k = 7`. Expected size: ~180–220 LOC (case analysis on `n_2 ∈ {0..16}` has 17 branches; ~3x S3 ACT's case-load). Allocate 2-3 retry budget; ~30 min Docker build.

Per the established pattern, all counting+omega ACTs share the same load-bearing case-analysis structure — a single ACT can refactor into a parametric `lemma waringG_lower_bound_template (k : ℕ) (s n_k : ℕ) (hk : ... ) : ¬ IsSumOfPowers _ s k n_k` that subsumes `k = 3..7` once written. The S2b ACT (`k = 3`) and S3 ACT (`k = 4`) confirm that the recipe ports mechanically; the (by simp) idiom from S2b BUILD-VERIFY is canonical.

## Attempt Counts

- Total iterations: 15 (3 ACTs MERGED + 1 BUILD-VERIFY MERGED + 11 PREPs MERGED + 2 STATE-SYNCs MERGED + this STATE-SYNC OPEN)
- ACT iterations merged: 3 (S2, S2b, S3) — all on origin/main, all build-verified
- ACT iterations in-flight: 0 — S2b BUILD-VERIFY (PR #19041) MERGED at 2026-05-15T23:38:13Z, retiring the only OPEN ACT
- ACT iterations this session: 0 (this STATE-SYNC is doc-only)
- PREP iterations merged: 11 (S1 OBSERVE, S2b PREP, S3 PREP, S4 PREP, S5 PREP, S6 PREP, S6b PREP, S6b audit, S6c audit, S2b bearer audit, **S7 PREP rescue [#19177](https://github.com/rjwalters/lean-genius/pull/19177) NEW**)
- PREP iterations drafted (no PR yet): 0 — S7 PREP rescued via #19177
- STATE-SYNC iterations merged: 2 ([#18866](https://github.com/rjwalters/lean-genius/pull/18866) on 2026-05-13 + [#19060](https://github.com/rjwalters/lean-genius/pull/19060) on 2026-05-15)
- STATE-SYNC iterations this session: 1 (this PR)
- Approaches: 2 — `native_decide` (S2 ACT only, adds `Lean.ofReduceBool` reflection axiom) and counting+omega (S2b ACT, S3 ACT, all 11 merged PREPs, future S4/S5/S6/S6b/S7 ACTs); S2b ACT + S3 ACT eliminate the reflection axiom on the `g(3) ≥ 9` and `g(4) ≥ 19` lower bounds respectively

## Open files

- `proofs/Proofs/LagrangeFourSquaresWaringG2OQ01.lean` — Lean deliverable for S2 (118 LOC, 2 theorems/lemmas, 0 sorries, 0 axioms via `native_decide` reflection axiom).
- `proofs/Proofs/LagrangeFourSquaresWaringG2OQ01Counting.lean` — Lean deliverable for S2b ACT + S2b BUILD-VERIFY (141 LOC on origin/main, 1 theorem `g3_lower_counting`, 0 sorries, 0 axioms, no `native_decide`). **BUILD-VERIFY PR [#19041](https://github.com/rjwalters/lean-genius/pull/19041) MERGED at 2026-05-15T23:38:13Z** — `(by simp)` v4.26.0 fix at line 122 is now on main.
- `proofs/Proofs/LagrangeFourSquaresWaringG2OQ01CountingG4.lean` — Lean deliverable for S3 ACT (155 LOC on origin/main, 1 theorem `g4_lower_counting`, 0 sorries, 0 axioms, no `native_decide`). Imports only Mathlib (no parent dependency). **PR [#19129](https://github.com/rjwalters/lean-genius/pull/19129) MERGED at 2026-05-15T22:58:02Z**, build-verified first iteration, 7743 jobs clean. Registered in `proofs/Proofs.lean`.
- `problem.md` — formal Lean signature targets, classification, Mathlib gap analysis, `g(k)` historical table.
- `knowledge.md` — `g(k)` historical table with citations, mod-arithmetic recipes, bibliographic references.
- `sessions/2026-05-12-s03-prep-g4-counting-omega.md` — S3 PREP (369 LOC).
- `sessions/2026-05-12-s04-prep-upper-bound-axioms.md` — S4 PREP (218 LOC).
- `sessions/2026-05-12-s06-prep-waringG-correctness-chain.md` — S6 PREP (543 LOC).
- `sessions/2026-05-13-s05-prep-g5-counting-omega.md` — S5 PREP (509 LOC).
- `sessions/2026-05-13-s2b-prep-g3-lower-counting-omega.md` — S2b PREP (186 LOC).
- `sessions/2026-05-13-s2b-prep-mathlib-bearer-audit.md` — S2b PREP follow-up bearer audit (~250 LOC).
- `sessions/2026-05-13-s6b-prep-audit-witness-arithmetic.md` — S6b audit (447 LOC).
- `sessions/2026-05-13-s6b-prep-g6-counting-omega.md` — S6b PREP (682 LOC).
- `sessions/2026-05-13-s6c-prep-audit-correctness-chain.md` — S6c audit (625 LOC).
- `sessions/2026-05-13-s7-prep-g7-counting-omega.md` — **S7 PREP (828 LOC) — NOW ON ORIGIN/MAIN via PR [#19177](https://github.com/rjwalters/lean-genius/pull/19177) (rescued from orphan branch).**
- `sessions/2026-05-14-s2b-act-build-verify-mem-univ-coercion-fix.md` — S2b ACT BUILD-VERIFY session memo (PR [#19041](https://github.com/rjwalters/lean-genius/pull/19041) MERGED).
- `sessions/2026-05-14-s3-act-g4-counting-omega.md` — S3 ACT session memo (PR [#19129](https://github.com/rjwalters/lean-genius/pull/19129) MERGED).
- `sessions/2026-05-14-state-sync-s2b-act-merge-build-verify.md` — STATE-SYNC #18866 / #19060 session memo (researcher-3, prior STATE-SYNC).
- `sessions/2026-05-15-state-sync-s3-act-merge-build-verify-s7-prep-rescue.md` — **this STATE-SYNC session memo**.

## Honesty block

This STATE-SYNC iteration is **doc-only**. It introduces 3 file edits (`state.md` refresh, JSON refresh, 1 new session memo `2026-05-15-state-sync-s3-act-merge-build-verify-s7-prep-rescue.md`) and **0 Lean code changes, 0 axiom-count changes, 0 sorry-count changes, 0 build attempts**.

The slug's three Lean deliverables are unchanged on origin/main:
- `LagrangeFourSquaresWaringG2OQ01.lean` (S2 ACT, 118 LOC)
- `LagrangeFourSquaresWaringG2OQ01Counting.lean` (S2b ACT post-#19041, 141 LOC)
- `LagrangeFourSquaresWaringG2OQ01CountingG4.lean` (S3 ACT, 155 LOC)

The bearer drift recheck in the session memo §3 is a **passive verification** (read lake-manifest, compare to last-known-good SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` v4.26.0, confirm no churn since 2026-05-14 v4.26.0 bump) rather than a re-run of the Mathlib bearer-audit script. The passive verification is sufficient because the v4.26.0 SHA pin has not changed since the last bearer audit (S2b PREP follow-up #18895 on 2026-05-13).

The `Iteration` increment 14 → 15 is justified per the slug's iteration-counting convention: STATE-SYNCs that introduce visibility for ≥1 merged-since-last-update ACT/PREP/BUILD-VERIFY count as iterations themselves. The three merges in the 22:56–23:38Z drain wave (#19129, #19041, #19177) are NOT separate iteration increments — they are landings of work whose iterations were already counted (iteration 13 for S3 ACT design / S3 ACT this PR, iteration ?? for S2b BUILD-VERIFY, iteration ?? for S7 PREP draft).

## Future Iterations

| Iter | Target | Predicate | Approach | Status |
|---:|---|---|---|---|
| S1 | OBSERVE survey | — | doc-only | **MERGED** #18152 |
| S2 | $g(3) \ge 9$ | $\neg \text{IsSumOfCubes } 8\ 23$ | `native_decide` $3^8$ | **MERGED** #18176 (0 sorries, 0 axioms) |
| S2b | $g(3) \ge 9$ (sibling) | $\neg \text{IsSumOfCubes } 8\ 23$ | counting + omega (template) | **PREP MERGED** #18483; **ACT MERGED** #18928; **BUILD-VERIFY MERGED** #19041 |
| S3 | $g(4) \ge 19$ | $\neg \text{IsSumOfFourthPowers } 18\ 79$ | counting + omega | **PREP MERGED** #18314; **ACT MERGED** #19129 (build-verified, 7743 jobs) |
| S4 | upper-bound axioms | `waring_g{3,4,5,6}_upper` | axiomatised | **PREP MERGED** #18348; ACT TODO |
| S5 | $g(5) \ge 37$ | $\neg \text{IsSumOfFifthPowers } 36\ 223$ | counting + omega | **PREP MERGED** #18463; ACT TODO |
| S6 | $\text{waringG } k = N$ | semantic correctness chain | bridge + `decide` per S6c | **PREP MERGED** #18406, audit #18664; ACT TODO |
| S6b | $g(6) \ge 73$ | $\neg \text{IsSumOfSixthPowers } 72\ 703$ | counting + omega | **PREP MERGED** #18547, audit #18555; ACT TODO |
| S7 | $g(7) \ge 143$ | $\neg \text{IsSumOfSeventhPowers } 142\ 2175$ | counting + omega | **PREP MERGED** #19177 (rescued); ACT TODO (newly unblocked) |
| (open) | $g(8) \ge 279$ | $\neg \text{IsSumOfEighthPowers } 278\ 6399$ | counting + omega | not yet designed |
| (open) | Hilbert–Waring existence | $\forall k \ge 1, \exists s, \forall n, \dots$ | Hardy–Littlewood (axiomatised) | not yet designed |
