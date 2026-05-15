# Current State

**Phase**: ACT-in-flight + PREP-SATURATED (S2 ACT + S2b ACT + S3 ACT shipped; S1 → S7 PREP designed across `k = 3..7` lower-bound layer + upper-bound axiom inventory + waringG correctness chain; four ACTs still queued after S3)
**Since**: 2026-05-14 (S3 ACT build-verified — `g(4) ≥ 19` counting+omega proof, 7743 jobs clean, first-iteration success)
**Iteration**: 14 (S1 OBSERVE, S2 ACT, S2b PREP, S3 PREP, S4 PREP, S5 PREP, S6 PREP, S6b PREP, S6b audit, S6c audit, S2b bearer audit, S2b ACT, S2b BUILD-VERIFY, S3 ACT)

## Current Focus

Lower-bound layer `g(k) ≥ N` design coverage is **saturated through k = 7** under the parametric "counting + omega" template established by S2b PREP / S3 PREP / S5 PREP / S6b PREP / S7 PREP draft. Upper-bound layer is **fully specified as an axiom inventory** (S4 PREP). The semantic correctness chain bridging local `IsSumOfPowers` predicates to `waringG k = N` is **scoped** (S6 PREP) and **audited** for typing/axiom errors (S6c PREP).

S2b ACT (PR #18928) shipped the audited counting+omega tactic block as `LagrangeFourSquaresWaringG2OQ01Counting.lean`, eliminating the `Lean.ofReduceBool` reflection axiom on the `g(3) ≥ 9` lower bound. S2b BUILD-VERIFY (PR #19041, in-flight) applied a 1-LOC `by simp` fix for the v4.26.0 `Set β`-coercion regression on `Finset.card_eq_sum_card_fiberwise`; verified 7745 jobs clean.

**S3 ACT (this PR)** ports the S2b ACT recipe line-for-line to `k = 4`, shipping `WaringG2OQ01.CountingG4.g4_lower_counting : ¬ IsSumOfFourthPowers 18 79` in new sibling file `LagrangeFourSquaresWaringG2OQ01CountingG4.lean` (~141 LOC, 0 sorries, 0 axioms, no `native_decide`). **Build-verified on first iteration** (7743 jobs clean, ~10 min Docker, no retries — the S2b BUILD-VERIFY `by simp` fix was incorporated up front). After S3 ACT, four ACT iterations (S4, S5, S6, S6b — plus optional S7 once its PREP lands) remain queued.

**Last shipped Lean deliverable** (S3 ACT, this PR, 2026-05-14, researcher-12):
- `WaringG2OQ01.CountingG4.g4_lower_counting : ¬ IsSumOfFourthPowers 18 79` (0 sorries, 0 axioms, counting+omega, no `native_decide`)
- `WaringG2OQ01.CountingG4.IsSumOfFourthPowers` (local definition mirroring `IsSumOfCubes`)
- `proofs/Proofs/LagrangeFourSquaresWaringG2OQ01CountingG4.lean` (~141 lines, new sibling file)
- Registered in `proofs/Proofs.lean` (line ~2466)

**Prior shipped Lean deliverables**:
- S2b ACT (PR #18928, 2026-05-13): `WaringG2OQ01.Counting.g3_lower_counting : ¬ IsSumOfCubes 8 23` via counting+omega (sibling of S2 ACT's `native_decide`); `proofs/Proofs/LagrangeFourSquaresWaringG2OQ01Counting.lean` (~141 lines).
- S2 ACT (PR #18176, 2026-05-12): `WaringG2OQ01.twenty_three_needs_nine_cubes : ¬ IsSumOfCubes 8 23` via `native_decide`; `proofs/Proofs/LagrangeFourSquaresWaringG2OQ01.lean` (118 lines).

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
| S2b BUILD-VERIFY | researcher-12 | 2026-05-14 | ACT | 1-LOC `by simp` fix on `Finset.card_eq_sum_card_fiberwise` membership goal (v4.26.0 `Set β`-coercion regression); 7745 jobs clean. | [#19041](https://github.com/rjwalters/lean-genius/pull/19041) | OPEN |
| S3 ACT | researcher-12 | 2026-05-14 | ACT | `g4_lower_counting : ¬ IsSumOfFourthPowers 18 79` via counting+omega — second verified instance of the parametric template (sibling of S2b ACT at `k = 4`). New file `LagrangeFourSquaresWaringG2OQ01CountingG4.lean` (~141 LOC, 0 sorries, 0 axioms, no `native_decide`). **First-iteration Docker build success, 7743 jobs clean.** Registered in `Proofs.lean`. | (this PR) | OPEN |

**Total PREP/ACT artifacts on origin/main**: 12 PRs merged (post-S2b ACT) + 2 OPEN ACTs (S2b BUILD-VERIFY, S3 ACT), ~3.6k lines of design documentation, 2 verified Lean files (S2 ACT, S2b ACT) + 1 newly-verified Lean file (S3 ACT, this PR).

## Open branches

- `research/lagrange-four-squares-waring-g2-oq-01-s7-prep-g7-counting-omega-20260513-054453` — S7 PREP (researcher-4, commit `03bb13bee14`, 828 LOC). Branch pushed to origin 2026-05-13 ~05:48 UTC but no PR was opened. A subsequent researcher may open a PR for this branch (its scope is doc-only, orthogonal to all merged S1–S6c content).

## Blockers

None for the PREP layer — design coverage is saturated through `k = 7`.

**ACT-side risk**: Docker build of Lean ACTs requires a fresh Mathlib clone if the worktree's `proofs/.lake` symlink is broken (`feedback_researcher_lake_symlink_broken.md`); end-to-end build is ~45 minutes. Allocate session budget accordingly.

## Next Action

Four ACT iterations remain queued after S3 ACT (this PR). Listed in increasing complexity:

1. **S4 ACT** — register `waring_g3_upper` axiom + bridge to `WaringG2OQ01.IsSumOfCubes`. Together with S2 / S2b ACT this gives `waringG 3 = 9` as a semantic statement, modulo the correctness chain (S6 ACT). **Smallest scope.**
2. **S5 ACT** — `g(5) ≥ 37` via counting+omega. Witness `223 = 6 · 32 + 31`. Expected size: ~150–180 LOC (case analysis on `n_2 ∈ {0..6}` has 7 branches vs. 5 for `k = 4`). **Routine port of S3 ACT recipe** — change `Fin 18 → Fin 36`, `79 → 223`, `16 → 32`, `81 → 243`, `^4 → ^5`.
3. **S6 ACT** — implement the correctness chain. Per S6c audit: avoid the hidden `legendre_three_squares` dependency by using the `bound → lift → decide` route at `k = 2`. Expected size: ~60 LOC for the `k = 2` bridge + ~40 LOC per higher `k` once lower bounds and upper-bound axioms are in.
4. **S6b ACT** — `g(6) ≥ 73`. Witness `703 = 11 · 64 + 63`. Expected size: ~180–220 LOC (case analysis on `n_2 ∈ {0..10}`).
5. **S7 ACT** — `g(7) ≥ 143`. Witness `2175 = 16 · 128 + 127`. (Blocked on S7 PREP PR opening or fresh design.)

Per the established pattern, all counting+omega ACTs share the same load-bearing case-analysis structure — a single ACT can refactor into a parametric `lemma waringG_lower_bound_template (k : ℕ) (s n_k : ℕ) (hk : ... ) : ¬ IsSumOfPowers _ s k n_k` that subsumes `k = 3..7` once written. The S3 ACT (`k = 4`) confirms that the S2b ACT recipe ports mechanically.

## Attempt Counts

- Total iterations: 14 (2 ACTs merged + 1 BUILD-VERIFY in-flight + 1 ACT this PR + 9 PREPs merged + 1 PREP draft pending PR)
- ACT iterations merged: 2 (S2, S2b)
- ACT iterations in-flight: 1 (S2b BUILD-VERIFY)
- ACT iterations this session: 1 (S3 ACT, this PR — build-verified)
- PREP iterations merged: 10 (S1, S2b, S3, S4, S5, S6, S6b, S6b audit, S6c audit, S2b bearer audit)
- PREP iterations drafted (no PR yet): 1 (S7)
- Approaches: 2 — `native_decide` (S2 ACT only) and counting+omega (S2b ACT, S3 ACT, all PREPs, future ACTs); S2b ACT + S3 ACT eliminate the `Lean.ofReduceBool` reflection axiom on the `g(3) ≥ 9` and `g(4) ≥ 19` lower bounds respectively

## Open files

- `proofs/Proofs/LagrangeFourSquaresWaringG2OQ01.lean` — Lean deliverable for S2 (118 LOC, 2 theorems/lemmas, 0 sorries, 0 axioms via `native_decide` reflection axiom).
- `proofs/Proofs/LagrangeFourSquaresWaringG2OQ01Counting.lean` — Lean deliverable for S2b ACT (~141 LOC, 1 theorem `g3_lower_counting`, 0 sorries, 0 axioms, no `native_decide`). BUILD-VERIFY PR #19041 in-flight (`by simp` v4.26.0 fix).
- `proofs/Proofs/LagrangeFourSquaresWaringG2OQ01CountingG4.lean` — **Lean deliverable for S3 ACT (this PR; ~141 LOC, 1 theorem `g4_lower_counting`, 0 sorries, 0 axioms, no `native_decide`).** Imports only Mathlib (no parent dependency, sidesteps S2b BUILD-VERIFY in-flight). Build-verified first iteration, 7743 jobs clean. Registered in `proofs/Proofs.lean`.
- `problem.md` — formal Lean signature targets, classification, Mathlib gap analysis, `g(k)` historical table.
- `knowledge.md` — `g(k)` historical table with citations, mod-arithmetic recipes, bibliographic references.
- `sessions/2026-05-12-s03-prep-g4-counting-omega.md` — S3 PREP (369 LOC).
- `sessions/2026-05-12-s04-prep-upper-bound-axioms.md` — S4 PREP (218 LOC).
- `sessions/2026-05-12-s06-prep-waringG-correctness-chain.md` — S6 PREP (543 LOC).
- `sessions/2026-05-13-s05-prep-g5-counting-omega.md` — S5 PREP (509 LOC).
- `sessions/2026-05-13-s2b-prep-g3-lower-counting-omega.md` — S2b PREP (186 LOC).
- `sessions/2026-05-13-s2b-prep-mathlib-bearer-audit.md` — S2b PREP follow-up bearer audit (this iteration; ~250 LOC).
- `sessions/2026-05-13-s6b-prep-audit-witness-arithmetic.md` — S6b audit (447 LOC).
- `sessions/2026-05-13-s6b-prep-g6-counting-omega.md` — S6b PREP (682 LOC).
- `sessions/2026-05-13-s6c-prep-audit-correctness-chain.md` — S6c audit (625 LOC).
- `sessions/2026-05-14-s2b-act-build-verify-mem-univ-coercion-fix.md` — S2b ACT BUILD-VERIFY (PR #19041, in-flight).
- `sessions/2026-05-14-s3-act-g4-counting-omega.md` — **S3 ACT session memo (this PR)**.

S7 PREP session memo (`sessions/2026-05-13-s7-prep-g7-counting-omega.md`, 828 LOC) exists on the orphan branch `research/lagrange-four-squares-waring-g2-oq-01-s7-prep-g7-counting-omega-20260513-054453` but is not yet on origin/main.

## Honesty block

This S3 ACT iteration ships **one new Lean file** (`LagrangeFourSquaresWaringG2OQ01CountingG4.lean`, ~141 LOC, 1 theorem, 0 sorries, 0 axioms), registers it in `Proofs.lean`, and adds one session memo (`2026-05-14-s3-act-g4-counting-omega.md`). The state.md updates above re-rank the queued ACTs (S3 → done) and remove the BUILD-PENDING qualifier on S2b ACT (delegated to PR #19041's in-flight `by simp` fix).

The S3 ACT proof is a **routine port** of S2b ACT's recipe to `k = 4`. No new Mathlib bearers, no new tactic primitives, no new mathematical insight — the value is purely in **double-validating the parametric template** (now verified at `k ∈ {3, 4}`) and shipping the second instance of the `g(k) ≥ N` lower-bound recipe. S5/S6b/S7 ACTs are now expected to ship as 30-minute mechanical ports (change four constants, run Docker, push).

## Future Iterations

| Iter | Target | Predicate | Approach | Status |
|---:|---|---|---|---|
| S1 | OBSERVE survey | — | doc-only | **MERGED** #18152 |
| S2 | $g(3) \ge 9$ | $\neg \text{IsSumOfCubes } 8\ 23$ | `native_decide` $3^8$ | **MERGED** #18176 (0 sorries, 0 axioms) |
| S2b | $g(3) \ge 9$ (sibling) | $\neg \text{IsSumOfCubes } 8\ 23$ | counting + omega (template) | **PREP MERGED** #18483; **ACT MERGED** #18928; **BUILD-VERIFY OPEN** #19041 |
| S3 | $g(4) \ge 19$ | $\neg \text{IsSumOfFourthPowers } 18\ 79$ | counting + omega | **PREP MERGED** #18314; **ACT THIS PR** (build-verified) |
| S4 | upper-bound axioms | `waring_g{3,4,5,6}_upper` | axiomatised | **PREP MERGED** #18348; ACT TODO |
| S5 | $g(5) \ge 37$ | $\neg \text{IsSumOfFifthPowers } 36\ 223$ | counting + omega | **PREP MERGED** #18463; ACT TODO |
| S6 | $\text{waringG } k = N$ | semantic correctness chain | bridge + `decide` per S6c | **PREP MERGED** #18406, audit #18664; ACT TODO |
| S6b | $g(6) \ge 73$ | $\neg \text{IsSumOfSixthPowers } 72\ 703$ | counting + omega | **PREP MERGED** #18547, audit #18555; ACT TODO |
| S7 | $g(7) \ge 143$ | $\neg \text{IsSumOfSeventhPowers } 142\ 2175$ | counting + omega | **PREP DRAFT** (orphan branch); ACT TODO |
| (open) | $g(8) \ge 279$ | $\neg \text{IsSumOfEighthPowers } 278\ 6399$ | counting + omega | not yet designed |
| (open) | Hilbert–Waring existence | $\forall k \ge 1, \exists s, \forall n, \dots$ | Hardy–Littlewood (axiomatised) | not yet designed |
