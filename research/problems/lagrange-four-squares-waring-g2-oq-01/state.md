# Current State

**Phase**: PREP-SATURATED (S1 → S7 PREP designed across `k = 3..7` lower-bound layer + upper-bound axiom inventory + waringG correctness chain; one ACT shipped, six ACTs queued)
**Since**: 2026-05-13 (S6c PREP audit merged at #18664; S7 PREP drafted but no PR opened — see "Open branches")
**Iteration**: 12 (S1 OBSERVE, S2 ACT, S2b PREP, S3 PREP, S4 PREP, S5 PREP, S6 PREP, S6b PREP, S6b audit, S6c audit, S2b bearer audit; S7 PREP draft)

## Current Focus

Lower-bound layer `g(k) ≥ N` design coverage is **saturated through k = 7** under the parametric "counting + omega" template established by S2b PREP / S3 PREP / S5 PREP / S6b PREP / S7 PREP draft. Upper-bound layer is **fully specified as an axiom inventory** (S4 PREP). The semantic correctness chain bridging local `IsSumOfPowers` predicates to `waringG k = N` is **scoped** (S6 PREP) and **audited** for typing/axiom errors (S6c PREP).

Six ACT iterations are queued for execution (see "Next Action"). No ACT has been shipped since S2 (2026-05-12), so the slug is in a PREP-saturated holding pattern awaiting Lean-level execution.

**Last shipped Lean deliverable** (S2 ACT, [PR #18176](https://github.com/rjwalters/lean-genius/pull/18176), 2026-05-12, researcher-3):
- `WaringG2OQ01.twenty_three_needs_nine_cubes : ¬ IsSumOfCubes 8 23` (0 sorries, 0 axioms, `native_decide` over `Fin 8 → Fin 3`)
- `WaringG2OQ01.IsSumOfCubes`, `representations23_empty`, witness example
- `proofs/Proofs/LagrangeFourSquaresWaringG2OQ01.lean` (118 lines, 2 theorems/lemmas)

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
| S2b audit | researcher-4 | 2026-05-13 | PREP | Mathlib bearer audit for S2b PREP skeleton at lake-pinned SHA `2df2f01` (Mathlib v4.26.0); 9-row bearer table + sorry-free tactic draft (`Finset.sum_fiberwise` route, ~75 LOC) ready for S2b ACT paste | (this PR) | PENDING |

**Total PREP/ACT artifacts on origin/main**: 10 PRs merged + 1 PENDING, ~3.6k lines of design documentation, 1 verified Lean file (118 LOC, 0 sorries, 0 axioms).

## Open branches

- `research/lagrange-four-squares-waring-g2-oq-01-s7-prep-g7-counting-omega-20260513-054453` — S7 PREP (researcher-4, commit `03bb13bee14`, 828 LOC). Branch pushed to origin 2026-05-13 ~05:48 UTC but no PR was opened. A subsequent researcher may open a PR for this branch (its scope is doc-only, orthogonal to all merged S1–S6c content).

## Blockers

None for the PREP layer — design coverage is saturated through `k = 7`.

**ACT-side risk**: Docker build of Lean ACTs requires a fresh Mathlib clone if the worktree's `proofs/.lake` symlink is broken (`feedback_researcher_lake_symlink_broken.md`); end-to-end build is ~45 minutes. Allocate session budget accordingly.

## Next Action

Six ACT iterations are queued; pick one. Listed in increasing complexity:

1. **S2b ACT** — re-prove `g(3) ≥ 9` via counting+omega (sibling to S2 ACT's `native_decide`). Smallest search space (`3^8 = 6561` is already verified by `native_decide`); the new proof eliminates the `native_decide` reflection axiom and unifies the proof template with `k = 4..7`. Expected size: ~80–100 LOC over S2 ACT's existing 118 LOC. **Recommended starting point** — lowest risk, validates the parametric template before applying at `k ≥ 4`.
2. **S3 ACT** — `g(4) ≥ 19` via counting+omega. Witness `79 = 4 · 16 + 15`. Expected size: ~120–150 LOC. Two `sorry` placeholders in the S3 PREP skeleton (`htotal` partition cardinality + `hsum` sum decomposition) need to be discharged — see S3 PREP §"Filling the two `sorry` placeholders" for two alternative Mathlib idioms.
3. **S4 ACT** — register `waring_g3_upper` axiom + bridge to `WaringG2OQ01.IsSumOfCubes`. Together with S2 ACT this gives `waringG 3 = 9` as a semantic statement, modulo the correctness chain (S6 ACT).
4. **S5 ACT** — `g(5) ≥ 37` via counting+omega. Witness `223 = 6 · 32 + 31`. Expected size: ~150–180 LOC (larger because the case analysis on `n_2 ∈ {0..6}` has 7 branches vs. 5 for `k = 4`).
5. **S6 ACT** — implement the correctness chain. Per S6c audit: avoid the hidden `legendre_three_squares` dependency by using the `bound → lift → decide` route at `k = 2`. Expected size: ~60 LOC for the `k = 2` bridge + ~40 LOC per higher `k` once lower bounds and upper-bound axioms are in.
6. **S6b ACT** — `g(6) ≥ 73`. Witness `703 = 11 · 64 + 63`. Expected size: ~180–220 LOC (case analysis on `n_2 ∈ {0..10}`).
7. **S7 ACT** — `g(7) ≥ 143`. Witness `2175 = 16 · 128 + 127`. (Blocked on S7 PREP PR opening or fresh design.)

Per the established pattern, all counting+omega ACTs share the same load-bearing case-analysis structure — a single ACT can refactor into a parametric `lemma waringG_lower_bound_template (k : ℕ) (s n_k : ℕ) (hk : ... ) : ¬ IsSumOfPowers _ s k n_k` that subsumes `k = 3..7` once written.

## Attempt Counts

- Total iterations: 12 (1 ACT shipped + 9 PREPs merged + 1 PREP draft pending PR + 1 PREP follow-up pending PR)
- ACT iterations shipped: 1 (S2)
- PREP iterations merged: 9 (S1, S2b, S3, S4, S5, S6, S6b, S6b audit, S6c audit)
- PREP iterations drafted (no PR yet): 1 (S7)
- PREP iterations pending PR (this session): 1 (S2b bearer audit)
- Approaches: 2 — `native_decide` (S2 ACT only) and counting+omega (all PREPs, future ACTs)

## Open files

- `proofs/Proofs/LagrangeFourSquaresWaringG2OQ01.lean` — Lean deliverable for S2 (118 LOC, 2 theorems/lemmas, 0 sorries, 0 axioms). Target for S2b ACT (parametric extension) and S3 ACT (new theorem appended).
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

S7 PREP session memo (`sessions/2026-05-13-s7-prep-g7-counting-omega.md`, 828 LOC) exists on the orphan branch `research/lagrange-four-squares-waring-g2-oq-01-s7-prep-g7-counting-omega-20260513-054453` but is not yet on origin/main.

## Honesty block

This STATE-SYNC iteration is doc-only — it updates `state.md` to reflect the actual progress of the slug as of 2026-05-13 ~12:30 UTC. It introduces **no edits** to `proofs/`, `problem.md`, `knowledge.md`, any session memo, `src/data/research/problems/lagrange-four-squares-waring-g2-oq-01.json`, the candidate pool, or any other slug. The Lean deliverable count and axiom count remain at the S2 ACT shipped values (2 theorems/lemmas, 0 sorries, 0 axioms in `LagrangeFourSquaresWaringG2OQ01.lean`).

The "PREP-SATURATED" Phase label reflects the empirical observation that 9 PREP iterations have shipped against 1 ACT iteration — the bottleneck is now Lean-level execution of the merged designs, not further design work. Future researchers selecting this slug via `claim-random` should prioritize one of the six queued ACTs (see "Next Action") rather than drafting an S8+ PREP unless a genuine new design dimension surfaces.

## Future Iterations

| Iter | Target | Predicate | Approach | Status |
|---:|---|---|---|---|
| S1 | OBSERVE survey | — | doc-only | **MERGED** #18152 |
| S2 | $g(3) \ge 9$ | $\neg \text{IsSumOfCubes } 8\ 23$ | `native_decide` $3^8$ | **MERGED** #18176 (0 sorries, 0 axioms) |
| S2b | $g(3) \ge 9$ (sibling) | $\neg \text{IsSumOfCubes } 8\ 23$ | counting + omega (template) | **PREP MERGED** #18483; ACT TODO |
| S3 | $g(4) \ge 19$ | $\neg \text{IsSumOfFourthPowers } 18\ 79$ | counting + omega | **PREP MERGED** #18314; ACT TODO |
| S4 | upper-bound axioms | `waring_g{3,4,5,6}_upper` | axiomatised | **PREP MERGED** #18348; ACT TODO |
| S5 | $g(5) \ge 37$ | $\neg \text{IsSumOfFifthPowers } 36\ 223$ | counting + omega | **PREP MERGED** #18463; ACT TODO |
| S6 | $\text{waringG } k = N$ | semantic correctness chain | bridge + `decide` per S6c | **PREP MERGED** #18406, audit #18664; ACT TODO |
| S6b | $g(6) \ge 73$ | $\neg \text{IsSumOfSixthPowers } 72\ 703$ | counting + omega | **PREP MERGED** #18547, audit #18555; ACT TODO |
| S7 | $g(7) \ge 143$ | $\neg \text{IsSumOfSeventhPowers } 142\ 2175$ | counting + omega | **PREP DRAFT** (orphan branch); ACT TODO |
| (open) | $g(8) \ge 279$ | $\neg \text{IsSumOfEighthPowers } 278\ 6399$ | counting + omega | not yet designed |
| (open) | Hilbert–Waring existence | $\forall k \ge 1, \exists s, \forall n, \dots$ | Hardy–Littlewood (axiomatised) | not yet designed |
