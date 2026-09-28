# Verdict — erdos85-drop.4

**Total: 37 / 44** (rubric `anvil-pub-v2`, advance threshold ≥ 35)

**Decision: `advance: true`** — no critical flags. Iteration 4 of `max_iterations: 4` (the last under the cap); prior: v1 17/44 (2 critical), v2 32/44, v3 35/44 (review) then BLOCK from `erdos85-drop.3.audit/` (2 critical, 1 major).

## Critical flags

None.

**Re-evaluation of the v3 audit flags (required before the threshold check applies).** Each was checked in the v4 text, against `refs/` and, for Lean names, by `grep` of `proofs/Proofs/` (no build run):

- **C1 (H7 cell attribution) — resolved.** §4.2 "H7: cells and certificates" now states that the thirteen canonical representatives with $t\ge 1$ (distributed 1,2,3,3,2,1,1 over $t=1,\dots,7$; fourteen in all with the $t=0$ one) are excluded by packed LRAT certificates checked inside Lean by `native_decide`, names the thirteen `Erdos85OrderFortyNineSevenHighT{t}Rep{i}Certificate.lean` modules, the formula `orderFortyNineGeneratedH7SatCnf` (1,329,041 clauses), the bridge `sevenHighCanonicalRepresentativeExcluded_of_lrat` and the aggregate `orderFortyNineStratumExcluded_seven_of_t0`, and discloses the trust profile the auditor asked for in three sentences (`Lean.ofReduceBool`; compiled at the 2026-08-15 commits and not rebuilt in the 2026-09-27 cold audit; certificates on absolute local paths). The 7/14/21 split, the 43 classes, the 28 roots and the 2026-09-15 ledger are scoped to the $t=0$ cell, whose Lean interface is the uninstantiated `…_seven_of_emptyCubeEvidenceVectors` (19/15/7/2). Table 2 row $h=7$ and Table 4 (new row "H7, cells $t\ge 1$"; old row relabelled "H7, cell $t=0$") say the same. All thirteen module files exist in `proofs/Proofs/`, `orderFortyNineStratumExcluded_seven_of_t0 (hzero : SevenHighCanonicalRepresentativeExcluded 0 0) : OrderFortyNineStratumExcluded 7` is declared with the docstring the receipt quotes, `Erdos85OrderFortyNineSevenHighT1Rep0Certificate.lean` `include_str`s an absolute Stripe path and proves `sevenHighT1Rep0_check` by `native_decide`, and the census file states `[1, 1, 2, 3, 3, 2, 1, 1]`. Every statement matches `H7_POSITIVE_TRIPLE_CELLS_H5_CLOSURE_FORMULA_COUNTS_20260928.md` §1. Table 1's caption, §2's trust-root paragraph, §4.4 and §6 are re-weighed consistently ("H3 and the thirteen positive-triple H7 representatives carry checked LRAT proofs"). No certificate is described as part of the cold audit.
- **C2 (seven vs five formulas) — resolved.** §3.2 lists the two consumers with their input counts and the rule "their input counts must not be mixed or added"; §4.2 derives $4\times 56+3\times 56=392$ and $8+6=14$ per base formula and states that the five whole-cell formulas and the seven base formulas "are never added together"; Appendix B's exchange-rate paragraph now reads "replaces the five whole-cell H3/H5 formulas of the LRAT interface by seven base formulas (four H3 scouts and three H5 cells)". The phrase "seven whole-cell" does not occur. Matches the receipt §3 and `orderFortyNineSmallHigh_positiveCube_job_count : 4 * (7 * 8) + 3 * (7 * 8) = 392` in `Erdos85OrderFortyNineSmallHighCubeCover.lean`.
- **M1 (H5 closure outcome) — resolved.** §4.2 states the outcome, route, date and reviews (T0 1,665 → 13 empty negatives plus the counting contradiction, review 2037; T1 249 → none, review 2032; T2 13 → 12 plus the 44-core with 92 branches, reviews 2062/2063; outer review 2065 PASS 2026-09-10 with an independent checker and pinned hashes), its level (paper-and-computation under the established graph-reduction premises), what it did not include (no SAT run, no certificate replay, the 129 root cubes not consumed, the three Boolean-exclusion premises of `orderFortyNineStratumExcluded_five_of_booleanExclusions` undischarged — the theorem does take exactly three such hypotheses `h0 h1 h2`), and the corrected role of the census H5 rows. Table 2 and a separate Table 4 "H5" row agree; §7 names the four H5 ledger files and the 2026-09-28 receipt. The v3 sentence "closed by reviewed paper-and-computation covers with archived local proof receipts" is gone.

**BRIEF hard scope rules — held** (findings.md § Scope discipline): Result A is never a theorem, proof or decided value; nothing is claimed about Erdős Problem 85 itself; A-REG is "an unproved hypothesis with a stated rival, not a conjecture we endorse"; no solver verdict or certificate is promoted (the new certificate sentences describe `native_decide` checks with their `Lean.ofReduceBool` dependency, local paths and missing cold rebuild in the same paragraph); every new number traces to a receipt in `refs/`; authorship and contributions unchanged.

## Dimension summary

| # | Dimension | Weight | v2 | v3 | v4 |
|---|---|---|---|---|---|
| 1 | Rigor of method / argument | 6 | 5 | 5 | 6 |
| 2 | Evidence sufficiency | 6 | 4 | 5 | 5 |
| 3 | Clarity of contribution | 5 | 4 | 5 | 5 |
| 4 | Related-work positioning | 5 | 3 | 3 | 3 |
| 5 | Reproducibility | 5 | 3 | 4 | 4 |
| 6 | Figure & table quality | 4 | 3 | 3 | 3 |
| 7 | Prose & structural quality | 4 | 3 | 3 | 3 |
| 8 | Citation hygiene | 5 | 4 | 4 | 5 |
| 9 | Rhetorical economy | 4 | 3 | 3 | 3 |
| | **Total** | **44** | **32** | **35** | **37** |

Full justifications with verbatim quotes are in `scoring.md`; line-level items in `comments.md` (0 blocker, 0 major, 7 minor, 6 nit); cross-section verification in `findings.md`.

## What moved

Rigor +1 (both v3 rigor gaps closed and verified at source), citation hygiene +1 (the three bare pointers now have named receipts and reviews; the unnamed bound is attributed). Evidence, reproducibility, tables, prose and economy hold at their v3 scores: the v3 deductions in each were fixed, but each dimension has a named residual (findings.md, comments.md) — the private review chain behind H5 and H7 $t=0$, the local-path LRAT files the thirteen Lean modules need, the absence of any figure, a noun slip in §1 plus one ninety-word sentence, and a 303-word abstract with a three-page collaboration appendix.

## Audit-relevant notes (advance: true)

The paper advances above threshold; `paper-audit` should re-run on v4. Items the auditor will meet:

1. **§1 [L74] "one for each of its canonical cells with a positive triple"** — thirteen certificates are one per canonical *representative* (seven cells $t=1,\dots,7$); every other occurrence (§3.2, §4.2, Table 2, §6) says representatives. Minor noun slip; the count is right.
2. **§4.2 H7 $t=0$ [L176] "source enumeration with complement completion for eleven of the twelve $a=7$ roots"** — `H7_CLOSURE_20260915.md` applies the complement completion (2683) only "where required" (three of the eleven rows); the wording slightly homogenizes the route. Minor.
3. The thirteen H7 certificate modules and the H5/H7 $t=0$ reviews are receipted but not publicly reproducible (absolute Stripe paths; private room transcript). Disclosed in the text; the auditor should confirm the §7 ledger snapshots are on the branch of record.
4. Off-disk citation verification (`zhang2017polarity` values; Boza bounds $r(109)$, $r(155)$ in Appendix A) remains an author obligation, as the v3 audit recorded.

`related-work`: the D4 method-lineage gap stands (declined correctly again; web search off). A `paper-litsearch` run before publication should cover the methods behind the exact $r(s)$ values and prior SAT-with-certificate results; no citation is proposed here.

## Notes

- Outstanding dependencies: none (`anvil.lib.pending_marker` on `erdos85-drop.4/`: no `[PENDING …]` markers; `erdos85-drop.4.pending/_review.json` written clean). Terminal-state gate: passed — `ready = advance AND pending gate passed = true`.
- Evidence drift: `CLEAN` — `BRIEF.md` and `refs/**` unchanged since the v4 snapshot (`anvil.lib.evidence_drift check`); no advisory note.
- Numeric-consistency detector: 831 numbers, 0 arithmetic claims, 0 findings (`erdos85-drop.4.numeric/`); manual cross-check of every sum in the body found none (findings.md). Render gate: pass, 21 pages, 0 overfull, 0 placeholders (`_gate.json`).
- Compile (scratch copy, version dir untouched): `xelatex` + `bibtex` + `xelatex` ×3 to the `.aux` fixpoint, all exits 0; 0 errors; 0 undefined citations or references; 0 overfull; 7 underfull (max badness 6094); 22 cosmetic Menlo font-shape warnings (the `hyphenat` `htt` option); 21 pages (Appendix A p. 16, Appendix B p. 17, References p. 20); `pdftotext`: 0 `??`, 0 `[?]`; 12 bibliography entries.
- No venue overlay (`erdos85-drop/.anvil.json` absent); no `artifact_verify` block; corpus and subject-voice tiers inactive; `web_search: false`.
- Rubric transition: none — v3 was also scored against `anvil-pub-v2`; 35/44 → 37/44 is directly comparable.
- Score history: no orchestrator process drove this loop, so the per-iteration row `{iteration: 4, total: 37, threshold: 35, rubric_id: "anvil-pub-v2"}` is carried in this sidecar's `_progress.json` (as the v1–v3 reviews did) and `erdos85-drop.4/_progress.json` is left untouched. Termination reason on the score/verdict path: `THRESHOLD_MET` (also the iteration cap is reached).
