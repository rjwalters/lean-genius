# Verdict — erdos85-drop.3

**Total: 35 / 44** (rubric `anvil-pub-v2`, advance threshold ≥ 35)

**Decision: `advance: true`** — at threshold; **no critical flags**.

## Critical flags

None. The BRIEF's hard scope rules were re-checked on v3 and hold (findings.md § Scope discipline): Result A is never a theorem, proof or decided value; nothing is claimed about Erdős Problem 85 itself; A-REG is an unproved hypothesis with a stated rival; no verdict or certificate is promoted; every number in Sections 1–7 traces to a file in `refs/` (two residual pointer exceptions are minor, findings.md § Number traceability). The new §3.2 strata definitions and Table 2 match `refs/STRATA_AND_SMALL_ORDERS_20260928.md`; the §4.2 sketches match the inventories, the squeezes and `H7_CLOSURE_20260915.md` in every figure checked; the §7 receipt list names only files that exist.

## Dimension summary

| # | Dimension | Weight | v2 | v3 |
|---|---|---|---|---|
| 1 | Rigor of method / argument | 6 | 5 | 5 |
| 2 | Evidence sufficiency | 6 | 4 | 5 |
| 3 | Clarity of contribution | 5 | 4 | 5 |
| 4 | Related-work positioning | 5 | 3 | 3 |
| 5 | Reproducibility | 5 | 3 | 4 |
| 6 | Figure & table quality | 4 | 3 | 3 |
| 7 | Prose & structural quality | 4 | 3 | 3 |
| 8 | Citation hygiene | 5 | 4 | 4 |
| 9 | Rhetorical economy | 4 | 3 | 3 |
| | **Total** | **44** | **32** | **35** |

Full justifications with verbatim quotes are in `scoring.md`; line-level items in `comments.md`; cross-section observations in `findings.md`.

## What moved

The v2 rigor hole is closed: the strata are defined from the Lean source, the elementary degree-7/8 derivation is correct, and the case split is stated as proved exhaustive in Lean with the composing theorem displayed. The traceability sentence is now essentially true (a receipt-by-receipt list in §7 with the repository URL), the projection rates are sourced, the 1,161 vs 1,158 gap is explained, the reserved verb is gone, the census scale is in §1, the jargon is gone, the abstract and §6 no longer restate §4, and the H3 and H7 closures are real sketches with their Lean and non-Lean pieces separated.

## Audit-relevant notes (advance: true)

The paper advances at exactly the threshold with three `major` findings that the reviser could not fix without a receipt the authors have not banked. `paper-audit` should treat them as the open items to verify against the branch of record:

1. **H7 cells $t=1,\dots,7$** (§4.2 H7). The closure sketch works from the $t=0$ profile (7/14/21); the paper attributes the reduction to "premises the closure ledger cites as established" without naming what excludes $t\ge 1$, and `refs/` contains no such statement (`Q7_H5_H7_SQUEEZE` calls H7/T0 "the remaining operator-designated sector"). The auditor should locate the premise reviews (1573/1574/2091 per the ledger) or the Lean statement and confirm the T0 reduction; if it cannot, this becomes an audit critical flag (missing evidence for the H7 exclusion).
2. **H5 closure outcome** (§4.2 H3/H5). The paper asserts closure "with archived local proof receipts" but never states which jobs ran, what they returned or who checked them, and no file in `refs/` documents the event (the 2026-09-10 inventory lists 129 open root cubes; `CENSUS.md` says closed by other routes). The auditor should find the H5 closure receipt on the branch of record and confirm the 129 root cubes (or the 406-job grid) are refuted with checked proofs.
3. **Seven vs five H3/H5 formulas** (§3.2, §4.2). "the seven whole-cell H3/H5 formulas" (the cube route's seven base CNFs: four H3 scouts + three H5 cells, per Appendix B) is never reconciled in the body with the two H3 + three H5 representative formulas of the LRAT consumer; both counts are traceable, the paper just does not connect them. One clause in a later revision.

Minor items the auditor will meet: the unnamed "$C_4$-free edge bound" behind $h\le 9$ (the standard bound does not give it; the Lean theorem does); the abstract's "it selects $r(42)=49$" (keep the Ramsey-side statement at the evidence level); "about 1,400 solver inputs" (1,412 preparations for 1,161 rows); the process note "left to a literature pass with search enabled" in §2; the C7 chain omitted from the H7 route list; the `v2cnf` hash and §5.3 census orders tracing to files not named in §7; Table 2's mid-identifier line breaks.

`related-work`: the D4 method-lineage gap stands (declined correctly; web search off). A `paper-litsearch` run before publication should cover the methods behind the exact $r(s)$ values and prior SAT-with-certificate results in extremal combinatorics; no citation is proposed here.

## Notes

- Outstanding dependencies: none (no `[PENDING …]` markers; `erdos85-drop.3.pending/_review.json` clean).
- Evidence drift: `CLEAN` — `BRIEF.md` and `refs/**` unchanged since the v3 snapshot (no advisory note).
- Numeric-consistency detector: 764 numbers, 0 arithmetic claims, 0 findings (`erdos85-drop.3.numeric/`); manual cross-check of every sum in the body found none. Render gate: pass, 18 pages, 0 overfull, 0 placeholders (`_gate.json`).
- No venue overlay (`erdos85-drop/.anvil.json` absent); no `artifact_verify` block; corpus and subject-voice tiers inactive.
- Rubric transition: none — v2 was also scored against `anvil-pub-v2`; 32/44 → 35/44 is directly comparable.
- Iteration 3 of `max_iterations: 4`; one revise pass remains if the authors bank the three receipts above.
