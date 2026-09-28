# Verdict — erdos85-drop.2

**Total: 32 / 44** (rubric `anvil-pub-v2`, advance threshold ≥ 35)

**Decision: `advance: false`** — below threshold by 3 points; **no critical flags**.

## Critical flags

None. Both v1 flags are verified resolved in the rendered PDF:

- `rendered_formal_statements_garbled` — `pdftotext main.pdf` has 0 `\_`, `\=`, `\→`, `\¬` or `??` artefacts; every formal statement and Lean identifier renders as written.
- `numerical_inconsistency` (1,159 vs 1,160) — every occurrence now reads 1,160 + 1 = 1,161; Table 3 sums to 1,160; the corrected timing figures match `refs/CENSUS_TIMING_20260928.md`.

The BRIEF's hard scope rules were re-checked on v2 and hold (findings.md § Scope discipline). Every number traces to a file in `refs/` (findings.md § Number traceability). The §1 $r(s)\leftrightarrow F(N)$ conversion agrees with the 2026-09-28 correction in `refs/FIRST_DROP_LITERATURE_CHECK.md`.

## Dimension summary

| # | Dimension | Weight | v1 | v2 |
|---|---|---|---|---|
| 1 | Rigor of method / argument | 6 | 4 | 5 |
| 2 | Evidence sufficiency | 6 | 4 | 4 |
| 3 | Clarity of contribution | 5 | 2 | 4 |
| 4 | Related-work positioning | 5 | 1 | 3 |
| 5 | Reproducibility | 5 | 2 | 3 |
| 6 | Figure & table quality | 4 | 1 | 3 |
| 7 | Prose & structural quality | 4 | 1 | 3 |
| 8 | Citation hygiene | 5 | 1 | 4 |
| 9 | Rhetorical economy | 4 | 1 | 3 |
| | **Total** | **44** | **17** | **32** |

Full justifications with verbatim quotes are in `scoring.md`; line-level items in `comments.md`; cross-section observations in `findings.md`.

## What is right

The paper is now a results paper: the problem, both results, the significance with its epistemic qualifier and the Boza $r(42)$ connection are all in the abstract and introduction; the render is clean; all 11 references are cited; the four tables are captioned and fit; the process essays are in an appendix; the AI-tell adjective class is gone; and every count and cost figure reconciles with a receipt in `refs/`. The evidence-level table, the trust-boundary discussion, the cost-to-verify section and the interpretation section survive in substance as the BRIEF requires.

## Top revision priorities (in order)

1. **Make the traceability sentence true and the projection checkable (D2, D8).** §1 claims every number traces to a receipt *named in Section 6*; it does not. Name the replay budget plan, the v3 timing readback, the fleet-cost JSON, the certificate-bank statistics and the 2026-09-28 timing/projection worksheet in the Artifacts or Data-availability paragraph, and give §4.6 one sentence saying where the 5.5 GB/h and 0.5 MB/s rates were measured (12,102 bank rows binned by solve time; the replay pilot). Explain in one clause why 1,161 residual roots give only 1,158 gap slots.
2. **Say what the strata are (D1).** Add to `refs/` a two-sentence statement of the Lean normalization (what a "high" vertex is; why $h\in\{1,3,5,7\}$ exhausts the candidates) and state it in §3.2. This is the one rigor gap a program-committee reader will not accept on trust.
3. **Sketch the three non-H1 closures and thicken related work (D2, D4).** One paragraph each on what an H3/H5 cover formula and an H7 singleton-capacity argument are (or an appendix table from `refs/H7_CLOSURE_20260915.md` with the 28 roots and review chains). In §2, say how the decided entries of Boza's table were obtained and where a two-solver SAT census sits among prior SAT-based extremal computations; run `paper-litsearch` for the method lineage (no citations invented here).
4. **Cut the restatement (D9, D7).** Trim the abstract to results plus qualifier; stop §6 re-narrating §4.2; state the trust-boundary sentence once; define or replace the room vocabulary ("cold-green", "jaw", "socket", "monoliths"); widen Table 3's Cap column. Surface the census scale (about 5,700 solver core-hours over about 1,400 instances) in §1 where the BRIEF says the surprise lives.
5. **Wording and receipts (D3, D8).** Replace the reserved verb in "the first strict drop of $f$ decided" with "settled/established at the level of computational evidence"; name the Lean statements behind "the exact Lean results at orders 15 and 16"; cite a receipt for the non-isomorphism check; align "two to four weeks" and "65 to 130 GB" with the receipts' printed ranges.

## Notes

- Outstanding dependencies: none (no `[PENDING …]` markers; `erdos85-drop.2.pending/_review.json` clean).
- **Evidence drift (advisory only):** `anvil.lib.evidence_drift check` reports `EVIDENCE-DRIFT` — `refs/**` changed after the v2 revise snapshot (`CENSUS_TIMING_20260928.md` added; correction appended to `FIRST_DROP_LITERATURE_CHECK.md`). This review re-weighed both against v2: they supply the receipts the changelog flagged as missing and confirm the §1 conversion and the omission of the 35/36 remark. Advisory only — it does not change `advance`, any dimension score, or the terminal transition.
- Numeric-consistency detector: 604 numbers, 0 arithmetic claims, 0 findings (`erdos85-drop.2.numeric/`). Render gate: pass, 16 pages, 0 overfull, 0 placeholders (`_gate.json`).
- No venue overlay (`erdos85-drop/.anvil.json` absent); no `artifact_verify` block; corpus and subject-voice tiers inactive.
- Rubric transition: none — v1 was also scored against `anvil-pub-v2`; 17/44 → 32/44 is directly comparable.
