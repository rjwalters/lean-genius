# Verdict — erdos85-drop.1

**Total: 17 / 44** (rubric `anvil-pub-v2`, advance threshold ≥ 35)

**Decision: `advance: false`** — below threshold *and* two blocking critical flags.

## Critical flags

- **`rendered_formal_statements_garbled`** (build/rendering class; §Preamble L9, visible on every page). The preamble line `\renewcommand{\texttt}[1]{\path{#1}}` makes `\path` print pandoc's escape backslashes literally, so the compiled PDF shows the abstract's headline claim as `f(48)\=\8 and f(49)\=\7`, Theorem B as `BinarySquareRegularExclusion\→\¬\Erdos85Question`, and the finite-drop hypothesis as `hno49\:\¬\C4FreeMinDegreeWitness\49\7`; 96 `\_` and 23 `\=`/`\→`/`\¬` artefacts occur in the extracted text. The statements as printed are not the statements the paper makes; a reader opening the PDF cannot take page 1 seriously. This is the paper analogue of the vision rubric's `mathtext_artifact_breaks_meaning`. The mechanical render gate passed because this defect is outside its detector set; the flag is set from a direct read of `pdftotext` output.
- **`numerical_inconsistency`** (§Cost to verify › cheaper route, L132 vs. Evidence-levels table L83 / Abstract L35 / §8 L313 / `refs/CENSUS.md`). The paper states "1,159 UNSAT verdicts needed 2,695 Kissat core-hours" for the residual whole-instance rows, while every other statement and the census receipt give "1,160 returned UNSAT from Kissat 4.0.4 and then CaDiCaL 3.0.1 under declared caps". For a paper whose Result A *is* a census count with an "empty open list", an unexplained off-by-one in the headline count is disqualifying until reconciled (one sentence naming the row without a timing record would suffice, if that is the cause).

## Dimension summary

| # | Dimension | Weight | Score |
|---|---|---|---|
| 1 | Rigor of method / argument | 6 | 4 |
| 2 | Evidence sufficiency | 6 | 4 |
| 3 | Clarity of contribution | 5 | 2 |
| 4 | Related-work positioning | 5 | 1 |
| 5 | Reproducibility | 5 | 2 |
| 6 | Figure & table quality | 4 | 1 |
| 7 | Prose & structural quality | 4 | 1 |
| 8 | Citation hygiene | 5 | 1 |
| 9 | Rhetorical economy | 4 | 1 |
| | **Total** | **44** | **17** |

Full justifications with verbatim quotes are in `scoring.md`; line-level items in `comments.md`; cross-section observations in `findings.md`.

## What is right

The scope discipline the BRIEF demands is almost entirely held: Result A is never called a theorem or "decided", nothing is claimed about Erdős 85 itself, no verdict or certificate is promoted, authorship is transcript-true, and every census count that *can* be checked against `refs/` checks. The evidence-levels table, the trust-boundary paragraph, the cost-to-verify section and §8 are the paper's best material and must survive the restructuring (the BRIEF says so too).

## Top revision priorities (in order)

1. **Fix the render.** Remove the `\path` override; typeset mathematics in math mode and Lean names in `\texttt` with a breaking package; give both tables captions, numbers, correct rule order and a page-fitting layout; strip the hand numbers from section titles and use `\label`/`\ref`; regenerate and grep the `pdftotext` output for `\\_` before the next review. Clears critical flag 1 and most of D6/D7.
2. **Reconcile 1,159 vs 1,160**, then make every remaining number traceable: add `sat49/H1_REPLAY_SPOT_16_BUDGET_PLAN_20260916.md`, `sat49/H1_V3_SOLVER_TIMING_20260916.md` and a certificate-bank statistics extract to `refs/`, or cut the figures that cannot be backed. Clears critical flag 2 and the D2 receipt gap.
3. **Write an Introduction and a Related Work section, and cite.** State the problem, define `f` (and Boza's `r`), state both results in plain mathematics, define the strata H1/H3/H5/H7 and assert their exhaustiveness, state the significance with the epistemic "to our knowledge" qualifier and the `r(42) ∈ {49, 50}` connection, and `\cite` all 11 `refs.bib` entries at their natural first mentions (Boza, Zhang–Chen–Cheng, Afzaly–McKay, Kissat, CaDiCaL, cube-and-conquer, DRAT-trim, LRAT, Lean 4, mathlib, Bloom's problem page). Lifts D3, D4, D8.
4. **Move the campaign-process sections to an appendix** (hand-numbered §§1–7, "Silence is not success", the room-protocol Methods bullets) and purge `room msg` / `outline v2.6x` / commit-hash citations from the body (one "Artifacts" appendix table may keep them). Delete the §8 "reconciled on 2026-09-28" meta-paragraph. Collapse the three restatements of the defect-operator reduction chain (§Theorem B, §0, §Results and evidence map) into one. Lifts D7, D9.
5. **Scope-word and tell cleanup.** Replace "axiom/conjecture" (L162) with "unproved hypothesis"; delete the *honest*/*candid*/*genuinely* label class (15 instances); restrict "168 edges" to the 48-vertex witness; state the `F`/`r` conversion when quoting Boza's 35/36 entries in the abstract.

## Notes

- Outstanding dependencies: none (no `[PENDING …]` markers).
- Evidence drift: no snapshot recorded for this version (pre-#857 draft); treated as clean.
- Venue overlay: none declared. External-artifact verification: none declared.
