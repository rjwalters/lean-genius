# Changelog — erdos85-drop.3 → erdos85-drop.4

Revised against every critic sibling at version 3: `erdos85-drop.3.review/` (generic rubric
`anvil-pub-v2`, 35/44, `advance: true`, 0 critical, 3 major, 10 minor, 5 nit),
`erdos85-drop.3.audit/` (tool evidence, verdict BLOCK: 2 critical flags C1 and C2, 1 major M1,
5 non-critical notes m1–m5, build note, citation notes), `erdos85-drop.3.numeric/` (0 findings) and
`erdos85-drop.3.pending/` (0 findings, no `[PENDING]` markers). No venue overlay, litsearch,
vision or corpus-audit sibling exists at version 3. The corpus tier is inactive (no `corpus:`
key in `BRIEF.md`), so no `provenance.md` is carried. This is iteration 4 of `max_iterations: 4`.

The verdict pre-check: the reviewer advanced v3 at threshold, but `.audit/` carries two
critical flags, so revision is required (paper-revise step 4, audit exception).

Build: `xelatex` + `bibtex` + `xelatex` ×2 in `erdos85-drop.4/` (log in `compile-log.txt`,
class file copied from `erdos85-drop.3/`; the document uses `fontspec`, so `xelatex` is kept):
0 LaTeX errors, 0 undefined citations or references, 0 BibTeX warnings, **0 overfull boxes,
7 underfull lines, none at badness 10000** (v3: 23 underfull, six at 10000), 21 pages
(v3: 18; Appendix A starts on page 16, References on page 20, so the body is 15 pages against
the BRIEF's 12–18-page target plus appendices). `pdftotext main.pdf`: 0 `??`, 0 `[?]`.
`python3 scope_lint.py erdos85-drop.4/main.tex`: **PASS** (66 numbers checked, 53 Lean names
checked; v3 reported the tabularx widths, outline labels and bare transcript pointers as
untraced — see the "scope_lint" row below). No solver, AWS, Docker, Lean build or git command
was run; Lean names were verified by `grep` against `proofs/Proofs/` in the
`claude-e85-wrapup` worktree only.

Receipts used for the new statements (all in `erdos85-drop/refs/`, none modified):
`H7_POSITIVE_TRIPLE_CELLS_H5_CLOSURE_FORMULA_COUNTS_20260928.md` (§1–§3),
`H5_CLOSURE_LEDGER_README_20260910.md`, `H5_CLOSURE_REVIEWED_RESULT_20260910.md`,
`h5-closure-review2065.json`, `h5-closure-reviewer-REVIEW2065.json`, `H7_CLOSURE_20260915.md`
(C7 row for `cube_F7_t14`), `STRATA_AND_SMALL_ORDERS_20260928.md`, `CENSUS_TIMING_20260928.md`
(1,412 = 1,132 + 261 + 17 + 2 preparations for the 1,161 rows), `PAUSE_HANDOFF_20260927.md`
(`v2cnf` hash), `Q7_H1_H3_SQUEEZE_20260910.md` ("incidence profiles"),
`PHASE_B_H5_H7_INVENTORY_20260910.md` (58/15/43 per H5 cell). New numbers introduced and their
receipts: 1,329,041 clauses per H7 representative formula, the 1,1,2,3,3,2,1,1 distribution,
the 2026-08-15 manifests, reviews 1573/1574/2091 (the 2026-09-28 receipt §1); reviews
2037/2032/2062/2063/2065, 1,665 → 13, 249 → 0, 13 → 12 + the 44-core with 92 branches, 49
masks per cell (receipt §2 and the H5 ledger files); 4 × 56 + 3 × 56 = 392, 8 + 6 = 14
(receipt §3). Lean names newly cited, all grep-verified as declarations or modules:
`sevenHighCanonicalGraphCover_all`, `orderFortyNineStratumExcluded_seven_of_t0`,
`sevenHighCanonicalRepresentativeExcluded_of_lrat`, `orderFortyNineGeneratedH7SatCnf`,
`orderFortyNineStratumExcluded_five_of_booleanExclusions`,
`orderFortyNineGeneratedThreeHighDistOne{B1,C1,C2}ScoutCnf`,
`orderFortyNineGeneratedThreeHighDistTwoScoutCnf`, `orderFortyNineGeneratedVariableHighSatCnf`,
`orderFortyNineFiveHighT{0,1,2}Masks`, modules `Erdos85OrderFortyNineSevenHighCanonicalCensus.lean`,
`Erdos85OrderFortyNineSevenHighT1Rep0Certificate.lean` … `…T7Rep0Certificate.lean`.

## Structural changes (summary)

- §4.2 "H3 and H5" split into two paragraphs (cells and whole-cell formulas; the cube route and
  how H5 was closed) and "H7" split into two (cells and certificates; the t = 0 cell), per the
  reviewer's D7 note on two twenty-line paragraphs and to carry the C1/C2/M1 corrections.
- §3.2 consumer paragraph rewritten as a two-item list (LRAT consumer, five whole-cell inputs;
  cube consumer, seven base formulas).
- Table 4 rows "H3, H5" and "H7" replaced by four rows: H3; H5; H7, cells t ≥ 1; H7, cell t = 0.
- New `\leantab` macro (url-style breaking at underscores and dots only) used for every
  identifier in Tables 1, 2 and 4, so names never break inside a camel-case word.
- §7 receipts list set ragged-right and the `manuscript/anvil/erdos85-drop/refs/` prefix
  abbreviated to `refs/` (stated once in the lead sentence); four receipts added.
- §5.2 Lean names moved out of the running sentences into a ragged-right list keyed (i)–(iv).
- Appendix B "Methods" reduced to pointers for the cold-audit and certificate-factory rules.

## Critic notes → changes

| Source | Note | Resolution |
|---|---|---|
| erdos85-drop.3.audit (critical-flag C1, claim_support_failure) | H7 cells t = 1,…,7: §4.2, Table 2 row h=7 and Table 4 attribute the whole stratum to the 2026-09-15 closure ledger and its premises; the receipt and the Lean source show the t ≥ 1 cells are closed by thirteen LRAT certificates checked in Lean by `native_decide`, and the ledger covers only t = 0; trust profile undisclosed | Addressed at every location. §4.2 "H7: cells and certificates" now states the fourteen canonical representatives (1,1,2,3,3,2,1,1 by t = 0..7; kernel-checked census; graph cover `sevenHighCanonicalGraphCover_all`), the thirteen t ≥ 1 certificate modules (`include_str` of packed LRAT files on absolute Stripe paths; LRAT check of `orderFortyNineGeneratedH7SatCnf` at 1,329,041 clauses by `native_decide`; `sevenHighCanonicalRepresentativeExcluded_of_lrat`; aggregate `orderFortyNineStratumExcluded_seven_of_t0`), and their trust profile in three explicit sentences (`Lean.ofReduceBool`; compiled at the 2026-08-15 commits and not rebuilt in the 2026-09-27 cold audit, compile receipts = commit records + production manifests with drat-trim, lrat-check and Lean replay; certificates on absolute local paths). §4.2 "H7: the t = 0 cell" scopes the 7/14/21 split, the 43 classes, the 28 roots and the ledger to t = 0 with `…_seven_of_emptyCubeEvidenceVectors` (19/15/7/2) as its uninstantiated interface, names the premise reviews 1573/1574 (also Lean theorems) and 2091, and keeps both caveats (enumerator audit; uninstantiated capstone). Table 2 row h=7 evidence rewritten per the auditor's wording. Table 4: distinct "H7, cells t ≥ 1" row (evidence and limit: `native_decide`/`Lean.ofReduceBool`, not covered by the Table 1 rebuild, local paths) and the old row relabelled "H7, cell t = 0". §4.4 trust paragraph lists the thirteen modules first among the post-solver trust items. §6 re-weighed ("H3 and the thirteen positive-triple H7 representatives carry checked LRAT proofs …" and "the thirteen H7 certificate checks add `Lean.ofReduceBool` outside that audit"). Also §1 Result A, §2 trust root, Table 1 caption ("were not part of this rebuild and are not listed"), §3.2 tail, §7 availability ("also need the packed LRAT files"), and the 2026-09-28 receipt named in §7. The certificates are never described as part of the cold audit. |
| erdos85-drop.3.audit (critical-flag C2, numerical_inconsistency) | "the seven whole-cell H3/H5 formulas" (§4.2 L162, App. B L332) vs five whole-cell formulas (§3.2); "a 7×8 grid per cell" gives 280/10, not 392/14 | Addressed. §3.2 now states the two consumers as a list: the LRAT consumer takes five whole-cell inputs (two H3 representative masks, three H5), the cube consumer seven base formulas (four H3 scouts B1, C1, C2, dist-2 and three H5 cell formulas), "and their input counts must not be mixed or added". §4.2 "the cube route" names the seven base formulas, states "a 7×8 grid of 56 positive cubes per base formula", derives 4×56 + 3×56 = 392 and 8 + 6 = 14, 406 jobs, and adds "The five whole-cell formulas and the seven base formulas are alternative inputs to the same conclusion and are never added together." App. B exchange-rate paragraph: "replaces the five whole-cell H3/H5 formulas of the LRAT interface by seven base formulas (four H3 scouts and three H5 cells), each with two checked cover formulas and a 7×8 grid of positive cubes". The phrase "seven whole-cell" no longer occurs. |
| erdos85-drop.3.audit (major M1) + erdos85-drop.3.review (generic, major) | H5 closure outcome never stated; the implied cube-grid/129-root mechanism contradicts the receipt; Table 4 lumps H3 with H5; §7 names no H5 receipt | Addressed. §4.2 states the outcome: closed 2026-09-10 by reviewed reductions of the three cells (T0 review 2037, T1 review 2032, T2 reviews 2062 and 2063), outer ledger review 2065 PASS with an independent checker and pinned result hashes; paper-and-computation level; the three Boolean-exclusion premises of `orderFortyNineStratumExcluded_five_of_booleanExclusions` undischarged in Lean; no SAT run or certificate replay; the 129 root cubes not consumed; "The H5 rows of the census index are therefore the SAT-side inventory of the same three cells, not the evidence for their exclusion." Table 2 row h=5 and a separate Table 4 "H5" row carry the same statement; Table 4 "H3" row now says "checked LRAT proofs of both whole-cell formulas". §7 names `H5_CLOSURE_LEDGER_README_20260910.md`, `H5_CLOSURE_REVIEWED_RESULT_20260910.md`, `h5-closure-review2065.json`, `h5-closure-reviewer-REVIEW2065.json` and the 2026-09-28 receipt. The v3 sentence "closed by reviewed paper-and-computation covers with archived local proof receipts" is removed. |
| erdos85-drop.3.review (generic, major) | §4.2 H7: cells t ≥ 1 disposed of by an unnamed premise | Same change as audit C1 (the receipt the reviewer asked the authors to bank is `H7_POSITIVE_TRIPLE_CELLS_H5_CLOSURE_FORMULA_COUNTS_20260928.md` §1). |
| erdos85-drop.3.review (generic, major) | Seven vs five H3/H5 formulas never reconciled | Same change as audit C2. |
| erdos85-drop.3.review (generic, minor) + audit m3 | "the C4-free edge bound gives h ≤ 9" — the textbook bound gives only h ≤ 21; the inequality is a Lean counting bound | §3.2: "and a counting bound proved in Lean gives h ≤ 9". |
| erdos85-drop.3.review (generic, minor) | Abstract "it selects r(42) = 49" | Abstract: "it corresponds to selecting r(42) = 49"; §1 already had "the nonexistence hypothesis selects". |
| erdos85-drop.3.review (generic, minor) + audit m2 | "about 1,400 solver inputs (1,412 preparation receipts …)" reads as distinct instances | §1: "The census recorded 1,412 input preparations for the 1,161 residual rows over four cloud passes (a row that reached its cap was prepared again for the next pass)"; §7 CENSUS_TIMING item: "the 1,412 preparation receipts for the 1,161 rows". The "about 1,400" gloss is dropped. |
| erdos85-drop.3.review (generic, minor, related-work) | §2 process note "left to a literature pass with search enabled" | §2: "We do not compare the methods behind the decided entries of the r table with the method used here." |
| erdos85-drop.3.review (generic, minor) | H7 route list omits the C7 chain that closes `cube_F7_t14` | §4.2: "source enumeration with complement completion for eleven of the twelve a = 7 roots and a cycle-exclusion chain for the twelfth" (`H7_CLOSURE_20260915.md` rows `cube_F7_*`; C7 → 2117). §7 inventory item: "root closures including the cycle-exclusion chain". |
| erdos85-drop.3.review (generic, minor) + audit m4 | Traceability sentence: the `v2cnf` hash and the §5.3 census orders trace to files not named in §7 | §7 names `refs/PAUSE_HANDOFF_20260927.md` for the `v2cnf` hash and trust-boundary summary; the §1 and §7 traceability sentences now except "the plane-order census figures quoted in Section 5.3", which "trace to the ledger files named beside them in Appendix A" (`Q9_EXISTENCE_DECISION_20260911.md`, `CAYLEY_CENSUS_Q11_Q13_20260913.md`). The numbers are kept (both options were offered; naming is preferred to dropping). |
| erdos85-drop.3.review (generic, minor) | "cells" vs the receipt's "incidence profiles" for H3 | §4.2: "For h = 3 there are two incidence profiles … one for each of the cells t = 0, 1 of Table 2 (the canonical cells of the Lean statement refine the profiles by fixing a representative mask)"; for H5 "the three cells T0, T1 and T2 have support profiles …" (the H5 ledger's own term). §7 inventory item: "the H3 and H5 profiles, formulas and root counts". |
| erdos85-drop.3.review (generic, minor) | Three-residual-roots mechanism is the dispatcher's reading | §4.2: "the inventory's three ``historical object conflicts'', which we read as follows: …". |
| erdos85-drop.3.review (generic, minor, D6) | Table 2 identifiers broken mid-name by the camel-case penalty | LaTeX structure fix, not prose: new `\leantab` url command (no camel-case specials) used in Tables 1, 2 and 4; h column .04, reduction column .47. `pdftotext -layout` shows every Table 2 name breaking only after an underscore (`orderFortyNineStratumExcluded_` / `tripleCells`, `orderFortyNine_` / `highIncidence_profile_of_seven_high`, `orderFortyNineStratumExcluded_seven_of_` / `t0`). Running text keeps `\lean` with the camel-case breaks. |
| erdos85-drop.3.review (generic, minor) | 23 underfull lines, six at badness 10000 (§3.2 L146, §4.1 L158, §5.2 L254–256) | §3.2 consumer paragraph is now a two-item list; §4.1 no longer repeats the two witness names (given in §3.1); §5.2 Lean names moved to a ragged-right list keyed (i)–(iv); §7 receipts list ragged-right. Result: 0 overfull, 7 underfull, 0 at badness 10000. |
| erdos85-drop.3.review (generic, nit) + scoring D9 | §6 opening sentence restates the architecture in 60 words | Halved and re-weighed for C1: "The upper side at order 49 is a Lean-proved case split: H3 and the thirteen positive-triple H7 representatives carry checked LRAT proofs, H5 and the last H7 cell are closed by reviewed arguments with independently checked computation, and H1 was settled by a verdict-only two-solver census with no open row." |
| erdos85-drop.3.review (generic, nit) + scoring D9 | Appendix B "Methods" duplicates §4.4 and §3.1 | Cold-audit rule → "as in Section 3.1 …"; certificate factory → "the rules of Section 4.4 (…)"; room protocol and census tooling kept. |
| erdos85-drop.3.review (generic, nit) | §7 names `h1-census-table.json`; `refs/` holds the `.tsv` twin | §7 names both `h1-census-table.json` and `h1-census-table.tsv` (`CENSUS.md` names both). |
| erdos85-drop.3.review (generic, nit) | Table 4 witness cell "and the edge count (168) the order-48 graph" is elliptical | "and the edge count (168) corroborates the order-48 graph". |
| erdos85-drop.3.review (generic, scoring D7) | Two twenty-line paragraphs (§4.2 H3/H5 and H7) would read better split | Each split into two paragraphs (see structural changes). |
| erdos85-drop.3.review (generic, scoring D6) | No figure where one would carry the argument (cube tree, solve-time tail) | Declined — `figures/` is empty and no figure source script exists; adding a figure is the `paper-figures` phase's work and would need a new receipt-backed data extraction; this is the last iteration under the cap and the critical flags took priority. |
| erdos85-drop.3.review (generic, scoring D4, related-work) | Method-lineage gap (how the decided r(s) entries were obtained; prior SAT-with-certificate results) | Declined again, as in v3 — web search is off, no `paper-litsearch` sibling exists, and nothing may be invented; the process note that pointed at it is removed from the body (minor above). A litsearch run before publication remains the fix. |
| erdos85-drop.3.review (generic, procedural) | Numeric detector clean; pending gate clean; render gate passed; evidence drift CLEAN at review time | No change required. The reviewer's manual sums were preserved; the new sums (4×56 + 3×56 = 392, 8 + 6 = 14, 3×43 = 129) are written out in the text. |
| erdos85-drop.3.audit (m1, evidence drift advisory) | `refs/**` changed after the v3 snapshot (the three new receipts) | Expected; those receipts are the inputs of this revision. The baseline is re-recorded for v4 by `anvil.lib.evidence_drift record` (see `_progress.json`). |
| erdos85-drop.3.audit (m5, bibliography) | `bloom-erdos85` and `afzaly-mckay-extremal` carry `year = {2026}` for undated web pages; the year is an access year | `refs.bib`: `year = {n.d.}` on both entries; the "undated web page, accessed …" notes are kept. Renders as "(Bloom, n.d.)" and "Afzaly and McKay (n.d.)" (BibTeX 0 warnings; 0 `??`). This consciously reverses the v2→v3 change that introduced the access year as a publication year; the v2 reviewer's "n.d." objection is outweighed by not misdating an undated source. Field change only. |
| erdos85-drop.3.audit (build note) | Clean build; 23 underfull; 10 cosmetic Menlo font-shape warnings | Rebuilt with the same four-pass sequence; the Menlo small-caps warnings are unchanged and cosmetic (class requests a small-caps monospace shape Menlo lacks). |
| erdos85-drop.3.audit (citation-audit: 9 unverified, 3 partial) | No PDF of any cited work on disk; author-side verification of `zhang2017polarity` values and the App. A Boza bounds r(109), r(155) still owed | Declined / out of scope for the reviser — no sources may be fetched (web search off) and no citation is added or removed. Carried forward as an author obligation before submission. |
| erdos85-drop.3.audit (corpus tier, venue overlay, artifact_verify) | Inactive | Nothing to do. |
| erdos85-drop.3.numeric (tool evidence) | 0 findings | Nothing to do; no arithmetic claim was changed except the C2 correction above. |
| erdos85-drop.3.pending (tool evidence) | 0 findings, no markers | Nothing to do; no `[PENDING …]` marker was introduced. |
| scope_lint (helper, not a critic) | v3 reported as untraced: tabularx column widths (0.04 … 0.85), outline labels 2.66/2.69 and bare room-message numbers (31664 … 32032) | Source made lint-clean without changing any claim: widths written `.34\textwidth` etc. and float parameters `.9`/`.05`/`.85`; "outline versions v2.66--v2.69.3" (matching the `v2.62`/`v2.64` usage elsewhere); every bare transcript pointer in Appendix B now carries the explicit prefix "message"/"messages" that the linter and a cold reader both expect. Result: PASS. |

## Scope self-check (BRIEF hard rules)

Result A is still "computational evidence", "a computational result, not an unconditional Lean
theorem", "evidence, not a theorem"; the words theorem/proof/decided are not applied to it. The
new certificate sentences describe LRAT checks "inside Lean by `native_decide`" with their
`Lean.ofReduceBool` dependency, local paths and missing cold rebuild stated in the same
paragraph, Table 4 and §4.4 — no verdict or certificate is promoted to a kernel-checked
statement, and the H5 closure is "paper-and-computation evidence". Nothing is claimed about
Erdős Problem 85 itself (abstract, §1 and §6 sentences unchanged). A-REG remains "an unproved
hypothesis with a stated rival, not a conjecture we endorse". Every new number is listed above
with its receipt; no existing disclosure was weakened (the v3 caveats on the enumerator audit,
the uninstantiated capstone, the open H1 assembly, the missing aggregate and the verdict-only
census are all retained). Authorship and the Contributions paragraph are unchanged.
