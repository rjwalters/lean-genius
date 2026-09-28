# Changelog — erdos85-drop.2 → erdos85-drop.3

Revised against every critic sibling at version 2: `erdos85-drop.2.review/` (generic rubric
`anvil-pub-v2`, 32/44, no critical flags, `advance: false`), `erdos85-drop.2.numeric/` (tool
evidence, 0 findings) and `erdos85-drop.2.pending/` (tool evidence, 0 findings, no `[PENDING]`
markers). No venue overlay, audit, litsearch, vision or corpus-audit sibling exists at version 2.
The corpus tier is inactive (no `corpus:` key in `BRIEF.md`), so no `provenance.md` is carried.

Build: `xelatex` + `bibtex` + `xelatex` ×2 in `erdos85-drop.3/` (log in `compile-log.txt`,
class file copied from `erdos85-drop.2/`): 0 LaTeX errors, 0 undefined citations or references,
0 overfull boxes, 0 BibTeX warnings, 18 pages (v2: 16; the two added pages are the strata
definition with the new Table 2, the H3/H5 and H7 closure sketches, the H1 instance paragraph
and the receipts list). `pdftotext main.pdf` contains no `\_`, `\=` or `??` artefacts and no
`n.d.`. Underfull lines: 23 (v2: 32), six at badness 10000 (v2: six), all on lines carrying long
Lean identifiers; see the "Underfull lines" row below.

New receipts in `erdos85-drop/refs/` since v2 (all used): `STRATA_AND_SMALL_ORDERS_20260928.md`,
`CENSUS_TIMING_20260928.md`, `CERT_BANK_STATS_20260926.md`,
`BOZA48_NONISOMORPHISM_RECEIPT_20260928.txt`, `PHASE_B_H1_H3_INVENTORY_20260910.md`,
`PHASE_B_H5_H7_INVENTORY_20260910.md`, `Q7_H1_H3_SQUEEZE_20260910.md`,
`Q7_H5_H7_SQUEEZE_20260910.md`, `H7_CLOSURE_20260915.md`, and the dated correction appended to
`FIRST_DROP_LITERATURE_CHECK.md`. Every Lean name newly cited from `STRATA_AND_SMALL_ORDERS` was
re-verified by grep against `proofs/Proofs/` in the `erdos85/integration` worktree on 2026-09-28
(all 19 resolve to a `theorem`/`def`; `c4FreeMinDegreeWitness_even_delete_absolute_nucleus` lives
in `namespace Erdos85.Polarity`).

## Structural changes (summary)

- Abstract trimmed to the two results, the evidence-level sentence, the qualifier and the Boza
  connection; the count-by-count description now lives only in §1.
- §3.2 now defines the strata from the Lean source (what a high vertex is, why every degree is 7
  or 8, why $h$ is odd and $\le 9$, the Lean-proved exclusion of $h=9$, the combining theorem);
  Table 2 is rebuilt as "stratum → Lean reduction to cells → evidence".
- §4.2 gains one paragraph each sketching the H3/H5 cell-and-cover closure and the H7
  singleton-capacity closure, plus a short "H1: the instances" paragraph describing an H1 graph,
  the five family profiles and the emitter interface.
- §4.4 states the trust boundary once (encoding → solvers → H7 enumeration → H7 capstone →
  historical certificates) and reinstates the 1,322 / 1,412 input-identity counts.
- §4.5 reinstates the archived-bank statistics; §4.6 sources both projection rates in one
  sentence and aligns the two ranges with the receipts.
- §5.1 and §5.2 replace room vocabulary with plain terms; §5.3 names the Lean statements behind
  the orders-15/16 remark.
- §6 keeps the claim, the "either answer" sentence, the price-of-certainty paragraph and the
  Theorem B paragraph, and no longer re-narrates the census.
- §7 gains an "Artifacts and receipts" list naming every receipt file by repository path, and the
  repository URL; the old "Artifacts" paragraph of §6 is absorbed into it.
- Appendix B states that the room transcript is not published.
- `refs.bib`: the two undated web entries carry `year = {2026}` with an "undated web page,
  accessed …" note (field change only; no entry added or removed; all 11 entries still cited).
- `figures/` carried over (empty in v2, empty in v3; no `figures/src/`).
- BRIEF hard scope rules re-checked on v3: Result A is never a theorem/proof/decided value;
  nothing is claimed about Erdős 85 itself; A-REG is "an unproved hypothesis with a stated rival,
  not a conjecture we endorse"; no verdict or certificate is promoted; the evidence-level table,
  trust-boundary discussion, cost-to-verify section with the cube-partitioned projection, Theorem B
  with its residue, and the Interpretation section survive in substance; authorship and the
  Contributions paragraph are unchanged.

## Critical flags

None at version 2.

## Major

| Source | Note | Resolution |
|---|---|---|
| erdos85-drop.2.review (generic, major, D2) | §1 "Every number in the paper traces to a banked receipt named in Section 6" is false on its face: the §4.5–4.6 cost/projection figures and the Appendix A figures trace to receipts not named anywhere | §7 "Artifacts and receipts" now lists every receipt file by path under `research/problems/erdos-85-wip-01/`: `phase_b_h1_census_20260927/` (CENSUS.md, census table, gap audit, cube tree check), `manuscript/anvil/erdos85-drop/refs/CENSUS_TIMING_20260928.md`, `…/CERT_BANK_STATS_20260926.md`, `sat49/H1_REPLAY_SPOT_16_BUDGET_PLAN_20260916.md`, `sat49/h1_replay_fleet_costs_20260910.json`, `sat49/H1_V3_SOLVER_TIMING_20260916.md`, `AXIOM_AUDIT_COLD_20260927/`, `…/STRATA_AND_SMALL_ORDERS_20260928.md`, the two Phase B inventories, the two Q7 squeezes, `H7_CLOSURE_20260915.md`, `sat49/verify_boza48_nonisomorphism.py` with `…/BOZA48_NONISOMORPHISM_RECEIPT_20260928.txt`, and `manuscript/FIRST_DROP_LITERATURE_CHECK.md`, each with the figures it carries. The §1 sentence is narrowed to "Every number in Sections 1 to 7 traces to a receipt file named in Section 7; the appendices carry transcript pointers into the campaign record" (the Appendix A ledger rows and commit hashes are pointers, not receipt files in `refs/`). |
| erdos85-drop.2.review (generic, major, D2) | §4.6 projection rests on 5.5 GB per Kissat-hour and 0.5 MB/s whose measurement is not pointed to | §4.6 opens with the two rates and their sources in one sentence each: the LRAT growth rate is the median compact-LRAT size per Kissat solve-hour over the bank's 12,102 UNSAT rows binned by solve time (roughly 5 to 6 GB per hour in each of four bins from under 15 minutes to 4 hours; the projection uses 5.5), and the kernel-check rate is the replay budget model's 984 s per certificate at a 509 MB mean gzipped object (346 MB in the pilot). Both figures are in `CERT_BANK_STATS_20260926.md` and `CENSUS_TIMING_20260928.md`, now named in §7. |
| erdos85-drop.2.review (generic, major, D2) | 1,161 residual roots vs 1,158 gap slots unexplained | §4.2 adds: "The three residual roots that are not gap slots are the inventory's three historical object conflicts: the capacity snapshot already lists a certificate object for each, so the gap auditor does not count them as gaps, but the frozen candidate set retained them and the census re-solved them." Taken from `PHASE_B_H1_H3_INVENTORY_20260910.md` ("The three historical object conflicts remain in the candidate set") with the dispatcher's reading of `CENSUS.md`; not guessed. The residual-root class in §4.2 and Table 4 is now described as "with no accepted certificate object" rather than "without a listed certificate object", so the sentence and the count agree. |
| erdos85-drop.2.review (generic, major, D1) | §3.2 does not define the strata; a reader cannot see that $h\in\{1,3,5,7\}$ exhausts the candidates | §3.2 now states, from `STRATA_AND_SMALL_ORDERS_20260928.md` and the Q7 squeeze: in a $C_4$-free graph on 49 vertices with minimum degree 7 the non-returning length-two walks from a vertex have distinct endpoints, so $\sum_{u\sim v}(\deg u-1)\le 48$ and every degree is 7 or 8; a high vertex has degree exactly 8 (`orderFortyNineHighVertices`); the degree sum $7\cdot 49+h$ is even so $h$ is odd, the $C_4$-free edge bound gives $h\le 9$, and Lean proves $h\in\{1,3,5,7,9\}$ (`orderFortyNine_card_high_eq_one_or_three_or_five_or_seven_or_nine`); `OrderFortyNineStratumExcluded h` is defined; $h=9$ is refuted in Lean with no external input (`orderFortyNineStratumExcluded_nine` via `false_of_orderFortyNine_nine_high`); and `not_c4FreeMinDegreeWitness_fortyNine_seven_of_strata (h1)(h3)(h5)(h7)` composes the four remaining exclusions (displayed). Table 2 is rebuilt to list all five strata with the Lean statement that reduces each to its cells (`…_one_of_pureFamilies`, `…_three_of_tripleCells` ($t=0,1$), `…_five_of_tripleCells` ($t=0,1,2$), `…_seven_of_tripleCells` ($t=0,\dots,7$, bounded by `orderFortyNine_highIncidence_profile_of_seven_high`), `…_nine`) and the evidence supplied. The abstract and §1 now say the case split is proved exhaustive in Lean. |
| erdos85-drop.2.review (generic, major, D4) | Related work never says how the decided entries of Boza's table were obtained nor where a two-solver SAT census sits among prior SAT-based extremal computations; run `paper-litsearch` | **Declined for this revision** — web search is off, no litsearch sibling exists, and no file in `refs/` describes Boza's or Zhang–Chen–Cheng's methods, so any sentence on them would be an invented claim (BRIEF: cite only `refs.bib`, no new factual claims). §2 now says explicitly that the paper does not describe how the decided $r$ entries were obtained and leaves that comparison to a literature pass with search enabled. Recommend the orchestrator run `paper-litsearch` before the next revision. |
| erdos85-drop.2.review (generic, major, D2) | H3/H5 and H7 closures are named but not sketched | §4.2 "H3 and H5": block form $A=[0,B;B^T,C]$, independence of high vertices, one common neighbour per pair, support $t_v\le 3$ from the matching structure of a neighbourhood, the cells indexed by the number $t$ of support-3 low vertices with the support-size counts of each cell ((25,18,3,0), (24,21,0,1) for H3; (14,20,10,0), (13,23,7,1), (12,26,4,2) for H5), what the checked formula of a cell is and why its UNSAT proof excludes the cell, the two H3 base CNFs (29,500 variables, 1,328,183 clauses) with checked LRAT proofs and the independent paper/Python exclusion of H3, the 7×8-grid cover with the Lean accounting and composition (392 + 14 = 406), and the H5 root count (43 per cell = 58 − 15 direct certificates; 129 rows). §4.2 "H7": the rigid incidence profile (cells $t=0,\dots,7$), the empty/singleton/pair split (7/14/21) under the ledger's premises, the empty-block classification (43 $C_4$-free subcubic classes at $a=6..9$ edges), the singleton-capacity argument (14 singletons force $\ge\max(0,35-4a)$ outside common-neighbour pairs; capacity $7-2d_E$ per vertex; contradiction in 12 classes at $a=6$ and 3 at $a=7$; 7/12/7/2 = 28 roots), which pieces are Lean theorems (`Erdos85VertexSubsetEdgeCapacity.lean`, the exterior-pair capacity $\deg_X v+2n_E(v)\le 7$, $35\le 4a+\lvert X\rvert$) and which are not (the enumeration, the representative certificates, the isomorphism transfer), the per-family closure routes of the 2026-09-15 ledger, the F14 host-leaf partition (2,278,608 = 1,757,882 + 75,027 + 445,699) with the third-seat reproduction at zero mismatches, and the two caveats (enumerator-code audit; uninstantiated capstone). All figures from `Q7_H1_H3_SQUEEZE`, `Q7_H5_H7_SQUEEZE`, the two Phase B inventories and `H7_CLOSURE_20260915.md`. The 28-root table itself was not moved into an appendix (the ledger's review-chain columns are transcript pointers and would add a page of numbers without a receipt in `refs/` beyond the ledger). |

## Minor

| Source | Note | Resolution |
|---|---|---|
| erdos85-drop.2.review (generic, minor, D3) | "the first strict drop of $f$ decided" uses the reserved verb | Abstract and §1 Significance now read "To our knowledge, this is the first strict drop of $f$ settled, at the level of computational evidence, on the problem's stated domain"; "to our knowledge" kept; "decided" no longer applied to Result A anywhere. |
| erdos85-drop.2.review (generic, minor, D2) | "two to four weeks of fleet time" glosses the JSON's 7.9–31.5 planned days | §4.6: "one to four and a half weeks of fleet time (8 to 32 planned days at 32 to 8 shards)", the reviewer's suggested wording, matching `h1_replay_fleet_costs_20260910.json` byte-weighted planned wall days 7.88 / 15.75 / 31.48 at 32 / 16 / 8 shards. |
| erdos85-drop.2.review (generic, minor, D2) | "roughly 65 to 130 GB" vs the worksheet's 60–130 GB | §4.6 now reads "roughly 60 to 130 GB", the printed range of the `CENSUS_TIMING_20260928.md` worksheet (12–24 h × 5.5 GB/h). |
| erdos85-drop.2.review (generic, minor, D8) | "the exact Lean results at orders 15 and 16" names no Lean statement | §5.3 now names `minDegreeForC4_fifteen : minDegreeForC4 15 = 5` and `minDegreeForC4_sixteen : minDegreeForC4 16 = 5` with the 4-regular $C_4$-free witnesses `fifteenRegular` and `sixteenRegular`, and states why the $q=4$ analogue fails (`sixteenRegular` is a $C_4$-free 4-regular graph on 16 vertices). The abstract keeps "Lean-checked exact values at orders 15 and 16" now that the statements are named in the body. Source: `STRATA_AND_SMALL_ORDERS_20260928.md` (`Erdos85Problem.lean`). |
| erdos85-drop.2.review (generic, minor, D8) | Non-isomorphism claim names a script but no receipt | §4.1 now cites the 2026-09-28 rerun of `sat49/verify_boza48_nonisomorphism.py` (NetworkX 3.6.1) with its receipt in the release material (`BOZA48_NONISOMORPHISM_RECEIPT_20260928.txt`, named in §7): PASS, non-isomorphic to all ten graphs of the Afzaly–McKay archive at order 48 with 168 edges, only one of which is 7-regular. §2 updated to match ("not isomorphic to any graph of the same archive at order 48"). |
| erdos85-drop.2.review (generic, minor, D6) | Table 3 Cap cell "probe 1 h, leaves 24 h" wraps to a lone "h" | Cap column widened 0.17 → 0.21, Hosts 0.22 → 0.20, Pass 0.15 → 0.14; cell reworded "1 h probe, 24 h leaves". Rendered check on page 7: no dangling unit. |
| erdos85-drop.2.review (generic, minor, D7) | Room vocabulary undefined: "cold-green", "jaw", "socket", "monoliths", "pincers" | "cold-green" → "is a dependency of Theorem B and so compiled in the cold rebuild of Table 1"; "jaw"/"pincers" → "a pair of adjacent orders with an existence half and a nonexistence half" (defined at first use in §5.1; "half" thereafter, including §5.3 and Appendix A); "socket" → "the Lean statement that a proof of this case would discharge" / "that statement" (§5.2) and "the older interface that expected five whole-cell LRAT proofs" (Appendix B); "monoliths" → "whole-cell formulas" (§3.2, §4.2, Appendix B). Grep for `cold-green|jaw|socket|monolith|pincer`: 0 hits. |
| erdos85-drop.2.review (generic, minor, D9) | §6 restates §4.2 almost in full; abstract and §1 Result A paragraph are near-duplicates; trust-boundary sentence appears four times | Abstract trimmed to results + qualifier (no per-class counts). §6 rewritten to the claim, the "either answer" sentence, the price-of-certainty paragraph (pointing to §4.5 and §4.6 instead of repeating their figures) and the Theorem B paragraph; the opening "this section is written so that it can be read standing alone" and the re-narration of passes, caps and the cube split are cut. The sentence "two solvers agreeing under a cap is evidence about solver behaviour, not a proof" now appears once, in §4.4; §1 says "Result A is evidence, not a theorem: Section 4.4 states where the residual trust sits", Table 4 points to §4.4, and §6 says "The trust boundary is stated in Section 4.4 rather than hidden". The counts 1,161 / 1,160 / 96 / 36 now appear in §1 (once, as the statement of Result A), §4.2 (the census), Table 4 (the evidence map), §4.6 (where the 1,160-row timing is used) and the §7 receipts list (where each receipt's figures are named); they are removed from the abstract, §2 and §6. |
| erdos85-drop.2.review (generic, minor, D8) | "(Bloom, n.d.)" and "(Afzaly and McKay, n.d.)" in running text | `refs.bib`: both web entries now `year = {2026}` with the note "undated web page, accessed 2026-09-28" / "accessed 2026-08-25". Renders as "Bloom (2026)" and "Afzaly and McKay (2026)"; `pdftotext` grep for `n.d.`: 0 hits. Field change only; no entry added or removed. |
| erdos85-drop.2.review (generic, minor, D7) | 32 underfull lines (6 at badness 10000) on long Lean identifiers | The `\lean` url command now also permits a discouraged break (penalty 500) before each capital letter, so camel-case identifiers can break at a word boundary when the only alternative is a badness-10000 line (implemented through url's `\UrlSpecials` with `\mathchar`, since `\char` in url's math mode re-reads the active mathcode and loops). Underfull lines fall from 32 to 23; six remain at badness 10000 (the "second consumer" paragraph of §3.2, the witness sentence of §4.1 and the residue paragraph of §5.2, each carrying three or more 40-character identifiers in one sentence). Visually checked on the rendered pages: breaks fall at `…smallHighLrat|Checks`, `…of_small|HighCubeBaseUnsat`, `adj|Matrix_comm_…`. Not silenced with `\hbadness`; not moved to footnotes (the identifiers are the paper's audit trail and belong in the sentence that cites them). |

## Nit

| Source | Note | Resolution |
|---|---|---|
| erdos85-drop.2.review (generic, nit, D7) | `hno49` typeset as `\text{\texttt{hno49}}` in one display and `\hnoFortyNine` elsewhere | The §1 display now uses `\text{\hnoFortyNine}`; one form throughout. |
| erdos85-drop.2.review (generic, nit, D6) | Table 4 cell "independent edge-list audits corroborate both graphs" reads as if both had an edge-count audit | Cell now reads "codegree checks corroborate both graphs, and the edge count (168) the order-48 graph". |
| erdos85-drop.2.review (generic, nit, D5) | Repository-relative paths without a repository URL | §7 Data and code availability: "the Lean Genius repository (https://github.com/rjwalters/lean-genius)" (from `git remote get-url origin` of the branch-of-record worktree); the receipts list states once that all its paths are under `research/problems/erdos-85-wip-01/` on that branch; Lean sources under `proofs/Proofs/`. |
| erdos85-drop.2.review (generic, nit, D7) | Appendix B's room-message numbers point to a transcript whose availability is not stated | Appendix B opening now says the room transcript is a database in the project's private workspace, is not published with the paper, and the pointers are kept so the record can be audited by whoever holds it. |
| erdos85-drop.2.review (generic, nit, procedural) | Numeric detector, pending gate, render gate, evidence drift | Noted. Evidence-drift baseline re-recorded for `erdos85-drop.3/` by `anvil.lib.evidence_drift record` (see `_progress.json`). The drift the v2 review reported (`CENSUS_TIMING_20260928.md`, the literature-check correction) is consumed by this revision: every §4.6 figure now has a named receipt, and §1's conversion matches the correction. |

## Other siblings and dispatcher instructions

| Source | Note | Resolution |
|---|---|---|
| erdos85-drop.2.numeric (tool evidence) | 604 numbers, 0 arithmetic claims, 0 findings | Nothing to apply. New checkable arithmetic added: $7\cdot 49+h$ even; 12 + 3 = 15 excluded classes and 7 + 12 + 7 + 2 = 28 roots; 283 + 346 + 388 + 198 + 42 = 1,257; 58 − 15 = 43 per cell, 3 × 43 = 129; 1,757,882 + 75,027 + 445,699 = 2,278,608; 1,322 + 90 = 1,412; 392 + 14 = 406. |
| erdos85-drop.2.pending (tool evidence) | No `[PENDING]` markers | Nothing to carry forward; v3 contains no markers. |
| dispatcher (priority 4) | State the census scale once in §1 | §1 Result A paragraph: "The census prepared about 1,400 solver inputs (1,412 preparation receipts over four cloud passes) and spent about 5,700 core-hours of final-attempt solver time" (`CENSUS_TIMING_20260928.md`: 1,412 receipts; about 5,716 core-hours including the cube tree, capped attempts excluded). |
| dispatcher (priority 1) | Reinstate the bank statistics and the 1,322 / 1,412 counts now that they are receipted | §4.5: 12,102 UNSAT rows with sizes; compact LRAT median 1.2 GB, p90 4.0 GB, max 26.5 GB, 22.6 TB total, about 6 TB gzipped. §4.4: 1,322 historical / 90 new of 1,412 preparation receipts. |
| dispatcher | `FIRST_DROP_LITERATURE_CHECK.md` now ends with a dated correction; §1 must stay consistent | §1 conversion unchanged from v2 (it is the corrected rule); no 35/36 remark reinstated; the literature check is named in §7 "with its dated correction". |
| `scope_lint.py` (thread-local helper, not a critic) | Reports 30 "untraced" numbers | All are table column widths (`0.05`, `0.07`, `0.14`, `0.20`, `0.26`, `0.29`, `0.34`, `0.47`, `0.85`), outline version numbers (`2.66`, `2.69`) and Appendix B room-message numbers (`31664`–`32032`) that v2 carried unchanged; none is a factual figure. The helper checks `\texttt{}` names only, so the `\lean{}` names were verified separately (see the header note). No banned claim pattern and no AI-tell word reported. |

## Deliberately not applied

- Related-work method lineage (major, D4): declined as above — requires `paper-litsearch` with search enabled; nothing invented.
- An appendix table of the 28 H7 roots with review chains: not added (transcript pointers; the closure is now sketched in prose with the ledger named in §7).
- A figure of the cube tree or the per-row Kissat-time distribution (D6 suggestion): not added; the per-row timing join is summarized in `CENSUS_TIMING_20260928.md` by statistics only, and a figure would need the row-level data as a `figures/src/` input, which is not in `refs/`. Left for the figurer if the authors bank the row-level extract.
- Describing the H1 encoding "mathematically" in full (D5 suggestion): partially applied (the H1 graph structure, the five family profiles, the 24 table values and the `v2cnf emit`/`check` interface are stated); the clause-level encoding is the Lean program itself and is not restated.
